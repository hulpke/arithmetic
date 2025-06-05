LoadPackage("ModularGroup");
LoadPackage("kbmag");
Read("~/git/arithmetic/arithmetic.g");

MobiusTest:="2bdefined";

# this is the main function and shows how to use the code. It forms a
# homomorphism giving the presentation of SL2(\Z[1/p]),
# and then runs MobiusTest for this homomorphism and numbers a/p^e with
# a<=2*p^e.
# results are accumulated in the global variable `result`.
Handle:=function(p,exp)
local e,num,n,hom;
  hom:=AmalgamSL2k(p);
  PMAPS:=[];
  for e in exp do
    num:=Filtered([1..2*p^e],x->Gcd(x,p)=1);
    for n in num do
      Print("Doing: ",n/p^e,"\n");
      MobiusTest(hom,n/p^e);
    od;
  od;
end;

if not IsBound(result) then
  result:=[];
  infinite:=[];
fi;

matA:=[[1,0],[1,1]];matB:=[[0,1],[-1,0]];matU:=[[2,0],[0,1/2]];
f:=FreeGroup("A","B","U");
rels:=ParseRelators(f,"(AB)3=(UB)2=(UA2B)3=B2,B4,AU=UA4");
g:=f/rels;

if not IsBound(PMAPS) then
  map:=GroupHomomorphismByImages(g,Group(matA,matB,matU),
    GeneratorsOfGroup(g),[matA,matB,matU]);
  PMAPS:=[];
fi;


reducemod:=function(hom,p)
local one,gens,new;
  one:=One(Integers mod p);
  gens:=List(MappingGeneratorsImages(hom)[2],x->x*one);
  new:=Group(gens);
  NiceMonomorphism(new:cheap);
  new:=GroupHomomorphismByImagesNC(Source(hom),new,
    MappingGeneratorsImages(hom)[1], gens);
  return new;
end;

elementarygens:=function(a)
   return [[[1,a],[0,1]],[[1,0],[a,1]]];
end;

elementarygens2:=function(a)
   return [[[1,0],[1,1]],[[1,a],[0,1]]];
end;

TryWordEnum:=function(hom,mats)
local prdprime,prime,onp,op,gens,o,l,prd,start,ende,j,k,a,i,m,one,
      istransvec,dict,new,dups,ap,mgi,let,prw,mf,result,mi;

  result:=[];
  mgi:=MappingGeneratorsImages(hom);
  # find a boring prime
  let:=ShallowCopy(mgi[1]);
  gens:=ShallowCopy(mgi[2]);
  if Characteristic(mats)=0 then
    i:=Lcm(List(Flat(mats),DenominatorRat));
    prime:=23;
    while i mod prime=0 do prime:=NextPrimeInt(prime);od;
    op:=Z(prime)^0;
    #dict:=NewDictionary(One(mats[1]),GL(Length(mats[1]),prime),true);
    dict:=NewDictionary(One(mats[1]),true);
  else
    op:=One(mats[1][1]);
    prime:=DefaultRing(Flat(mats));
    dict:=NewDictionary(One(mats[1]),true);
  fi;

  # generators, inverse closed
  for i in [1..Length(gens)] do
    if not gens[i]^-1 in gens then
      Add(gens,gens[i]^-1);
      Add(let,let[i]^-1);
    fi;
  od;

  # first form all products of length up to l. There are technically |gens|^l
  # products, so 

  l:=LogInt(Int(2*10^10/Length(gens[1])^2),Length(gens));
  m:=ValueOption("extra");
  if IsInt(m) then l:=l+m;fi;

  one:=One(gens[1]);
  onp:=one*op;
  prd:=[one];
  prw:=[One(let[1])];
  prdprime:=[onp];
  dups:=[];

  start:=1;
  for m in [1..l] do
    Print(m,"\n");
    ende:=Length(prd);
    for j in [start..ende] do
      for k in [1..Length(gens)] do
        a:=prd[j]*gens[k];
	ap:=a*op;
	i:=LookupDictionary(dict,ap);
	if i<>fail then
	  if not IsBound(dups[i]) then
	    # first duplication
	    new:=a<>prd[i];
	    if new then dups[i]:=[i];fi;
	  else
	    new:=ForAll(dups[i],x->prd[x]<>a);
	  fi;
	  # will duplicate also new one
	  if new then Add(dups[i],Length(prd)+1);fi;
	else
	  new:=true;
	fi;
	
	if new then
	  Add(prd,a);
	  Add(prw,prw[j]*let[k]);
	  Add(prdprime,ap);
	  if i=fail then
	    AddDictionary(dict,ap,Length(prd));
	  fi;

          for mi in [1..Length(mats)] do
            if not IsBound(result[mi]) and a=mats[mi] then
              result[mi]:=prw[Length(prw)];
              if Number(result,x->IsBound(x))=Length(mats) then
                return result;
              fi;
            fi;
          od;
	fi;
      od;
    od;
    start:=ende+1;
  od;
  return result;
end;

WordsForMatsTry:=function(map,mats)
local q,hom,sub,cnt,w,wr,i,assg,hashard,lim,sel,tryassg,pow,j;

  assg:=function(pos,w)
    if not IsBound(wr[pos]) or Length(wr[pos])>Length(w) then
      wr[pos]:=w;
      RemoveSet(sel,pos);
    fi;
  end;
  tryassg:=function(w,m)
  local i;
    for i in [1..Length(mats)] do
      if mats[i]=m then assg(i,w);fi;
    od;
  end;
  wr:=[];
  hashard:=false;
  if ValueOption("short")=true then
    wr:=TryWordEnum(map,mats);
    hashard:=true;
  fi;

  sel:=Filtered([1..Length(mats)],x->not IsBound(wr[x]));
  if Length(sel)>0 then
    # try a few special cases that seem to come up often:
    # powers and conjugation by powers
    lim:=ValueOption("lim"); 
    if not IsInt(lim) then lim:=30;fi;
    hom:=MappingGeneratorsImages(map);
    for i in [1..Length(hom[1])] do
      for pow in [-2*lim..2*lim] do
        tryassg(hom[1][i]^pow,hom[2][i]^pow);
      od;
    od;
    q:=List(mats{sel},x->[
      [x[1,1],x[2,2]],[-x[1,1],-x[2,2]],
      [x[2,2],x[1,1]],[-x[2,2],-x[1,1]]
      ]);
    q:=Union(q);
    for pow in Filtered(q,x->ForAll(x,IsInt)) do
      tryassg(hom[1][2]^pow[1]*hom[1][1]*hom[1][2]^pow[2],
        hom[2][2]^pow[1]*hom[2][1]*hom[2][2]^pow[2]);
      tryassg(hom[1][2]^pow[1]/hom[1][1]*hom[1][i]^pow[2],
        hom[2][2]^pow[1]/hom[2][1]*hom[2][2]^pow[2]);
    od;

    if Length(sel)>0 and Length(hom[1])=2 and Length(mats[1])=2 
      and ForAll(Flat(mats),IsInt) then 
      #Print("biggie",sel,"\n");
      for i in ShallowCopy(sel) do
        #Print("i=",i,"\n");
        pow:=UnderlyingElement(STDecomposition(
          Reversed(List(mats[i],Reversed))));
        q:=GeneratorsOfGroup(FamilyObj(pow)!.freeGroup);
        tryassg(MappedWord(pow,q,hom[1]),MappedWord(pow,q,hom[2]));
      od;
      if Length(sel)>0 then Error();fi;
    fi;

  fi;

  cnt:=1;
  q:=ValueOption("start");
  if q=fail then
    q:=30;
  elif IsPrimeInt(q) then
    q:=q-1;
  fi;
  while Length(sel)>0 do
    q:=NextPrimeInt(q);
    Print("Try ",q,"\n");
    hom:=First(PMAPS,x->x[1]=q and
      MappingGeneratorsImages(x[2])[1]=MappingGeneratorsImages(map)[1]);
    if hom=fail then
      hom:=reducemod(map,q);
      if ValueOption("nocache")<>true then
        Add(PMAPS,[q,hom]);
      fi;
    else
      hom:=hom[2];
    fi;

    sub:=Group(mats*One(Integers mod q));
    w:=List(GeneratorsOfGroup(sub),x->PreImagesRepresentative(hom,x));
    for i in [1..Length(w)] do
      if Image(map,w[i])=mats[i] then assg(i,w[i]);fi;
    od;
    cnt:=Maximum(cnt+1,Int(cnt*105/100));
    if hashard=false and q+cnt>=400 and Number(wr,x->IsBound(x))<Length(mats) 
      and ForAll(PMAPS,x->x[1]<>NextPrimeInt(q+cnt)) then
      hom:=TryWordEnum(map,mats);
      hashard:=true;
      for i in [1..Length(mats)] do
        if IsBound(hom[i]) then
          assg(i,hom[i]);
        fi;
      od;
    fi;
    q:=q+cnt;
  od;
  return wr;
end;

MyTzKill:=function(T)
local tietze, store,f;

  tietze := T!.tietze;
  if tietze[TZ_TOTAL]>1000000 then
    # kill very long relators

    store:=TzOptions(T).protected;
    f:=FpGroupPresentation(T);
    f:=FreeGroupOfFpGroup(f)/Filtered(RelatorsOfFpGroup(f),
      x->Length(x)<10000 or NrSyllables(x)<=100);
    Print("Kill long \n");
    T:=PresentationFpGroup(f);
    TzOptions(T).printLevel:=2;
    TzOptions(T).protected:=store;
  fi;
  return T;
end;


MyGoElim:=function(T,downto)
local tietze,len,olen,store;
  TzTestInitialSetup(T); # run `1Or2Relators' if not yet done
  tietze := T!.tietze;

  len:=tietze[TZ_TOTAL];
  olen:=len+1;
  while tietze[TZ_NUMGENS]-tietze[TZ_NUMREDUNDS]>downto and olen<>len do

    T:=MyTzKill(T);
    tietze := T!.tietze;
    TzSearch(T);
    TzEliminateGens(T);
    if not tietze[TZ_MODIFIED] then TzSearchEqual(T);fi;
    olen:=len;
    len:=tietze[TZ_TOTAL];
    if TzOptions(T).printLevel>0 then  TzPrintStatus(T,true); fi;
  od;

  T:=MyTzKill(T);
  tietze := T!.tietze;

  olen:=TzOptions(T).loopLimit;
  TzOptions(T).loopLimit:=5;
  TzGo(T); # cleanup
  TzOptions(T).loopLimit:=olen;
  return T;
end;

# special relator rewriting
RewPresSome:=function(DATA)
local rels,i,j,w,f,r,s,fam,new,ri,a,offset,p,rset,re,start,stack,pres,
  subnum,bad,warn,str,rx;

  offset:=DATA.offset;
  subnum:=Length(DATA.subgens);
  rels:=[];

  for i in [1..subnum] do
    r:=WordProductLetterRep(NEWTC_Rewrite(DATA,1,DATA.subgword[i]),[-i]);
    if Length(r)>0 then
      Add(rels,r);
    fi;
  od;

  stack:=[];

  for i in [1..DATA.n] do
    CompletionBar(InfoFpGroup,2,"Coset Loop: ",i/DATA.n);
    for w in DATA.rels do
      r:=NEWTC_Rewrite(DATA,i,w);
      MakeCanonical(r);

      ri:=Length(r);
      if ri>10000 then r:=[];ri:=0;fi;
      # reduce with others
      for j in rels do
        r:=NEWTC_ReplacedStringCyclic(r,j);
        r:=NEWTC_ReplacedStringCyclic(r,-Reversed(j));
      od;
      Info(InfoFpGroup,3,"Relatorlen ",ri,"->",Length(r));

      if Length(r)>0 then
        Add(stack,r);
        while Length(stack)>0 do
          r:=stack[Length(stack)];
          Unbind(stack[Length(stack)]);
          ri:=-Reversed(r);
          rset:=Set([r,ri]);
          # reduce others
          j:=1;
          while j<=Length(rels) do
            s:=rels[j];
            for re in rset do;
              s:=NEWTC_ReplacedStringCyclic(s,re);
            od;
            if not IsIdenticalObj(s,rels[j]) then
              if Length(s)>0 then
                Add(stack,s);
              fi;
              rels:=WordProductLetterRep(rels{[1..j-1]},rels{[j+1..Length(rels)]});
            else
              j:=j+1;
            fi;
          od;

          Add(rels,r);
          SortBy(rels,Length);

            # does it occur in the augmented table?
            for a in DATA.A do
              for j in [1..DATA.n] do
                s:=DATA.aug[a+offset][j];
                if Length(s)>=Length(r) then
                  for re in rset do
                    s:=NEWTC_ReplacedStringCyclic(s,re);
                  od;
                  DATA.aug[a+offset][j]:=s;
                fi;
              od;
            od;
          od;
        fi;

    od;
  od;
  CompletionBar(InfoFpGroup,2,"Coset Loop: ",false);

  # add definitions of secondary generators
  rx:=Length(rels);
  for i in [subnum+1..DATA.secount] do
    r:=WordProductLetterRep(DATA.secondary[i],[-i]);
    Add(rels,r);
  od;

  str:=Concatenation(["a","b","p","q"],List([1..DATA.secount-subnum],
    x->Concatenation("x",String(x))));
  
  f:=FreeGroup(str); #DATA.secount,str);
  fam:=FamilyObj(One(f));

  rels:=List(rels,x->AssocWordByLetterRep(fam,x));
  rels:=Concatenation(Filtered(rels{[1..rx]},
    x->NrSyllables(x)<=Maximum(50,RootInt(DATA.index^3,2))),
    rels{[rx+1..Length(rels)]});
  pres:=PresentationFpGroup(f/rels);
  TzOptions(pres).protected:=subnum;
  TzOptions(pres).printLevel:=InfoLevel(InfoFpGroup);
  TzOptions(pres).eliminationsLimit:=4;
  pres:=MyGoElim(pres,subnum);
  if Length(GeneratorsOfPresentation(pres))>subnum then
    warn:=true;
    # Help Tietze with elimination
    bad:=Reversed(List(GeneratorsOfPresentation(pres)
          {[subnum+1..Length(GeneratorsOfPresentation(pres))]},
          x->LetterRepAssocWord(x)[1]));
    for i in bad do
      r:=DATA.secondary[i];
      re:=true;
      while re do
        s:=[];
        re:=false;
        for j in r do
          if AbsInt(j)>subnum then
            re:=true;
            if j>0 then
              Append(s,DATA.secondary[j]);
            else
              Append(s,-Reversed(DATA.secondary[-j]));
            fi;
          else
            Add(s,j);
          fi;
        od;
        Info(InfoFpGroup,2,"Length =",Length(s));
        r:=s;
        if warn and Length(s)>100*Sum(rels,Length) then
          warn:=false;
          Error(
            "Trying to eliminate all auxiliary generators might cause the\n",
            "size of the presentation to explode. Proceed at risk!");
        fi;
      od;
      r:=AssocWordByLetterRep(fam,Concatenation(r,[-i]));
      AddRelator(pres,r);
      #TzSearch(pres); Do *not* search, as this might kill the relator we
      #just added.
      r:=TzOptions(pres).printLevel;
      TzOptions(pres).printLevel:=0;
      TzEliminate(pres,i);
      TzOptions(pres).printLevel:=r;
      Print("Elimination ",i," from ",pres,"\n");
    od;
    Assert(1,Length(GeneratorsOfPresentation(pres))=subnum);
    
  fi;
  r:=List(GeneratorsOfPresentation(pres){[1..subnum]},
    x->LetterRepAssocWord(x)[1]);
  pres!.primarywords:=r;
  r:=List(GeneratorsOfPresentation(pres){
      [subnum+1..Length(GeneratorsOfPresentation(pres))]},
        x->LetterRepAssocWord(x)[1]);
  pres!.secondarywords:=r;
  return pres;
end;

SUBG:=fail;
MobiusTest:=function(arg)
local map,val,mfact,mats,gp,primes,m,r,w,t,den,p,e,num,mg,wmg,i,j,a,b,x,
  max,int,iso,red,ran,trace,nf,dopres,eval,dokerword,zwei,pstart;
  if arg[1]="Zwei" then
    zwei:=true;
    arg:=arg{[2..Length(arg)]};
  else
    zwei:=false;
  fi;
  if Length(arg)=1 then
    val:=arg[1];
    map:=AmalgamSL2k(DenominatorRat(val));
  else
    map:=arg[1];
    val:=arg[2];
  fi;
  mfact:=ValueOption("factor");
  if not IsInt(mfact) then mfact:=1;fi;
  if ForAny(result,x->x.val=val) then
    if ValueOption("factor")<>fail or ValueOption("redo")<>fail 
    or ValueOption("intermediate")=true then
      Print("removed old entry\n");
      RemoveElmList(result,PositionProperty(result,x->x.val=val));
    else
      return "done aleady";
    fi;
  fi;

  pstart:=Maximum(Concatenation([30],Factors(DenominatorRat(val))))+1;

  dopres:=ValueOption("dopres")=true;
  dokerword:=ValueOption("dokerword")=true;


  if zwei then
    mats:=elementarygens2(val);
  else
    mats:=elementarygens(val);
  fi;
  gp:=Group(mats);
  primes:=PrimesNonSurjective(gp);
  m:=MaxPCSPrimes(gp,primes);
  r:=rec(val:=val,primes:=primes,lev:=m[1],ind_calc:=m[2]);

  # create matrices that will combine to the elementary generators
  den:=DenominatorRat(val);
  #if den<>1 and not IsPrimePowerInt(den) then
  #  Error("currently only implemented for prime power denominator");
  #fi;
  p:=Factors(den)[1];
  if p=1 then
    e:=0;
    num:=[1];
    mg:=[];
  else
    e:=LogInt(den,p);
    num:=CoefficientsQadic(NumeratorRat(val),p);
    if zwei then
      mg:=List([0..e],x->elementarygens2(1/p^x));
    else
      mg:=List([0..e],x->elementarygens(1/p^x));
    fi;
    mg:=Concatenation(List(mg,x->x[1]),List(mg,x->x[2]));
  fi;

  wmg:=[];
  if IsBound(map!.specialpre) then
    # try special words for generators: b^((xa)^j) and p-th powers
    for i in [1..2] do
      a:=map!.specialpre[4*i-2];
      b:=map!.specialpre[4*i-1];
      x:=map!.specialpre[4*i];
      for j in [0..e] do
        w:=b^((x*a)^j);
        t:=ImagesRepresentative(map,w);
        t:=Position(mg,t);
        if t<>fail then wmg[t]:=w;fi;
        w:=(b^p)^((x*a)^j);
        t:=ImagesRepresentative(map,w);
        t:=Position(mg,t);
        if t<>fail then wmg[t]:=w;fi;
      od;
    od;
    #if ForAny([1..Length(mg)],x->not IsBound(wmg[x])) then Error("ugh!");fi;
  fi;

  w:=[];
  if ForAny([1..Length(mg)],x->not IsBound(wmg[x])) then
    wmg:=WordsForMatsTry(map,mg:start:=pstart);
  fi;
if false and p>1 then
    e:=e+1;
    for i in [1,2] do
      t:=One(Source(map));
      for j in [1..Length(num)] do
        t:=t*wmg[i*e-j+1]^num[j];
      od;
      w[i]:=t;
    od;
  fi;

  if List(w,x->ImagesRepresentative(map,x))=mats then
    Print("found words ",w," easily!\n");
  else
    Print("Hard factor!\n");
    w:=WordsForMatsTry(map,mats:start:=pstart);
  fi;
  SUBG:=SubgroupNC(Source(map),w);
  r.sub:=ShallowCopy(w);
  if ValueOption("tryinf")=true then
    t:=KBMAGRewritingSystem(Source(map));
    b:=SubgroupOfKBMAGRewritingSystem(t, w);
    Print("trying automatic structure\n");
    a:=AutomaticStructureOnCosetsWithSubgroupPresentation(t,b);
    Print("Result of KB: ",a,"\n");
    if a=true then
      r.index:=Index(t,b);
    else
      r.index:=fail;
    fi;
  elif ValueOption("intermediate")<>fail then
    red:=NumeratorRat(val);
    if not IsPrimeInt(red) then
      red:=List(Collected(Factors(red)),x->x[1]^x[2]);
      red:=Filtered(red,x->not ForAny(red,y->x^2<y));
      red:=Product(red);
    fi;

    m:=ValueOption("intermediate");
    if not IsInt(m) then m:=10000;fi;
    red:=reducemod(map,red);
    red:=red*IsomorphismPermGroup(Image(red));
    int:=List(w,x->Image(red,x));
    #max:=MaximalSubgroupClassReps(Image(red));
    max:=LowLayerSubgroups(Image(red),3);
    max:=Filtered(max,x->Size(x)^3<Size(Image(red))^2 
      and Index(Image(red),x)<=m);
    SortBy(max,x->-Size(x));
    max:=Filtered(max,x->ForAll(int,y->y in x));
    max:=Filtered(max,x->Number(max,y->x<>y and IsSubset(x,y) 
      and Index(x,y)<=3)=0);
    r.index:=fail;
    while Length(max)>0 do
      m:=max[1];
      max:=max{[2..Length(max)]};
      Print("maximal index ",IndexNC(Image(red),m),"\n");
      int:=PreImage(red,m);
      iso:=IsomorphismFpGroup(int);
      ran:=Range(iso);
      t:=CosetTableFromGensAndRels(FreeGeneratorsOfFpGroup(ran),
          RelatorsOfFpGroup(ran),
          List(w,x->UnderlyingElement(Image(iso,x))):
            silent:=true,hard,max:=mfact*10^20,Wo:=mfact*10^9);
      if t=fail then 
        Print("enumeration failed!\n");
      else
        r.index:=Length(t[1])*IndexNC(Image(red),m);
        Print("enumeration succeeded : ",r.index,"!\n");

        max:=[];
      fi;
    od;

  else
    Print("starting coset enum\n");
    t:=CosetTableFromGensAndRels(FreeGeneratorsOfFpGroup(Source(map)),
        RelatorsOfFpGroup(Source(map)),
        List(w,UnderlyingElement):
          silent:=true,hard,max:=mfact*10^20,Wo:=mfact*10^9);
    if t=fail then Print("enumeration failed!\n");r.index:=fail;

      Add(infinite,[r,Source(map),w,map]);
    else 
      r.index:=Length(t[1]);
      Print("enumeration succeeded : ",r.index,"!\n");

      if ValueOption("abel")=true and r.index<10000 then
        t:=SubgroupNC(Source(map),w);
        t:=AbelianInvariants(t);
        Print("Abelianization:",t,"\n");
        r.abel:=t;
      fi;

      # now try to find relators.

      Append(w,List(w,x->x^DenominatorRat(val))); # p-th powers as extra gens
      trace:=[];
      if dokerword or dopres then
        t:=NEWTC_CosetEnumerator(FreeGeneratorsOfFpGroup(Source(map)),
          RelatorsOfFpGroup(Source(map)),
          List(w,UnderlyingElement),
          true,trace);
      else
        t:="not done";
      fi;

      if dokerword then
        # make word in generators
        m:=mats[2]^[[-1,1],[0,-1]];
        wmg:=WordsForMatsTry(map,[m]:start:=pstart);
        wmg:=wmg[1]^NumeratorRat(val);

        #wmg:=w[1]^5*w[2]^5*w[1]^-5*w[2]*w[1]^10;
        #wmg:=(w[2]^5*w[1]^5*w[2]^-1*w[1]^-5*w[2]^-5*w[1])^(w[1]*w[2]^-15);
        a:=NEWTC_Rewrite(t,1,LetterRepAssocWord(UnderlyingElement(wmg)));

        e:=FreeGroup("a","b");
        m:=One(e);
        b:=ShallowCopy(GeneratorsOfGroup(e));
        Append(b,List(b,x->x^DenominatorRat(val))); # p-th powers as extra gens

        eval:=function(i)
        local w,j;
          w:=One(b[1]);
          if not IsBound(b[i]) then
            for j in t.secondary[i] do
              if j<0 then
                w:=w/eval(-j);
              else
                w:=w*eval(j);
              fi;
            od;
            b[i]:=w;
          fi;
          return b[i];
        end;

        for i in a do
          if i<0 then m:=m/eval(-i);
          else m:=m*eval(i); fi;
        od;

        if
        ImagesRepresentative(map,wmg)=MappedWord(m,GeneratorsOfGroup(e),mats)
        then
          r.kerword:=m;
        else
          Error("word");
        fi;
      fi;


      # relators amongst generators
      if dopres then
        m:=FpGroupPresentation(RewPresSome(t));

        # got back to original generatores
        nf:=FreeGroup("x","y");
        t:=List(RelatorsOfFpGroup(m),x->MappedWord(x,FreeGeneratorsOfFpGroup(m),
          [nf.1,nf.2,nf.1^DenominatorRat(val),nf.2^DenominatorRat(val)]));
        t:=Filtered(t,x->Length(x)<50000);
        m:=RelatorRepresentatives(t);
        SortBy(m,NrSyllables);
        t:=Minimum(10,Length(m));
        while t<Length(m) and NrSyllables(m[t])=NrSyllables(m[t+1]) do
          t:=t+1;
        od;
        m:=m{[1..t]};
        r.relators:=m;
      fi;
    fi;
  fi;
  Add(result,r);
  return r;
end;

Allatest:=function(a,b)
local r,one,g,t,s,gp,ts,e,c;
   r:=Integers mod a^3;
   one:=One(r);
   g:=elementarygens(a/b)*one;
   t:=[[1,a^2/b],[0,1]]*one;
   ts:=[t];
   gp:=SL(2,r);
   FittingFreeLiftSetup(gp);
   g:=SubgroupNC(gp,g);
   FittingFreeSubgroupSetup(gp,g);
   s:=SubgroupNC(gp,ts);
   FittingFreeSubgroupSetup(gp,s);
   for t in ts do
     for e in GeneratorsOfGroup(gp) do
       c:=t^e;
       if not c in s then
         if not c in g then
           Error("notin!");
         else
           Add(ts,c);
           c:=Size(s);
           s:=SubgroupNC(gp,ts);
           FittingFreeSubgroupSetup(gp,s);
           Print("expand ",c," => ",Size(s),"\n");
         fi;
       fi;
     od;
   od;
   Error();
end;

AmalgamSL2k:=function(p)
local f,g,mats,gf,mare,red,gamma,gens,rels,i,sub,a,imgs,new,map1,map2,suma,pre,
  orb,rep,sch,e,img,sg,show;

  if p<=1 or not IsInt(p) then Error("p");fi;

  p:=Set(Factors(p));
  if Length(p)>1 then
    # amalgamate ths SL(Z)
    map1:=AmalgamSL2k(Product(p{[1..Length(p)-1]}):simplify:=false);
    map2:=AmalgamSL2k(p[Length(p)]:simplify:=false);
    a:=Source(map1);
    e:=Source(map2);
    gf:=List(GeneratorsOfGroup(a),String);
    # name generators different
    f:=List("zwcdefgh",x->[x]);
    f:=Difference(f,gf);
    i:=0;
    while Length(f)=0 do
      i:=i+1;
      f:=[Concatenation("x",String(i)),Concatenation("y",String(i))];
      f:=Difference(f,gf);
    od;
    gf:=Concatenation(gf,f{[1,2]});
    f:=FreeGroup(gf);
    gf:=GeneratorsOfGroup(f);
    rels:=List(RelatorsOfFpGroup(a),
      x->MappedWord(x,FreeGeneratorsOfFpGroup(a),gf{[1..Length(gf)-2]}));
    # relators of second map first two generators to first two -- this way
    # we identify the Z-generators w/o need to duplicate (implicit Tietze)
    red:=gf{[1,2,Length(gf)-1,Length(gf)]};
    Append(rels,Filtered(List(RelatorsOfFpGroup(e),
      x->MappedWord(x,FreeGeneratorsOfFpGroup(e),red)),
        x->not x in rels));
    f:=f/rels;
    new:=Concatenation(MappingGeneratorsImages(map1)[2],
      MappingGeneratorsImages(map2)[2]{[3,4]});
    return GroupHomomorphismByImages(f,Group(new),GeneratorsOfGroup(f),new);
  else
    # normal
    p:=p[1];
  fi;


  show:=ValueOption("show")=true;
  f:=FreeGroup("a","b");
  g:=f/ParseRelators(f,"a4,a2=(ab)3");
  # choose generators as in Serre
  mats:=[[[0,1],[-1,0]],[[1,0],[1,1]]];
  gf:=Integers mod p;
  mare:=mats*One(gf);
  red:=GroupHomomorphismByImagesNC(g,Group(mare),GeneratorsOfGroup(g),
    mare);

  # generators of the second SL. See Serre, TREES, p.81. But we conjugate by
  # inverse of first gen, so that gamma maps to \Gamma_0(p) in both cases.
  new:=List(mats,x->List(x,r->List(r,ShallowCopy)));
  for i in new do i[1][2]:=i[1][2]*1/p;i[2][1]:=i[2][1]*p;od;
  a:=new[1]^-1;
  new:=List(new,x->x^a);
  map1:=GroupHomomorphismByImagesNC(g,Group(mats),GeneratorsOfGroup(g),mats);
  map2:=GroupHomomorphismByImagesNC(g,Group(new),GeneratorsOfGroup(g),new);
  if show then View("beta=",map2,"\n");fi;

  # generic orbit/stabilizer
  orb:=[[0,1]*One(gf)];
  rep:=[One(g)];
  sch:=[];
  suma:=[];
  a:=1;
  while a<=Length(orb) do
    for i in [1..Length(mats)] do
      for e in [1,-1] do
        img:=OnLines(orb[a],mare[i]^e);
        pre:=Position(orb,img);
        if pre=fail then
          Add(orb,img);
          Add(rep,rep[a]*GeneratorsOfGroup(g)[i]^e);
        else
          sg:=rep[a]*GeneratorsOfGroup(g)[i]^e/rep[pre];
          img:=MappedWord(sg,GeneratorsOfGroup(g),mats);
          pre:=Position(suma,img);
          if IsOne(img) then
            # ignore
          elif pre=fail then
            pre:=Position(suma,img^-1);
            if pre=fail then
              Add(sch,sg);
              Add(suma,img);
            fi;
          else
            if NrSyllables(UnderlyingElement(sg))
                <NrSyllables(UnderlyingElement(sch[pre])) then
              sch[pre]:=sg;
            fi;
          fi;
        fi;
      od;
    od;
    a:=a+1;
  od;

  if p<100 then

    gamma:=Range(red);
    NiceMonomorphism(gamma:cheap); # don't try hard to reduce degree
    sub:=Stabilizer(gamma,Immutable([0,1]*One(gf)),OnLines);
    gamma:=PreImage(red,sub);

    # take images of Gamma_0 in second copy
    sub:=GeneratorsOfGroup(gamma);
    suma:=List(sub,x->ImagesRepresentative(map2,x));

    # eliminate duplicates
    f:=Set(List(Unique(suma),x->Position(suma,x)));

    if Index(g,SubgroupNC(g,sub{f}))=IndexNC(g,gamma) then
      sub:=sub{f};
      suma:=suma{f};
    fi;

    if not IsSubset(List(sch,x->ImagesRepresentative(map2,x)),suma) then
      Error("SUB");
    fi;
  else
    sub:=sch;
    suma:=List(sub,x->ImagesRepresentative(map2,x));
  fi;
  if show then Print("Schreier gens:",sch," ",sub," ",suma,"\n");fi;

  # and express as words
  a:=WordsForMatsTry(map1,suma:nocache,lim:=QuoInt(p,2)+1);
  if show then Print("words:",a,"\n");fi;


  f:=FreeGroup("a","b","x","y");
  gens:=GeneratorsOfGroup(f);
  rels:=ParseRelators(f,"a4,a2=(ab)3,x4,x2=(xy)3");
  for i in [1..Length(sub)] do
    Add(rels,
      MappedWord(UnderlyingElement(sub[i]),FreeGeneratorsOfFpGroup(g),gens{[3,4]})/
      MappedWord(UnderlyingElement(a[i]),FreeGeneratorsOfFpGroup(g),gens{[1,2]}));
  od;
  if show then Print("rels :",rels,"\n");fi;
  a:=f/rels;

  img:=Concatenation(mats,new);
  red:=GroupHomomorphismByImages(a,Group(img),GeneratorsOfGroup(a),img);

  pre:=[[[0,1],[-1,0]],[[1,0],[1,1]],[[0,1/p],[-p,0]],[[1,-1/p],[0,1]]];
  pre:=Concatenation(pre,List(pre,TransposedMat));
  pre:=WordsForMatsTry(red,pre:short);
  if ValueOption("simplify")=true then
    new:=IsomorphismSimplifiedFpGroup(a);
  else
    new:=IdentityMapping(a);
  fi;
  pre:=List(pre,x->ImagesRepresentative(new,x));
  g:=Range(new);
  #map1:=InverseGeneralMapping(new)*red;
  f:=List(GeneratorsOfGroup(a),x->ImagesRepresentative(new,x));

  suma:=List(FreeGeneratorsOfFpGroup(g),
    x->PositionProperty(f,y->x=UnderlyingElement(y)));
  if ForAll(suma,IsInt) then
    f:=f{suma};
    img:=img{suma};
  fi;


  # safety check of relators
  if not ForAll(RelatorsOfFpGroup(g),
    x->IsOne(MappedWord(x,List(f,UnderlyingElement),img))) then
    Error("rels");
  fi;
  #red:=GroupHomomorphismByImages(g,Range(red),f,img);
  red:=GroupGeneralMappingByImages(g,Range(red),f,img);
  SetIsMapping(red,true);
  red!.specialpre:=pre;
  return red;

end;

TryWord2:=function(hom,mat)
local prdprime,prime,onp,op,gens,o,l,prd,start,ende,j,k,a,i,m,one,
      istransvec,dict,new,dups,ap,mgi,let,prw,mf;

  mgi:=MappingGeneratorsImages(hom);
  # find a boring prime
  let:=ShallowCopy(mgi[1]);
  gens:=ShallowCopy(mgi[2]);
  prime:=23;
  op:=Z(prime)^0;

  # generators, inverse closed
  for i in [1..Length(gens)] do
    if not gens[i]^-1 in gens then
      Add(gens,gens[i]^-1);
      Add(let,let[i]^-1);
    fi;
  od;

  # first form all products of length up to l. There are technically |gens|^l
  # products, so 

  l:=LogInt(Int(2*10^10/Length(gens[1])^2),Length(gens));

  one:=One(gens[1]);
  onp:=one*op;
  prd:=[one];
  prw:=[One(let[1])];
  prdprime:=[onp];
  dups:=[];
  dict:=NewDictionary(onp,GL(Length(onp),prime),true);

  start:=1;
  for m in [1..l] do
    Print(m,"\n");
    ende:=Length(prd);
    for j in [start..ende] do
      for k in [1..Length(gens)] do
        a:=prd[j]*gens[k];
	ap:=a*op;
	i:=LookupDictionary(dict,ap);
	if i<>fail then
	  if not IsBound(dups[i]) then
	    # first duplication
	    new:=a<>prd[i];
	    if new then dups[i]:=[i];fi;
	  else
	    new:=ForAll(dups[i],x->prd[x]<>a);
	  fi;
	  # will duplicate also new one
	  if new then Add(dups[i],Length(prd)+1);fi;
	else
	  new:=true;
	fi;
	
	if new then
	  Add(prd,a);
	  Add(prw,prw[j]*let[k]);
	  Add(prdprime,ap);
	  if i=fail then
	    AddDictionary(dict,ap,Length(prd));
	  fi;

	  if a=mat then
	    return prw[Length(prw)];
	  fi;
	fi;
      od;
    od;
    start:=ende+1;
  od;
  # prd also will be inverse-closed

  Print("Stage2\n");

  for i in [1..Length(prd)] do
    mf:=LeftQuotient(prd[i],mat);
    ap:=LookupDictionary(dict,mf*op);
    if ap<>fail then
      if IsBound(dups[ap]) then
	ap:=dups[ap];
      else
	ap:=[ap];
      fi;
      for j in ap do
	if prd[j]=mf then
	  Error("found2");
	fi;
      od;
    fi;
  od;


  for i in [1..Length(prd)] do
    Print("Stage3 ",i,"\n");
    for j in [1..Length(prd)] do

      mf:=LeftQuotient(prd[i]*prd[j],mat);
      ap:=LookupDictionary(dict,mf*op);
      if ap<>fail then
	if IsBound(dups[ap]) then
	  ap:=dups[ap];
	else
	  ap:=[ap];
	fi;
	for k in ap do
	  if prd[k]=mat then
	    Error("found3");
	  fi;
	od;
      fi;

      mf:=Comm(prd[i],prd[j]);
      if mf=mat then
	Error("found4");
      fi;

    od;
  od;

  Error("notfound");
end;

HumphriesGrp:=Group([[1,1,0],[0,-1,0],[0,0,-1]],[[-1,0,0],[0,1,1],[0,0,-1]],[[-1,0,0],[0,-1,0],[1,5,1]],[[-1,0,0],[0,-1,0],[1,4,1]]);

TwoGenHumTest:=function(rad)
local f,map,cnt,g,primes,ok,w;
  cnt:=0;
  f:=FreeGroup(4);
  map:=GroupHomomorphismByImages(f,HumphriesGrp,
    GeneratorsOfGroup(f),GeneratorsOfGroup(HumphriesGrp));
  repeat
    cnt:=cnt+1;
    ok:=false;
    w:=List([1,2],x->PseudoRandom(f:radius:=rad));
    g:=List(w,x->ImagesRepresentative(map,x));
    g:=Group(g,One(HumphriesGrp));
    if IsDenseIR2(g) then
      primes:=PrimesNonSurjective(g);
      Print(cnt,primes,"\n");
      ok:=Length(primes)=0;
    fi;
  until ok;
  return [w,g];
end;

CongruenceClosureFP:=function(hom,s)
local f,int,sub,m,sel,u;
  f:=FamilyObj(s)!.wholeGroup;
  int:=IntermediateSubgroups(f,s);
  sub:=Concatenation([s],int.subgroups,[f]);
  m:=List(sub,x->ModularSubgroup(GeneratorsOfGroup(Image(hom,x))));
  # which ones are congruence?
  sel:=Filtered([1..Length(m)],x->IsCongruence(m[x]))-1;
  u:=First(sel,x->not ForAny(sel,y->[y,x] in int.inclusions));
  return sub[u+1];
end;

DisplayResults:=function()
local val,den,i,a,b,c,d,pr;
  pr:=function(from,what)
  local p,i,l,e,s;
    s:=true;
    what:=Set(what);
    l:=fail;
    for i in what do
      p:=Position(from,i);
      if l<>fail then 
        if p=l+1 then
          e:=i;
          l:=p; # range go on
        else
          # range ended
          if e<>fail then
            # range was more than one
            Print(" - ",e);
          fi;
          l:=fail;
        fi;
      fi;

      if l=fail then 
        # no range on the go, just print current number
        if not s then
          Print(", ");
          s:=true;
        fi;
        Print(i);
        l:=p;
        e:=fail;
      fi;

    od;
    if l<>fail and e<>fail then
      # there is a range to close
      Print(" - ",e);
    fi;

  end;

  val:=Set(List(result,x->x.val));
  den:=Set(List(val,DenominatorRat));
  SortBy(den,PrimeBase);
  for i in den do
    c:=Filtered(val,x->DenominatorRat(x)=i); # relevant values
    d:=Filtered(result,x->DenominatorRat(x.val)=i);
    a:=Filtered(d,x->IsInt(x.index));
    b:=Filtered(d,x->x.index=fail);
    d:=Filtered(d,x->x.index=infinity);
    a:=List(a,x->x.val);
    b:=List(b,x->x.val);
    d:=List(d,x->x.val);
    Print(i," : ");
    pr(c,a);
    Print(" | ");
    pr(c,b);
    if Length(d)>0 then
      Print(" || ");
      pr(c,d);
    fi;
    Print("\n");
  od;
end;

TryKerGens:=function(map,m)
local den,gens,ts,c,a,w,n;
  den:=Lcm(List(Flat(MappingGeneratorsImages(map)[2]),DenominatorRat));
  den:=PrimeBase(den);
  gens:=[];
  w:=[];
  a:=[[[1,1/den],[0,1]],[[1,0],[1/den,1]]];
  c:=[[-1,1],[0,-1]];
  Add(a,c);
  a:=TryWordEnum(map,a);
  ts:=[[[1,m/den],[0,1]],[[1,0],[m/den,1]]];
  Append(gens,ts);
  w:=List(a{[1,2]},x->x^m);
  Append(gens,List(ts,x->x^c));
  Append(w,List(w{[1,2]},x->x^a[3]));
  Append(w,List(w{[1,2]},x->x^a[3]));
  # remove duplicate
  gens:=gens{[1,2,4]};
  w:=w{[1,2,4]};

  if List(w,x->Image(map,x))<>gens then Error("words");fi;
  a:=SubgroupNC(Source(map),w);
  n:=Size(SL(2,Integers mod m));
  Print("m=",m," expect index ",n,"\n");
  if Index(Source(map),a:hard,max:=10^20,Wo:=10^9)<>n then Error("index");fi;
  return [w,gens];
end;

TestKerWord:=function(map,val)
local den,gens,ts,c,a,w,n,m,el,epi,sub,suw,red,f,prime,redl,has,i,fa;
  m:=NumeratorRat(val)^2;
  den:=Lcm(List(Flat(MappingGeneratorsImages(map)[2]),DenominatorRat));
  den:=PrimeBase(den);
  gens:=[];
  w:=[];
  a:=[[[1,1/den],[0,1]],[[1,0],[1/den,1]]];
  c:=[[-1,1],[0,-1]];
  Add(a,c);
  a:=TryWordEnum(map,a);
  ts:=[[[1,m/den],[0,1]],[[1,0],[m/den,1]]];
  Append(gens,ts);
  w:=List(a{[1,2]},x->x^m);
  Append(gens,List(ts,x->x^c));
  Append(w,List(w{[1,2]},x->x^a[3]));
  # remove duplicate
  gens:=gens{[1,2,4]};
  w:=w{[1,2,4]};

  if List(w,x->Image(map,x))<>gens then Error("words");fi;

  el:=elementarygens(val);
  suw:=TryWordEnum(map,el);
  sub:=SubgroupNC(Source(map),suw);
  if not ForAll(w,x->x in sub) then Error("contain?");fi;
  epi:=EpimorphismFromFreeGroup(Group(Concatenation(el,List(el,x->x^den))));

  prime:=5;
  if prime=den then prime:=NextPrimeInt(prime);fi;
  red:=reducemod(map,prime);
  red:=red*IsomorphismPermGroup(Range(red));
  has:=[];
  fa:=[];
  repeat
    sub:=false;epi:=false;
    prime:=NextPrimeInt(prime);
    if prime=den then prime:=NextPrimeInt(prime);fi;
    Print("prime=",prime,"\n");
    redl:=reducemod(map,prime);
    redl:=redl*IsomorphismPermGroup(Range(redl));
    redl:=redl*NaturalHomomorphismByNormalSubgroup(Range(redl),Centre(Range(redl)));
    a:=SubdirectDiagonalPerms(MappingGeneratorsImages(red)[2],
      MappingGeneratorsImages(redl)[2]);
    a:=Group(a);
    if Size(a)>10^12 then
      epi:=List(OrbitsDomain(a,MovedPoints(a)),Set);;
      epi:=Reversed(Set(epi));
      i:=Length(epi);
      repeat
        i:=i-1;
        f:=ActionHomomorphism(a,Union(epi{[1..i]}),"surjective");
        f:=List(GeneratorsOfGroup(a),x->ImagesRepresentative(f,x));
        f:=Group(f,());
      until Size(f)<10^12;
      Print("biggie ",Size(a),"->",Size(f),"\n");
      a:=f;

    fi;
    sub:=SmallerDegreePermutationRepresentation(a);
    a:=List(GeneratorsOfGroup(a),x->ImagesRepresentative(sub,x));
    f:=Image(sub);

    red:=GroupHomomorphismByImages(Source(red),f,
      MappingGeneratorsImages(red)[1],a);
Print("deg",NrMovedPoints(Range(red))," ",Size(Range(red)),"\n");

    sub:=List(suw,x->ImagesRepresentative(red,x));
    # note that the group is constructed from scratch
    sub:=Group(Concatenation(sub,List(sub,x->x^den)));
    epi:=EpimorphismFromFreeGroup(sub);
    for i in Difference([1..3],has) do
      f:=PreImagesRepresentative(epi,Image(red,w[i]));
      a:=MappedWord(f,GeneratorsOfGroup(Source(epi)),Concatenation(el,List(el,x->x^den)));
      if a=gens[i] then
        Add(has,i);
        fa[i]:=LetterRepAssocWord(f);
      else
        f:=Factorization(sub,Image(red,w[i]));
        a:=MappedWord(f,GeneratorsOfGroup(Source(epi)),Concatenation(el,List(el,x->x^den)));
        if a=gens[i] then
          Add(has,i);
          fa[i]:=LetterRepAssocWord(f);
        fi;
      fi;
    od;
      
    Print("work=",has,"\n");
  until Length(has)=3;
  f:=FamilyObj(One(Source(epi)));
  fa:=List(fa,x->AssocWordByLetterRep(f,x));
  a:=FreeGroup("a","b");
  fa:= List(fa,x->
    MappedWord(x,MappingGeneratorsImages(epi)[1],[a.1,a.2,a.1^den,a.2^den]));
  if not ForAll([1..Length(gens)],x->gens[x]=
    MappedWord(fa[x],GeneratorsOfGroup(a),el)) then Error("wrong");fi;
  return fa;
end;

TestCube:=function(map,val)
local den,gens,ts,c,a,w,n,m,el,epi,sub,suw,red,f,prime,redl,has,i,fa;
  m:=NumeratorRat(val)^2;
  den:=Lcm(List(Flat(MappingGeneratorsImages(map)[2]),DenominatorRat));
  den:=PrimeBase(den);
  gens:=[];
  w:=[];
  a:=[[[1,1/den],[0,1]],[[1,0],[1/den,1]]];
  c:=[[-1,1],[0,-1]];
  Add(a,c);
  a:=TryWordEnum(map,a);
  ts:=[[[1,m/den],[0,1]],[[1,0],[m/den,1]]];
  Append(gens,ts);
  w:=List(a{[1,2]},x->x^m);
  Append(gens,List(ts,x->x^c));
  Append(w,List(w{[1,2]},x->x^a[3]));
  # remove duplicate
  gens:=gens{[1,2,4]};
  w:=w{[1,2,4]};

  if List(w,x->Image(map,x))<>gens then Error("words");fi;

  el:=elementarygens(val);
  suw:=TryWordEnum(map,el);
  sub:=SubgroupNC(Source(map),suw);
  if not ForAll(w,x->x in sub) then Error("contain?");fi;
  epi:=EpimorphismFromFreeGroup(Group(Concatenation(el,List(el,x->x^den))));

  red:=reducemod(map,NumeratorRat(val)^3);
  red:=red*IsomorphismPermGroup(Range(red));
  has:=[];
  fa:=[];

  sub:=List(suw,x->ImagesRepresentative(red,x));
  # note that the group is constructed from scratch
  sub:=Group(Concatenation(sub,List(sub,x->x^den)));
  epi:=EpimorphismFromFreeGroup(sub);
  for i in Difference([1..3],has) do
    f:=PreImagesRepresentative(epi,Image(red,w[i]));
    a:=MappedWord(f,GeneratorsOfGroup(Source(epi)),Concatenation(el,List(el,x->x^den)));
    if a=gens[i] then
      Add(has,i);
      fa[i]:=LetterRepAssocWord(f);
    else
      #if i=3 and (sub.1*sub.2)^NumeratorRat(val)=Image(red,w[i]) then
      #  Error("hooray");
      #fi;
      f:=Factorization(sub,Image(red,w[i]));
      a:=MappedWord(f,GeneratorsOfGroup(Source(epi)),Concatenation(el,List(el,x->x^den)));
#      if a=gens[i] then
      Add(has,i);
      fa[i]:=LetterRepAssocWord(f);
#      fi;
    fi;
  od;
    
  Print("work=",has,"\n");
  f:=FamilyObj(One(Source(epi)));
  fa:=List(fa,x->AssocWordByLetterRep(f,x));
  a:=FreeGroup("a","b");
  fa:= List(fa,x->
    MappedWord(x,MappingGeneratorsImages(epi)[1],[a.1,a.2,a.1^den,a.2^den]));
  #if not ForAll([1..Length(gens)],x->gens[x]=
  #  MappedWord(fa[x],GeneratorsOfGroup(a),el)) then Error("wrong");fi;
  return fa;
end;



TryFormula:=function()
local mats,r,a,b,c,d,e,f,inds,prd,eq;
  r:=PolynomialRing(Rationals,["a","b","c","d","e","f"]:old);
  inds:=IndeterminatesOfPolynomialRing(r);
  a:=inds[1];
  b:=inds[2];
  c:=inds[3];
  d:=inds[4];
  e:=inds[5];
  f:=inds[3];
  mats:=List([1..6],x->IdentityMat(2,0));
  mats[1][1][2]:=d*a;
  mats[2][2][1]:=d*b;
  mats[3][1][2]:=d*c;
  mats[4][2][1]:=d*a;
  mats[5][1][2]:=d*b;
  mats[6][2][1]:=d*c;
  prd:=mats[1]*mats[2]*mats[3]*mats[4]*mats[5]*mats[6];
  eq:=[prd[1][1]-1,prd[1][2],prd[2][1],prd[2][2]-1];
  return eq;
end;

TestPat1:=function(d)
local bd,ar,oa,a,b,c,x,y,den,sq;
  den:=DenominatorRat(d);
  oa:=[0];
  y:=elementarygens(d);
  x:=y[1];y:=y[2];
  for bd in [50,100..20000] do
    Print("bound: ",bd,"\n");
    ar:=Difference([-bd..bd],oa);
    oa:=Union(oa,ar);
    for a in ar do
      if IsZero(a mod den) then
        sq:=IsZero(a mod (den^2));
        for b in [-bd..bd] do
          if sq or IsZero(b mod den) then
            for c in [-den..den] do
              if IsZero(a*b*c*d^2+a+b+c) and not IsZero(a*b*c) then 
                if not IsOne(x^a*y^b*x^c*y^a*x^b*y^c) then Error("ugh!");fi;
                return [a,b,c];
              fi;
              if IsZero(a*b*c*d^2+a-b+c) and not IsZero(a*b*c) then 
                if not IsOne(x^a*y^b*x^c*y^-a*x^-b*y^-c) then Error("ugh2!");fi;
                return [a,b,c,-1];
              fi;
            od;
          fi;
        od;
      fi;
    od;
  od;

  return fail;
end;


TestPat2:=function(d)
local bd,br,oa,a,b,c,x,y,den,num,sq;
  y:=elementarygens(d);
  x:=y[1];y:=y[2];
  num:=NumeratorRat(d)^2;
  den:=DenominatorRat(d)^2;
  br:=Union([-1000..1000],DenominatorRat(d)*[-200..200]);
  br:=Reversed(br);
  for a in br do
    for b in [1000,999..-1000] do
      if not IsZero(a*b) then

        c:=-(a+b)*den/(num*a*b+den);
        if IsInt(c) and c<>0  then
          if not IsZero(a*b*c*d^2+a+b+c) then 
            Error("ugh2");
          else
            if not IsOne(x^a*y^b*x^c*y^a*x^b*y^c) then Error("ugh!");fi;
            return [a,b,c];
          fi;
        fi;

        c:=-(a-b)*den/(num*a*b+den);
        if IsInt(c) and c<>0  then
          if not IsZero(a*b*c*d^2+a-b+c) then 
            Error("ugh3");
          else
            if not IsOne(x^a*y^b*x^c*y^-a*x^-b*y^-c) then Error("ugh4!");fi;
            return [a,b,c,-1];
          fi;
        fi;

      fi;
    od;
  od;
  return fail;
end;

Symmfi:=function(d)
local g,epi,gens,o,a,b,e,z,t;
  g:=Group(elementarygens(d));
  epi:=EpimorphismFromFreeGroup(g);
  gens:=MappingGeneratorsImages(epi);
  gens:=[Concatenation(gens[1],List(gens[1],Inverse)),
         Concatenation(gens[2],List(gens[2],Inverse))];
  o:=[One(g)];
  t:=[One(Source(epi))];
  a:=1;
  while a<=Length(o) do
    for b in [1..Length(gens[1])] do
      e:=o[a]*gens[2][b]; 
      if not e in o then
        Add(o,e);
        Add(t,t[a]*gens[1][b]);
        z:=PositionProperty(o,y->TransposedMat(y^-1*e)=y^-1*e and y<>e);
        if z<>fail then Error("EEE");fi;
      fi;
    od;
  od;
end;

Handle2:=function(p,exp)
local e,num,n,hom;
  hom:=AmalgamSL2k(p);
  PMAPS:=[];
  for e in exp do
    num:=Filtered([1..4*p^e],x->Gcd(x,p)=1);
    for n in num do
      Print("Doing: ",n/p^e,"\n");
      MobiusTest("Zwei",hom,n/p^e);
    od;
  od;
end;


# Hermite NF code, factorize in SLNZ




TryWord:=function(hom,mat)
local m,p,red,mr,g,h2,w,a;
  m:=MappingGeneratorsImages(hom);
  p:=ValueOption("start");
  if p=fail then
    p:=2;
  fi;
  repeat
    p:=NextPrimeInt(p);
    red:=List(m[2],x->x*Z(p)^0);
    mr:=mat*Z(p)^0;
    g:=Group(red);
    h2:=GroupHomomorphismByImages(Source(hom),g,m[1],red);
    w:=PreImagesRepresentative(h2,mr);
    a:=Image(hom,w);
    Print(p,":",a-mat," ",w,"\n");
  until a=mat;
  return w;
end;

TryWord0:=function(hom,mat)
local m,p,red,mr,g,h2,w,a;
  m:=MappingGeneratorsImages(hom);
  p:=ValueOption("start");
  if p=fail then
    p:=2;
  fi;
  repeat
    p:=NextPrimeInt(p);
    red:=List(m[2],x->x*Z(p)^0);
    mr:=mat*Z(p)^0;
    g:=Group(red);
    h2:=GroupHomomorphismByImages(Source(hom),g,m[1],red);
    SetEpimorphismFromFreeGroup(g,h2);
    w:=Factorization(g,mr);
    a:=Image(hom,w);
    Print(p,":",a-mat," ",w,"\n");
  until a=mat;
  return w;
end;

TryWord1:=function(hom,mat,q)
local m,ring,red,mr,g,h2,w,a,n,piso,orb,p;
  p:=Factors(q)[1];
  m:=MappingGeneratorsImages(hom);
  n:=LogInt(q,p)-1;
  repeat
    n:=n+1;
    ring:=Integers mod p^n;
    red:=List(m[2],x->x*One(ring));
    mr:=mat*One(ring);
    g:=Group(red);
    orb:=Orbit(g,One(g)[1],OnRight);
    piso:=ActionHomomorphism(g,orb,OnRight,"surjective");
    h2:=GroupHomomorphismByImages(Source(hom),Image(piso),m[1],
	 List(red,x->ImagesRepresentative(piso,x)));
    w:=PreImagesRepresentative(h2,ImagesRepresentative(piso,mr));
    a:=Image(hom,w);
    Print(n,":",a-mat,"\n");
  until a=mat;
  return w;
end;

TryWord2:=function(hom,mat)
local prime,onp,op,gens,o,l,prd,start,ende,j,k,a,i,m,one,dim,
      istransvec,dict,new,dups,ap,mgi,let,prw,mf,non,sel,maxmem,nrm;

  maxmem:=10^10;
  if ValueOption("maxmem")<>fail then
    maxmem:=ValueOption("maxmem");
  fi;
  nrm:=ValueOption("norm");
  non:=ValueOption("nonhom");
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

  sel:=[];
  for i in [1..Length(gens)] do
    if not ForAny([1..i-1],j->gens[i]=gens[j]) then
      Add(sel,i);
    fi;
  od;

  # first form all products of length up to l. There are technically |gens|^l
  # products, so 

  l:=LogInt(Int(maxmem/Length(gens[1])^2),Length(gens));

  one:=One(gens[1]);
  dim:=Length(one);
  onp:=one*op;
  prd:=[one];
  prw:=[One(let[1])];
  dups:=[];
  dict:=NewDictionary(onp,GL(Length(onp),prime),true);
  AddDictionary(dict,onp,1);

  start:=1;
  for m in [1..l] do
    Print(m,":",Length(prd),"\n");
    ende:=Length(prd);
    for j in [start..ende] do
      for k in sel do
        a:=prd[j]*gens[k];
	ap:=a*op;
	i:=LookupDictionary(dict,ap);
	if i=fail then
	  new:=true;
	elif a=prd[i] then
	  new:=false;
	else
	  if not IsBound(dups[i]) then
	    # first duplication
	    new:=a<>prd[i];
	    if new then dups[i]:=[i];fi;
	  else
	    new:=ForAll(dups[i],x->prd[x]<>a);
	  fi;
	  # will duplicate also new one
	  if new then Add(dups[i],Length(prd)+1);fi;
	fi;
	
	if new then
	  #if nrm<>fail and not IsOne(a) and nrm(a)<nrm(prd[j]) then
	  #  Error("normsmall");
	  #fi;
	  Add(prd,a);
	  Add(prw,prw[j]*let[k]);
	  if i=fail then
	    AddDictionary(dict,ap,Length(prd));
	  fi;

	  if a=mat and
            (non=fail or not
            IsOne(ImagesRepresentative(non,prw[Length(prw)]))) then
	    return prw[Length(prw)];
	  fi;
	fi;
      od;
    od;
    start:=ende+1;
  od;
  # prd also will be inverse-closed

  Print("Stage2new :",Length(prd),"\n");

  for i in [1..Length(prd)] do
    Print("Stage2 ",i,"\n");
    for j in [start..Length(prd)] do

      if Sum([1..dim],k->prd[i][1][k]*prd[j][k][1])=mat[1][1] 
        and prd[i]*prd[j]=mat and
        (non=fail or not
        IsOne(ImagesRepresentative(non,prw[i]*prw[j]))) then
          return prw[i]*prw[j];
          Error("found2");
      fi;

    od;
  od;


  # older stage 2 -- divide off

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

      mf:=Comm(prd[i],prd[j]);
      if mf=mat then
	Error("found4");
      fi;
    od;
  od;

  for i in [1..Length(prd)] do
    Print("Stage4 ",i,"\n");
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

    od;
  od;

  Error("notfound");
end;


#rho1.1=t12*t13^-3*t32*t23^-3;
#rho1.2=t12^2*t13^-2*t21^-3*t31^-1*t13^-1*t12;
#rho1.3=t13*t12^-1*t21*t13^-1*t32*t23^-3;
#u:=Subgroup(f,[f.1*f.2^-3*f.6*f.4^-3,
#  f.1^2*f.2^-2*f.3^-3*f.5^-1*f.2^-1*f.1,
#  f.2*f.1^-1*f.3*f.2^-1*f.6*f.4^-3]);

FindForm:=function(g)
  local n,f,m,at,ai,i,j,k,v,p,a;
  n:=DimensionOfMatrixGroup(g);
  f:=DefaultFieldOfMatrixGroup(g);
  m:=[];
  for a in GeneratorsOfGroup(g) do
    at:=TransposedMat(a);
    ai:=Inverse(a);
    # equation at*J=J*ai:
    for i in [1..n] do
      for j in [1..n] do
	v:=ListWithIdenticalEntries(n^2,0);
	for k in [1..n] do
	  #T_ak*J_kb    - J_akI_kb
	  p:=(k-1)*n+j;
	  v[p]:=v[p]+at[i][k];
	  p:=(i-1)*n+k;
	  v[p]:=v[p]-ai[k][j];
        od;
	v:=v*One(f);
	Add(m,v);
      od;
    od;
  od;
  return NullspaceMat(TransposedMat(m));
end;








HumphriesGrp:=Group([[1,1,0],[0,-1,0],[0,0,-1]],[[-1,0,0],[0,1,1],[0,0,-1]],[[-1,0,0],[0,-1,0],[1,5,1]],[[-1,0,0],[0,-1,0],[1,4,1]]);


OLDMonodromyExample:=function(n)
local x,f,g;
  x:=X(Rationals,"x");
  f:=(x-1)^4;
  if n=1 then
    g:=x^4-2*x^3+3*x^2-2*x+1;
  elif n=2 then
    g:=x^4-x^3+2*x^2-x+1;
  elif n=3 then
    g:=x^4-x^3+x^2-x+1;
  elif n=4 then
    g:=x^4+2*x^3+3*x^2+2*x+1;
  elif n=5 then
    g:=x^4+2*x^2+1;
  elif n=6 then
    g:=x^4+x^3+2*x^2+x+1;
  elif n=7 then
    g:=x^4+x^2+1;
  else
    Error("wrong n");
  fi;
  f:=CompanionMat(f);
  g:=CompanionMat(g);
  return Group(f,g);
end;

ASIndexGamma:=function(H,m)
  local ring,mats,G,ind;
  ring:=Integers mod m;
  mats:=List(GeneratorsOfGroup(H),x->x*One(ring));
  G:=Group(mats);
  FittingFreeLiftSetup(G);
  ind:=Size(SL(Length(One(G)),ring))/Size(G);
  Print("Index is ",ind,"=",Collected(Factors(ind)),"\n");
  return ind;
end;

ConstructOnePolrep:=function(mats,ii)
local f,n,r,v,sn,l,j,homo,a,homoe,fct,hom;

  f:=FieldOfMatrixList(mats);
  n:=Length(mats[1]);
  r:=PolynomialRing(f,n);
  v:=IndeterminatesOfPolynomialRing(r);
  sn:=SymmetricGroup(n);
    # homogeneous polynomials
    homo:=[];
    for j in Partitions(ii) do
      a:=Product([1..Length(j)],x->v[x]^j[x]);
      Append(homo,Orbit(sn,a,OnIndeterminates));
    od;
    Sort(homo);
    homoe:=List(homo,x->ExtRepPolynomialRatFun(x)[1]);
    fct:=function(x)
	  local a,zz,i,m;
	    a:=List(homo,y->Value(y,v,v*x));
	    m:=[];
	    for i in [1..Length(homo)] do;
	      m[i]:=ListWithIdenticalEntries(Length(homo),Zero(f));
	      zz:=ExtRepPolynomialRatFun(a[i]);
	      m[i]{List([1,3..Length(zz)-1],x->Position(homoe,zz[x]))}
		:=zz{[2,4..Length(zz)]};
	    od;
	    return m;
	end;
  return rec(gens:=List(mats,x->TransposedMat(fct(x))),
              kind:="polrep",
	      name:=Concatenation("Pol",String(ii)));
end;

ConstructAllPolreps:=function(mats)
local n,i,l;
  l:=[];
  n:=Length(mats[1]);
  for i in [1..n] do
    Add(l,ConstructOnePolrep(mats,i));
  od;
  return l;
end;

# 15-dim rep for n=3, from homogeneous 2, symmetric square, span (1,0,...)
rep15:=x->[ [ x[1][1]^4, x[1][1]^3*x[1][2], x[1][1]^3*x[1][3], x[1][1]^2*x[1][2]^2, 
      x[1][1]^2*x[1][2]*x[1][3], x[1][1]^2*x[1][3]^2, x[1][1]*x[1][2]^3, 
      x[1][1]*x[1][2]^2*x[1][3], x[1][1]*x[1][2]*x[1][3]^2, x[1][1]*x[1][3]^3,
      x[1][2]^4, x[1][2]^3*x[1][3], x[1][2]^2*x[1][3]^2, x[1][2]*x[1][3]^3, 
      x[1][3]^4 ], 
  [ 4*x[1][1]^3*x[2][1], x[1][1]^3*x[2][2]+3*x[1][1]^2*x[1][2]*x[2][1], 
      x[1][1]^3*x[2][3]+3*x[1][1]^2*x[1][3]*x[2][1], 
      2*x[1][1]^2*x[1][2]*x[2][2]+2*x[1][1]*x[1][2]^2*x[2][1], 
      x[1][1]^2*x[1][2]*x[2][3]+x[1][1]^2*x[1][3]*x[2][2]+2*x[1][1]*x[1][2]*x[\
1][3]*x[2][1], 2*x[1][1]^2*x[1][3]*x[2][3]+2*x[1][1]*x[1][3]^2*x[2][1], 
      3*x[1][1]*x[1][2]^2*x[2][2]+x[1][2]^3*x[2][1], 
      x[1][1]*x[1][2]^2*x[2][3]+2*x[1][1]*x[1][2]*x[1][3]*x[2][2]+x[1][2]^2*x[\
1][3]*x[2][1], 
      2*x[1][1]*x[1][2]*x[1][3]*x[2][3]+x[1][1]*x[1][3]^2*x[2][2]+x[1][2]*x[1]\
[3]^2*x[2][1], 3*x[1][1]*x[1][3]^2*x[2][3]+x[1][3]^3*x[2][1], 
      4*x[1][2]^3*x[2][2], x[1][2]^3*x[2][3]+3*x[1][2]^2*x[1][3]*x[2][2], 
      2*x[1][2]^2*x[1][3]*x[2][3]+2*x[1][2]*x[1][3]^2*x[2][2], 
      3*x[1][2]*x[1][3]^2*x[2][3]+x[1][3]^3*x[2][2], 4*x[1][3]^3*x[2][3] ], 
  [ 4*x[1][1]^3*x[3][1], x[1][1]^3*x[3][2]+3*x[1][1]^2*x[1][2]*x[3][1], 
      x[1][1]^3*x[3][3]+3*x[1][1]^2*x[1][3]*x[3][1], 
      2*x[1][1]^2*x[1][2]*x[3][2]+2*x[1][1]*x[1][2]^2*x[3][1], 
      x[1][1]^2*x[1][2]*x[3][3]+x[1][1]^2*x[1][3]*x[3][2]+2*x[1][1]*x[1][2]*x[\
1][3]*x[3][1], 2*x[1][1]^2*x[1][3]*x[3][3]+2*x[1][1]*x[1][3]^2*x[3][1], 
      3*x[1][1]*x[1][2]^2*x[3][2]+x[1][2]^3*x[3][1], 
      x[1][1]*x[1][2]^2*x[3][3]+2*x[1][1]*x[1][2]*x[1][3]*x[3][2]+x[1][2]^2*x[\
1][3]*x[3][1], 
      2*x[1][1]*x[1][2]*x[1][3]*x[3][3]+x[1][1]*x[1][3]^2*x[3][2]+x[1][2]*x[1]\
[3]^2*x[3][1], 3*x[1][1]*x[1][3]^2*x[3][3]+x[1][3]^3*x[3][1], 
      4*x[1][2]^3*x[3][2], x[1][2]^3*x[3][3]+3*x[1][2]^2*x[1][3]*x[3][2], 
      2*x[1][2]^2*x[1][3]*x[3][3]+2*x[1][2]*x[1][3]^2*x[3][2], 
      3*x[1][2]*x[1][3]^2*x[3][3]+x[1][3]^3*x[3][2], 4*x[1][3]^3*x[3][3] ], 
  [ 6*x[1][1]^2*x[2][1]^2, 
      3*x[1][1]^2*x[2][1]*x[2][2]+3*x[1][1]*x[1][2]*x[2][1]^2, 
      3*x[1][1]^2*x[2][1]*x[2][3]+3*x[1][1]*x[1][3]*x[2][1]^2, 
      x[1][1]^2*x[2][2]^2+4*x[1][1]*x[1][2]*x[2][1]*x[2][2]+x[1][2]^2*x[2][1]^\
2, x[1][1]^2*x[2][2]*x[2][3]+2*x[1][1]*x[1][2]*x[2][1]*x[2][3]+2*x[1][1]*x[1][\
3]*x[2][1]*x[2][2]+x[1][2]*x[1][3]*x[2][1]^2, 
      x[1][1]^2*x[2][3]^2+4*x[1][1]*x[1][3]*x[2][1]*x[2][3]+x[1][3]^2*x[2][1]^\
2, 3*x[1][1]*x[1][2]*x[2][2]^2+3*x[1][2]^2*x[2][1]*x[2][2], 
      2*x[1][1]*x[1][2]*x[2][2]*x[2][3]+x[1][1]*x[1][3]*x[2][2]^2+x[1][2]^2*x[\
2][1]*x[2][3]+2*x[1][2]*x[1][3]*x[2][1]*x[2][2], 
      x[1][1]*x[1][2]*x[2][3]^2+2*x[1][1]*x[1][3]*x[2][2]*x[2][3]+2*x[1][2]*x[\
1][3]*x[2][1]*x[2][3]+x[1][3]^2*x[2][1]*x[2][2], 
      3*x[1][1]*x[1][3]*x[2][3]^2+3*x[1][3]^2*x[2][1]*x[2][3], 
      6*x[1][2]^2*x[2][2]^2, 
      3*x[1][2]^2*x[2][2]*x[2][3]+3*x[1][2]*x[1][3]*x[2][2]^2, 
      x[1][2]^2*x[2][3]^2+4*x[1][2]*x[1][3]*x[2][2]*x[2][3]+x[1][3]^2*x[2][2]^\
2, 3*x[1][2]*x[1][3]*x[2][3]^2+3*x[1][3]^2*x[2][2]*x[2][3], 
      6*x[1][3]^2*x[2][3]^2 ], 
  [ 12*x[1][1]^2*x[2][1]*x[3][1], 
      3*x[1][1]^2*x[2][1]*x[3][2]+3*x[1][1]^2*x[2][2]*x[3][1]+6*x[1][1]*x[1][2\
]*x[2][1]*x[3][1], 
      3*x[1][1]^2*x[2][1]*x[3][3]+3*x[1][1]^2*x[2][3]*x[3][1]+6*x[1][1]*x[1][3\
]*x[2][1]*x[3][1], 
      2*x[1][1]^2*x[2][2]*x[3][2]+4*x[1][1]*x[1][2]*x[2][1]*x[3][2]+4*x[1][1]*\
x[1][2]*x[2][2]*x[3][1]+2*x[1][2]^2*x[2][1]*x[3][1], 
      x[1][1]^2*x[2][2]*x[3][3]+x[1][1]^2*x[2][3]*x[3][2]+2*x[1][1]*x[1][2]*x[\
2][1]*x[3][3]+2*x[1][1]*x[1][2]*x[2][3]*x[3][1]+2*x[1][1]*x[1][3]*x[2][1]*x[3]\
[2]+2*x[1][1]*x[1][3]*x[2][2]*x[3][1]+2*x[1][2]*x[1][3]*x[2][1]*x[3][1], 
      2*x[1][1]^2*x[2][3]*x[3][3]+4*x[1][1]*x[1][3]*x[2][1]*x[3][3]+4*x[1][1]*\
x[1][3]*x[2][3]*x[3][1]+2*x[1][3]^2*x[2][1]*x[3][1], 
      6*x[1][1]*x[1][2]*x[2][2]*x[3][2]+3*x[1][2]^2*x[2][1]*x[3][2]+3*x[1][2]^\
2*x[2][2]*x[3][1], 
      2*x[1][1]*x[1][2]*x[2][2]*x[3][3]+2*x[1][1]*x[1][2]*x[2][3]*x[3][2]+2*x[\
1][1]*x[1][3]*x[2][2]*x[3][2]+x[1][2]^2*x[2][1]*x[3][3]+x[1][2]^2*x[2][3]*x[3]\
[1]+2*x[1][2]*x[1][3]*x[2][1]*x[3][2]+2*x[1][2]*x[1][3]*x[2][2]*x[3][1], 
      2*x[1][1]*x[1][2]*x[2][3]*x[3][3]+2*x[1][1]*x[1][3]*x[2][2]*x[3][3]+2*x[\
1][1]*x[1][3]*x[2][3]*x[3][2]+2*x[1][2]*x[1][3]*x[2][1]*x[3][3]+2*x[1][2]*x[1]\
[3]*x[2][3]*x[3][1]+x[1][3]^2*x[2][1]*x[3][2]+x[1][3]^2*x[2][2]*x[3][1], 
      6*x[1][1]*x[1][3]*x[2][3]*x[3][3]+3*x[1][3]^2*x[2][1]*x[3][3]+3*x[1][3]^\
2*x[2][3]*x[3][1], 12*x[1][2]^2*x[2][2]*x[3][2], 
      3*x[1][2]^2*x[2][2]*x[3][3]+3*x[1][2]^2*x[2][3]*x[3][2]+6*x[1][2]*x[1][3\
]*x[2][2]*x[3][2], 
      2*x[1][2]^2*x[2][3]*x[3][3]+4*x[1][2]*x[1][3]*x[2][2]*x[3][3]+4*x[1][2]*\
x[1][3]*x[2][3]*x[3][2]+2*x[1][3]^2*x[2][2]*x[3][2], 
      6*x[1][2]*x[1][3]*x[2][3]*x[3][3]+3*x[1][3]^2*x[2][2]*x[3][3]+3*x[1][3]^\
2*x[2][3]*x[3][2], 12*x[1][3]^2*x[2][3]*x[3][3] ], 
  [ 6*x[1][1]^2*x[3][1]^2, 
      3*x[1][1]^2*x[3][1]*x[3][2]+3*x[1][1]*x[1][2]*x[3][1]^2, 
      3*x[1][1]^2*x[3][1]*x[3][3]+3*x[1][1]*x[1][3]*x[3][1]^2, 
      x[1][1]^2*x[3][2]^2+4*x[1][1]*x[1][2]*x[3][1]*x[3][2]+x[1][2]^2*x[3][1]^\
2, x[1][1]^2*x[3][2]*x[3][3]+2*x[1][1]*x[1][2]*x[3][1]*x[3][3]+2*x[1][1]*x[1][\
3]*x[3][1]*x[3][2]+x[1][2]*x[1][3]*x[3][1]^2, 
      x[1][1]^2*x[3][3]^2+4*x[1][1]*x[1][3]*x[3][1]*x[3][3]+x[1][3]^2*x[3][1]^\
2, 3*x[1][1]*x[1][2]*x[3][2]^2+3*x[1][2]^2*x[3][1]*x[3][2], 
      2*x[1][1]*x[1][2]*x[3][2]*x[3][3]+x[1][1]*x[1][3]*x[3][2]^2+x[1][2]^2*x[\
3][1]*x[3][3]+2*x[1][2]*x[1][3]*x[3][1]*x[3][2], 
      x[1][1]*x[1][2]*x[3][3]^2+2*x[1][1]*x[1][3]*x[3][2]*x[3][3]+2*x[1][2]*x[\
1][3]*x[3][1]*x[3][3]+x[1][3]^2*x[3][1]*x[3][2], 
      3*x[1][1]*x[1][3]*x[3][3]^2+3*x[1][3]^2*x[3][1]*x[3][3], 
      6*x[1][2]^2*x[3][2]^2, 
      3*x[1][2]^2*x[3][2]*x[3][3]+3*x[1][2]*x[1][3]*x[3][2]^2, 
      x[1][2]^2*x[3][3]^2+4*x[1][2]*x[1][3]*x[3][2]*x[3][3]+x[1][3]^2*x[3][2]^\
2, 3*x[1][2]*x[1][3]*x[3][3]^2+3*x[1][3]^2*x[3][2]*x[3][3], 
      6*x[1][3]^2*x[3][3]^2 ], 
  [ 4*x[1][1]*x[2][1]^3, 3*x[1][1]*x[2][1]^2*x[2][2]+x[1][2]*x[2][1]^3, 
      3*x[1][1]*x[2][1]^2*x[2][3]+x[1][3]*x[2][1]^3, 
      2*x[1][1]*x[2][1]*x[2][2]^2+2*x[1][2]*x[2][1]^2*x[2][2], 
      2*x[1][1]*x[2][1]*x[2][2]*x[2][3]+x[1][2]*x[2][1]^2*x[2][3]+x[1][3]*x[2]\
[1]^2*x[2][2], 2*x[1][1]*x[2][1]*x[2][3]^2+2*x[1][3]*x[2][1]^2*x[2][3], 
      x[1][1]*x[2][2]^3+3*x[1][2]*x[2][1]*x[2][2]^2, 
      x[1][1]*x[2][2]^2*x[2][3]+2*x[1][2]*x[2][1]*x[2][2]*x[2][3]+x[1][3]*x[2]\
[1]*x[2][2]^2, 
      x[1][1]*x[2][2]*x[2][3]^2+x[1][2]*x[2][1]*x[2][3]^2+2*x[1][3]*x[2][1]*x[\
2][2]*x[2][3], x[1][1]*x[2][3]^3+3*x[1][3]*x[2][1]*x[2][3]^2, 
      4*x[1][2]*x[2][2]^3, 3*x[1][2]*x[2][2]^2*x[2][3]+x[1][3]*x[2][2]^3, 
      2*x[1][2]*x[2][2]*x[2][3]^2+2*x[1][3]*x[2][2]^2*x[2][3], 
      x[1][2]*x[2][3]^3+3*x[1][3]*x[2][2]*x[2][3]^2, 4*x[1][3]*x[2][3]^3 ], 
  [ 12*x[1][1]*x[2][1]^2*x[3][1], 
      3*x[1][1]*x[2][1]^2*x[3][2]+6*x[1][1]*x[2][1]*x[2][2]*x[3][1]+3*x[1][2]*\
x[2][1]^2*x[3][1], 
      3*x[1][1]*x[2][1]^2*x[3][3]+6*x[1][1]*x[2][1]*x[2][3]*x[3][1]+3*x[1][3]*\
x[2][1]^2*x[3][1], 
      4*x[1][1]*x[2][1]*x[2][2]*x[3][2]+2*x[1][1]*x[2][2]^2*x[3][1]+2*x[1][2]*\
x[2][1]^2*x[3][2]+4*x[1][2]*x[2][1]*x[2][2]*x[3][1], 
      2*x[1][1]*x[2][1]*x[2][2]*x[3][3]+2*x[1][1]*x[2][1]*x[2][3]*x[3][2]+2*x[\
1][1]*x[2][2]*x[2][3]*x[3][1]+x[1][2]*x[2][1]^2*x[3][3]+2*x[1][2]*x[2][1]*x[2]\
[3]*x[3][1]+x[1][3]*x[2][1]^2*x[3][2]+2*x[1][3]*x[2][1]*x[2][2]*x[3][1], 
      4*x[1][1]*x[2][1]*x[2][3]*x[3][3]+2*x[1][1]*x[2][3]^2*x[3][1]+2*x[1][3]*\
x[2][1]^2*x[3][3]+4*x[1][3]*x[2][1]*x[2][3]*x[3][1], 
      3*x[1][1]*x[2][2]^2*x[3][2]+6*x[1][2]*x[2][1]*x[2][2]*x[3][2]+3*x[1][2]*\
x[2][2]^2*x[3][1], 
      x[1][1]*x[2][2]^2*x[3][3]+2*x[1][1]*x[2][2]*x[2][3]*x[3][2]+2*x[1][2]*x[\
2][1]*x[2][2]*x[3][3]+2*x[1][2]*x[2][1]*x[2][3]*x[3][2]+2*x[1][2]*x[2][2]*x[2]\
[3]*x[3][1]+2*x[1][3]*x[2][1]*x[2][2]*x[3][2]+x[1][3]*x[2][2]^2*x[3][1], 
      2*x[1][1]*x[2][2]*x[2][3]*x[3][3]+x[1][1]*x[2][3]^2*x[3][2]+2*x[1][2]*x[\
2][1]*x[2][3]*x[3][3]+x[1][2]*x[2][3]^2*x[3][1]+2*x[1][3]*x[2][1]*x[2][2]*x[3]\
[3]+2*x[1][3]*x[2][1]*x[2][3]*x[3][2]+2*x[1][3]*x[2][2]*x[2][3]*x[3][1], 
      3*x[1][1]*x[2][3]^2*x[3][3]+6*x[1][3]*x[2][1]*x[2][3]*x[3][3]+3*x[1][3]*\
x[2][3]^2*x[3][1], 12*x[1][2]*x[2][2]^2*x[3][2], 
      3*x[1][2]*x[2][2]^2*x[3][3]+6*x[1][2]*x[2][2]*x[2][3]*x[3][2]+3*x[1][3]*\
x[2][2]^2*x[3][2], 
      4*x[1][2]*x[2][2]*x[2][3]*x[3][3]+2*x[1][2]*x[2][3]^2*x[3][2]+2*x[1][3]*\
x[2][2]^2*x[3][3]+4*x[1][3]*x[2][2]*x[2][3]*x[3][2], 
      3*x[1][2]*x[2][3]^2*x[3][3]+6*x[1][3]*x[2][2]*x[2][3]*x[3][3]+3*x[1][3]*\
x[2][3]^2*x[3][2], 12*x[1][3]*x[2][3]^2*x[3][3] ], 
  [ 12*x[1][1]*x[2][1]*x[3][1]^2, 
      6*x[1][1]*x[2][1]*x[3][1]*x[3][2]+3*x[1][1]*x[2][2]*x[3][1]^2+3*x[1][2]*\
x[2][1]*x[3][1]^2, 
      6*x[1][1]*x[2][1]*x[3][1]*x[3][3]+3*x[1][1]*x[2][3]*x[3][1]^2+3*x[1][3]*\
x[2][1]*x[3][1]^2, 
      2*x[1][1]*x[2][1]*x[3][2]^2+4*x[1][1]*x[2][2]*x[3][1]*x[3][2]+4*x[1][2]*\
x[2][1]*x[3][1]*x[3][2]+2*x[1][2]*x[2][2]*x[3][1]^2, 
      2*x[1][1]*x[2][1]*x[3][2]*x[3][3]+2*x[1][1]*x[2][2]*x[3][1]*x[3][3]+2*x[\
1][1]*x[2][3]*x[3][1]*x[3][2]+2*x[1][2]*x[2][1]*x[3][1]*x[3][3]+x[1][2]*x[2][3\
]*x[3][1]^2+2*x[1][3]*x[2][1]*x[3][1]*x[3][2]+x[1][3]*x[2][2]*x[3][1]^2, 
      2*x[1][1]*x[2][1]*x[3][3]^2+4*x[1][1]*x[2][3]*x[3][1]*x[3][3]+4*x[1][3]*\
x[2][1]*x[3][1]*x[3][3]+2*x[1][3]*x[2][3]*x[3][1]^2, 
      3*x[1][1]*x[2][2]*x[3][2]^2+3*x[1][2]*x[2][1]*x[3][2]^2+6*x[1][2]*x[2][2\
]*x[3][1]*x[3][2], 
      2*x[1][1]*x[2][2]*x[3][2]*x[3][3]+x[1][1]*x[2][3]*x[3][2]^2+2*x[1][2]*x[\
2][1]*x[3][2]*x[3][3]+2*x[1][2]*x[2][2]*x[3][1]*x[3][3]+2*x[1][2]*x[2][3]*x[3]\
[1]*x[3][2]+x[1][3]*x[2][1]*x[3][2]^2+2*x[1][3]*x[2][2]*x[3][1]*x[3][2], 
      x[1][1]*x[2][2]*x[3][3]^2+2*x[1][1]*x[2][3]*x[3][2]*x[3][3]+x[1][2]*x[2]\
[1]*x[3][3]^2+2*x[1][2]*x[2][3]*x[3][1]*x[3][3]+2*x[1][3]*x[2][1]*x[3][2]*x[3]\
[3]+2*x[1][3]*x[2][2]*x[3][1]*x[3][3]+2*x[1][3]*x[2][3]*x[3][1]*x[3][2], 
      3*x[1][1]*x[2][3]*x[3][3]^2+3*x[1][3]*x[2][1]*x[3][3]^2+6*x[1][3]*x[2][3\
]*x[3][1]*x[3][3], 12*x[1][2]*x[2][2]*x[3][2]^2, 
      6*x[1][2]*x[2][2]*x[3][2]*x[3][3]+3*x[1][2]*x[2][3]*x[3][2]^2+3*x[1][3]*\
x[2][2]*x[3][2]^2, 
      2*x[1][2]*x[2][2]*x[3][3]^2+4*x[1][2]*x[2][3]*x[3][2]*x[3][3]+4*x[1][3]*\
x[2][2]*x[3][2]*x[3][3]+2*x[1][3]*x[2][3]*x[3][2]^2, 
      3*x[1][2]*x[2][3]*x[3][3]^2+3*x[1][3]*x[2][2]*x[3][3]^2+6*x[1][3]*x[2][3\
]*x[3][2]*x[3][3], 12*x[1][3]*x[2][3]*x[3][3]^2 ], 
  [ 4*x[1][1]*x[3][1]^3, 3*x[1][1]*x[3][1]^2*x[3][2]+x[1][2]*x[3][1]^3, 
      3*x[1][1]*x[3][1]^2*x[3][3]+x[1][3]*x[3][1]^3, 
      2*x[1][1]*x[3][1]*x[3][2]^2+2*x[1][2]*x[3][1]^2*x[3][2], 
      2*x[1][1]*x[3][1]*x[3][2]*x[3][3]+x[1][2]*x[3][1]^2*x[3][3]+x[1][3]*x[3]\
[1]^2*x[3][2], 2*x[1][1]*x[3][1]*x[3][3]^2+2*x[1][3]*x[3][1]^2*x[3][3], 
      x[1][1]*x[3][2]^3+3*x[1][2]*x[3][1]*x[3][2]^2, 
      x[1][1]*x[3][2]^2*x[3][3]+2*x[1][2]*x[3][1]*x[3][2]*x[3][3]+x[1][3]*x[3]\
[1]*x[3][2]^2, 
      x[1][1]*x[3][2]*x[3][3]^2+x[1][2]*x[3][1]*x[3][3]^2+2*x[1][3]*x[3][1]*x[\
3][2]*x[3][3], x[1][1]*x[3][3]^3+3*x[1][3]*x[3][1]*x[3][3]^2, 
      4*x[1][2]*x[3][2]^3, 3*x[1][2]*x[3][2]^2*x[3][3]+x[1][3]*x[3][2]^3, 
      2*x[1][2]*x[3][2]*x[3][3]^2+2*x[1][3]*x[3][2]^2*x[3][3], 
      x[1][2]*x[3][3]^3+3*x[1][3]*x[3][2]*x[3][3]^2, 4*x[1][3]*x[3][3]^3 ], 
  [ x[2][1]^4, x[2][1]^3*x[2][2], x[2][1]^3*x[2][3], x[2][1]^2*x[2][2]^2, 
      x[2][1]^2*x[2][2]*x[2][3], x[2][1]^2*x[2][3]^2, x[2][1]*x[2][2]^3, 
      x[2][1]*x[2][2]^2*x[2][3], x[2][1]*x[2][2]*x[2][3]^2, x[2][1]*x[2][3]^3,
      x[2][2]^4, x[2][2]^3*x[2][3], x[2][2]^2*x[2][3]^2, x[2][2]*x[2][3]^3, 
      x[2][3]^4 ], 
  [ 4*x[2][1]^3*x[3][1], x[2][1]^3*x[3][2]+3*x[2][1]^2*x[2][2]*x[3][1], 
      x[2][1]^3*x[3][3]+3*x[2][1]^2*x[2][3]*x[3][1], 
      2*x[2][1]^2*x[2][2]*x[3][2]+2*x[2][1]*x[2][2]^2*x[3][1], 
      x[2][1]^2*x[2][2]*x[3][3]+x[2][1]^2*x[2][3]*x[3][2]+2*x[2][1]*x[2][2]*x[\
2][3]*x[3][1], 2*x[2][1]^2*x[2][3]*x[3][3]+2*x[2][1]*x[2][3]^2*x[3][1], 
      3*x[2][1]*x[2][2]^2*x[3][2]+x[2][2]^3*x[3][1], 
      x[2][1]*x[2][2]^2*x[3][3]+2*x[2][1]*x[2][2]*x[2][3]*x[3][2]+x[2][2]^2*x[\
2][3]*x[3][1], 
      2*x[2][1]*x[2][2]*x[2][3]*x[3][3]+x[2][1]*x[2][3]^2*x[3][2]+x[2][2]*x[2]\
[3]^2*x[3][1], 3*x[2][1]*x[2][3]^2*x[3][3]+x[2][3]^3*x[3][1], 
      4*x[2][2]^3*x[3][2], x[2][2]^3*x[3][3]+3*x[2][2]^2*x[2][3]*x[3][2], 
      2*x[2][2]^2*x[2][3]*x[3][3]+2*x[2][2]*x[2][3]^2*x[3][2], 
      3*x[2][2]*x[2][3]^2*x[3][3]+x[2][3]^3*x[3][2], 4*x[2][3]^3*x[3][3] ], 
  [ 6*x[2][1]^2*x[3][1]^2, 
      3*x[2][1]^2*x[3][1]*x[3][2]+3*x[2][1]*x[2][2]*x[3][1]^2, 
      3*x[2][1]^2*x[3][1]*x[3][3]+3*x[2][1]*x[2][3]*x[3][1]^2, 
      x[2][1]^2*x[3][2]^2+4*x[2][1]*x[2][2]*x[3][1]*x[3][2]+x[2][2]^2*x[3][1]^\
2, x[2][1]^2*x[3][2]*x[3][3]+2*x[2][1]*x[2][2]*x[3][1]*x[3][3]+2*x[2][1]*x[2][\
3]*x[3][1]*x[3][2]+x[2][2]*x[2][3]*x[3][1]^2, 
      x[2][1]^2*x[3][3]^2+4*x[2][1]*x[2][3]*x[3][1]*x[3][3]+x[2][3]^2*x[3][1]^\
2, 3*x[2][1]*x[2][2]*x[3][2]^2+3*x[2][2]^2*x[3][1]*x[3][2], 
      2*x[2][1]*x[2][2]*x[3][2]*x[3][3]+x[2][1]*x[2][3]*x[3][2]^2+x[2][2]^2*x[\
3][1]*x[3][3]+2*x[2][2]*x[2][3]*x[3][1]*x[3][2], 
      x[2][1]*x[2][2]*x[3][3]^2+2*x[2][1]*x[2][3]*x[3][2]*x[3][3]+2*x[2][2]*x[\
2][3]*x[3][1]*x[3][3]+x[2][3]^2*x[3][1]*x[3][2], 
      3*x[2][1]*x[2][3]*x[3][3]^2+3*x[2][3]^2*x[3][1]*x[3][3], 
      6*x[2][2]^2*x[3][2]^2, 
      3*x[2][2]^2*x[3][2]*x[3][3]+3*x[2][2]*x[2][3]*x[3][2]^2, 
      x[2][2]^2*x[3][3]^2+4*x[2][2]*x[2][3]*x[3][2]*x[3][3]+x[2][3]^2*x[3][2]^\
2, 3*x[2][2]*x[2][3]*x[3][3]^2+3*x[2][3]^2*x[3][2]*x[3][3], 
      6*x[2][3]^2*x[3][3]^2 ], 
  [ 4*x[2][1]*x[3][1]^3, 3*x[2][1]*x[3][1]^2*x[3][2]+x[2][2]*x[3][1]^3, 
      3*x[2][1]*x[3][1]^2*x[3][3]+x[2][3]*x[3][1]^3, 
      2*x[2][1]*x[3][1]*x[3][2]^2+2*x[2][2]*x[3][1]^2*x[3][2], 
      2*x[2][1]*x[3][1]*x[3][2]*x[3][3]+x[2][2]*x[3][1]^2*x[3][3]+x[2][3]*x[3]\
[1]^2*x[3][2], 2*x[2][1]*x[3][1]*x[3][3]^2+2*x[2][3]*x[3][1]^2*x[3][3], 
      x[2][1]*x[3][2]^3+3*x[2][2]*x[3][1]*x[3][2]^2, 
      x[2][1]*x[3][2]^2*x[3][3]+2*x[2][2]*x[3][1]*x[3][2]*x[3][3]+x[2][3]*x[3]\
[1]*x[3][2]^2, 
      x[2][1]*x[3][2]*x[3][3]^2+x[2][2]*x[3][1]*x[3][3]^2+2*x[2][3]*x[3][1]*x[\
3][2]*x[3][3], x[2][1]*x[3][3]^3+3*x[2][3]*x[3][1]*x[3][3]^2, 
      4*x[2][2]*x[3][2]^3, 3*x[2][2]*x[3][2]^2*x[3][3]+x[2][3]*x[3][2]^3, 
      2*x[2][2]*x[3][2]*x[3][3]^2+2*x[2][3]*x[3][2]^2*x[3][3], 
      x[2][2]*x[3][3]^3+3*x[2][3]*x[3][2]*x[3][3]^2, 4*x[2][3]*x[3][3]^3 ], 
  [ x[3][1]^4, x[3][1]^3*x[3][2], x[3][1]^3*x[3][3], x[3][1]^2*x[3][2]^2, 
      x[3][1]^2*x[3][2]*x[3][3], x[3][1]^2*x[3][3]^2, x[3][1]*x[3][2]^3, 
      x[3][1]*x[3][2]^2*x[3][3], x[3][1]*x[3][2]*x[3][3]^2, x[3][1]*x[3][3]^3,
      x[3][2]^4, x[3][2]^3*x[3][3], x[3][2]^2*x[3][3]^2, x[3][2]*x[3][3]^3, 
      x[3][3]^4 ] ];



ConstructTensors:=function(seeds)
local f,all,pat,allmo,i,j,np,t,mo,k,cf,lim;
  lim:=ValueOption("limit");
  if lim=fail then lim:=infinity;fi;
  f:=FieldOfMatrixList(seeds[1]);
  all:=ShallowCopy(seeds);
  pat:=List([1..Length(seeds)],x->[x]);
  allmo:=List(seeds,x->GModuleByMats(x,f));
  i:=1;
  while i<=Length(all) do
    for j in [1..Length(seeds)] do
      np:=Concatenation(pat[i],[j]);
      Sort(np);
#      if np in pat then 
#	Print("duplicate ",np,"\n");
#      else
	Add(pat,np);
	t:=List([1..Length(seeds[j])],
          x->KroneckerProduct(all[i][x],seeds[j][x]));
        mo:=GModuleByMats(t,f);
	cf:=List(MTX.CollectedFactors(mo),x->x[1]);
	Sort(cf,function(a,b) return a.dimension<b.dimension;end);
	for mo in cf do
	  k:=PositionProperty([1..Length(allmo)],x->
            allmo[x].dimension=mo.dimension and MTX.Isomorphism(allmo[x],mo)<>fail);
	  if k=fail then
	    Print("new irred ",np," ",mo.dimension,"\n");
	    Add(pat,np);
	    Add(all,mo.generators);
	    Add(allmo,mo);
	    if Length(all)=lim then return all;fi;
	  #else
	  #  Print("isom ",np," ",mo.dimension," ",k,"\n");
	  fi;
	od;
#      fi;
    od;
    i:=i+1;
  od;
  
  return all;
end;

Constructsymmreps:=function(mats)
local i,l;
  l:=[ShallowCopy(mats)];
  for i in [2..4] do
    Add(l,List(mats,x->SymmetricPower(x,i)));
  od;
  return l;
end;

RepresKind:=function(mats,kind)
local n,r,f;
  n:=Int(Filtered(kind,x->x in CHARS_DIGITS));
  r:=fail;
  if Length(kind)>3 and kind{[1..3]}="Pol" then
    r:=ConstructOnePolrep(mats,n);
  elif Length(kind)>1 and kind{[1]}="S" then
    # symmetric
    r:=rec(name:=Concatenation("S",String(n)),
                   kind:="sympow",level:=n,
                   gens:=List(mats,y->SymmetricPower(y,n)));
  elif Length(kind)>1 and kind{[1]}="E" then
    # exterior
    r:=rec(name:=Concatenation("E",String(n)),
                   kind:="sympow",level:=n,
                   gens:=List(mats,y->ExteriorPower(y,n)));
  elif kind="rep15" then
    r:=rec(name:="Rep15", kind:="rep15",
                   gens:=List(mats,rep15));

  fi;
  if r=fail then
    Error("Do not know repres ",kind);
  else
    f:=FieldOfMatrixList(r.gens);
    if IsFinite(f) then
      n:=GModuleByMats(r.gens,f);
      r.absirr:=MTX.IsAbsolutelyIrreducible(n);
    fi;
    return r;
  fi;
end;

# which kinds to try in which dimension
KindsForDim:=function(n)
local kinds,i;
  kinds:=["Pol1","Pol2","Pol3"];
  if n=3 then 
    Add(kinds,"rep15");
  else 
    Append(kinds,["S2","E2"]);
  fi;
  for i in [4..n] do
    Add(kinds,Concatenation("Pol",String(i)));
  od;
  return kinds;
end;

#3: [ "Pol1", "Pol2", "Pol3", "rep15" ]
#4: [ "E2", "Pol1", "Pol2", "Pol4" ]
#5: [ "Pol1", "Pol2", "Pol3" ]
#6: [ "E2", "Pol1", "Pol2", "Pol3", "Pol4" ]
#7: [ "Pol1", "Pol2", "Pol3" ]
#8: [ "E2", "Pol1", "Pol2", "Pol3", "Pol4" ]
#9: [ "Pol1", "Pol2", "Pol3" ]
#10: [ "E2", "Pol1", "Pol2", "Pol3", "Pol4" ]
#11: [ "Pol1", "Pol2", "Pol3" ]


TestReps:=function(g,l,subs)
local i,j,r,mo,hom,is;
  is:=[1..Length(subs)];
  for i in [1..Length(l)] do
    hom:=GroupHomomorphismByImagesNC(g,Group(l[i]),GeneratorsOfGroup(g),l[i]);
    #if hom=fail then Error("UGH");fi;
    r:=[];
    for j in [1..Length(subs)] do
      mo:=List(GeneratorsOfGroup(subs[j]),x->Image(hom,x));
      mo:=GModuleByMats(mo,DefaultFieldOfMatrixGroup(g));
      if MTX.IsAbsolutelyIrreducible(mo) then
	#if Size(Group(mo.generators))>Size(subs[j]) then Error("ZZZ");fi;
	Add(r,j);
      fi;
    od;
    Print(i,":",Length(One(Range(hom)))," ",r,"\n");
    is:=Intersection(is,r);
    if Length(is)=0 then return true;fi;
  od;
  return false;
end;

IntFacTrial:=function(n)
  local f,i;
  f:=[];
  i:=1;
  while n>1 and i<=Length(Primes) do
    while n mod Primes[i]=0 do
      n:=n/Primes[i];
      AddSet(f,Primes[i]);
    od;
    i:=i+1;
  od;
  if n=1 then return f;
  else
    return fail;
  fi;
end;

RegModZSpanOrig:=function(gens,seed,oneirr,bad)
local n,matsplit,b,cnt,HM,si,new,bc,i,j,d,process,stack,max,prime;

  process:=function(new)
    bc:=Concatenation(b,[new])*oneirr;
    if Length(b)=Length(b[1]) or Length(b)+1>RankMat(bc) then
      if HM=fail then
	HM:=HermiteNormalFormIntegerMatTransform(b);
      fi;
      d:=SolutionMat(HM.normal,new);
      if d<>fail and ForAll(d,IsInt) then
	# same lattice
	cnt:=cnt+1;
	if Length(b)>=Length(b[1]) and cnt>=5 then
	  return b;
	fi;
      else
	bc:=Concatenation(b,[new]);
	if ForAll(bad,x->RankMat(bc*Z(x)^0)<=Length(b))
	  and (Length(bc)>Length(bc[1]) or RankMat(bc)<=Length(b)) then
	  # new lattice, same rank
	  cnt:=0;
	  b:=bc;
  #Print(Maximum(Union(b)),"\n");
  #b0:=b;
	  HM:=HermiteNormalFormIntegerMatTransform(b);
	  b:=Filtered(HM.normal,x->not IsZero(x));
    #if Maximum(Union(b))>10^60 then Error("huge"); fi;
	else
	  # add vector, prime was bad;
	  b:=bc;
	  #b:=LLLint(bc);
	  HM:=fail;
	  prime:=NextPrimeInt(prime);
	  oneirr:=Z(prime)^0;
	  Print("prime increased to:",prime,"\n");
	fi;
      fi;
    else
      # rank increases
      cnt:=0;
      Add(b,new);
      HM:=fail;
    fi;
  end;

  if oneirr=false then
    oneirr:=Z(101);
  fi;
  prime:=Characteristic(oneirr);

  n:=Length(gens[1]);
  matsplit:=l->List([1..n],x->l{[n*(x-1)+1..n*x]});
  b:=ShallowCopy(seed);
  max:=Maximum(Concatenation(seed));
  max:=Maximum(max,Maximum(Concatenation(Concatenation(gens))));
  cnt:=0;
  HM:=fail;
  stack:=[];
  for i in b do
    si:=matsplit(i);
    for j in gens do
      new:=Concatenation(si*j);
      if Maximum(new)>max*1000 then
	Add(stack,new);
      else
	process(new);
	max:=Maximum(max,Maximum(Concatenation(b)));
      fi;
    od;
  od;
  for i in stack do
    process(i);
  od;
  return b;
end;

InterestingPrimes:=function(H)
local f,b,i,all,primes,d,cnt,fct,basch,n,r,v,sn,j,a,homo,homoe,dold,ii,
      rad,new,irr,HM,p,cnt1,reduced,good,bad,gens,kinds,ngens;
  n:=Length(One(H));
  if n<>3 then Error("so far only dimension 3 done");fi;

  # get an irrelevant prime, to allow matrix work modulo
  # also immediately test small primes to be rid of them
  good:=[];
  bad:=[];
  irr:=ValueOption("prime");
  if irr=fail then
    irr:=1;
    repeat
      irr:=NextPrimeInt(irr); 
      HM:=List(GeneratorsOfGroup(H),x->x*Z(irr)^0);
      HM:=Group(HM);
      if not IsNaturalSL(HM) then Add(good,irr);
      elif irr=2 and n<=4  then
	# special treatment of 2 -- need to use mod 4:
	HM:=Integers mod 4;
	HM:=List(GeneratorsOfGroup(H),x->x*One(HM));
	HM:=Group(HM);
	FittingFreeLiftSetup(HM);
	if Size(HM)<Size(SL(n,Integers mod 4)) then
	  Add(good,2);
	  SetIsNaturalSL(HM,false);
	else
	  SetIsNaturalSL(HM,true);
	fi;
      else Add(bad,irr);fi;
    until IsNaturalSL(HM) and irr>7;
  fi;

  Print("irrelevant prime ",irr,"\n");

  sn:=SymmetricGroup(n);
  all:=[];
  kinds:=KindsForDim(n);
  for i in [1..Length(kinds)] do
    Print("i=",i," ",kinds[i],"\n");
    gens:=RepresKind(GeneratorsOfGroup(H),kinds[i]).gens;
    f:=EpimorphismFromFreeGroup(Group(gens));

    rad:=5;
    primes:=[];
    cnt:=0;
    dold:=0;
    reduced:=false;
    b:=[Concatenation(gens[1])];
    ngens:=ShallowCopy(gens);
    repeat
      b:=RegModZSpanOrig(gens,b,Z(irr)^0,Difference(bad,[irr]));

      d:=DeterminantMat(List(b,x->List(b,y->x*y)));

      # remove primes we know already about
      for p in Union(good,bad) do
	while d mod p=0 do
	  d:=d/p;
	od;
      od;
#Print("det=",d,"\n");
  #if d>10^40 then Error("YYY");fi;

#      if d=dold then cnt:=cnt+1;else cnt:=0;fi;
#      dold:=d;
#
#      # no new primes or stable for a while
      rad:=rad+2;
    until cnt>=10 or d<10^100;

    if d>1 then
      d:=Set(Factors(d));
      Print("->",d,"\n");
      for p in d do
	HM:=List(GeneratorsOfGroup(H),x->x*Z(p)^0);
	HM:=Group(HM);
	if not IsNaturalSL(HM) then AddSet(good,p);
	else AddSet(bad,p);fi;
      od;
      Print("good=",good," bad=",bad,"\n");
    fi;
  od;

  return good;
end;





























# old, obsolete code
AAAAAAASStabilizerGens:=function(gens,u,m)
local n,ring,one,u1,v1,gens1,orb,d,t,stabgens,stabsub,o,i,img,p,post,vo,s,gp,
  ff,actfun;

  n:=Length(u);

  ring:=Integers mod m;
  one:=One(ring);
  u1:=u*one;
  gens1:=List(gens,x->x*one);
  #gens1:=GeneratorsWithMemory(gens1);
  # do clever orbit algorithm using recognition
  gp:=Group(gens1);
  ff:=FittingFreeLiftSetup(gp);
  d:=Enumerator(ring^n);
  p:=MappingGeneratorsImages(ff.pcisom);
  o:=MappingGeneratorsImages(ff.factorhom);
  orb:=OrbitStabRepsMultistage(p[1],p[1],ff.pcisom,
    Size(Image(ff.pcisom)),TrivialSubgroup(Image(ff.pcisom)),o[1],o[1],o[2],
                 ff.factorhom,Size(gp),OnRight,d,u1);

  stabgens:=Concatenation(orb.stabradgens,orb.stabfacgens);
  stabgens:=List(stabgens,x->ASBestPreImg(x,m,gens));
  Assert(1,ForAll(stabgens,y->DeterminantMat(y)=1));

  # function for action on Gamma_m orbits, represented by ``canonical'' reps
  actfun:=function(v,a)
  local i;
    v:=v*a;
    for i in d do
      if ASOrbitGammaM(v,i,m)<>false then
	return i;
      fi;
    od;
    return v;
  end;

  orb:=OrbitStabRepsMultistage(orb.stabradgens,
	stabgens{[1..Length(orb.stabradgens)]},ff.pcisom,
    orb.stabrsubsz,TrivialSubgroup(Image(ff.pcisom)),
      orb.stabfacgens,stabgens{[Length(orb.stabradgens)+1..Length(stabgens)]},
      orb.stabfacimgs,
                 ff.factorhom,orb.subsz,actfun,false,u);

  stabgens:=Concatenation(orb.stabradgens,orb.stabfacgens);
  stabgens:=List(stabgens,x->ASBestPreImg(x,m,gens));
  Assert(1,ForAll(stabgens,y->DeterminantMat(y)=1));

  # correct stabilizing generators
  for i in [1..Length(stabgens)] do
    d:=ASOrbitGammaM(u*stabgens[i],u,m);
    stabgens[i]:=stabgens[i]*d;
  od;
  Error("ZZZ");



end;

tens:=function(rep1,rep2)
  local f,m,n,t,mo,cs;
  f:=DefaultFieldOfMatrixGroup(Range(rep1));
  m:=MappingGeneratorsImages(rep1);
  n:=MappingGeneratorsImages(rep2);
  t:=List([1..Length(m[1])],x->KroneckerProduct(m[2][x],n[2][x]));
  mo:=GModuleByMats(t,f);
  cs:=List(MTX.CollectedFactors(mo),x->x[1]);
  mo:=List(cs,x->GroupHomomorphismByImagesNC(Source(rep1),Group(x.generators),
       m[1],x.generators));
  return mo;
end;


timer:=function(range)
local m,i,l,g,t,a,primes;

  m:=[];
  for i in range do
    l:=rec(T:=i);
    g:=BetaT(i);
    g:=Group(g.1,g.2);
    t:=Runtime();
    primes:=PrimesForDense(g,b1beta(g));
    l.t1:=Runtime()-t;
    l.primes:=primes;
    t:=Runtime();
    a:=MaxPCSPrimes(g,primes);
    l.t2:=Runtime()-t;
    l.m:=a[1];
    l.idx:=a[2];
    Add(m,l);
  od;
  return m;
end;

timerrho:=function(range)
local m,i,l,g,gg,t,a,primes;

  m:=[];
  for i in range do
    l:=rec(T:=i);
    g:=RhoK(i);
    t:=Runtime();
    primes:=PrimesForDense(g,g!.unipotent);
    l.t1:=Runtime()-t;
    l.primes:=primes;
    t:=Runtime();
    a:=MaxPCSPrimes(g,primes);
    l.t2:=Runtime()-t;
    l.m:=a[1];
    l.idx:=a[2];
    gg:=Group(g.1,g.2);
    t:=Runtime();
    primes:=PrimesForDense(gg,g!.unipotent);
    l.t3:=Runtime()-t;
    l.primesF:=primes;
    t:=Runtime();
    a:=MaxPCSPrimes(gg,primes);
    l.t4:=Runtime()-t;
    l.mF:=a[1];
    l.idxF:=a[2];
    Add(m,l);
  od;
  return m;
end;

ModuleTensor:=function(a,b)
    return GModuleByMats(List([1..Length(a.generators)],x->
      KroneckerProduct(a.generators[x],b.generators[x])),a.field);
end;

BuildIrrs:=function(g)
local gens,f,reps,register,i,j,irrs;

  register:=function(mo)
  local bad;
    bad:=Filtered(irrs,x->x.dimension=mo.dimension);
    if not ForAny(bad,x->MTX.Isomorphism(x,mo)<>fail) then
      Print("new ",mo.dimension,"\n");
      Add(irrs,mo);
    else
      Print("old ",mo.dimension,"\n");
    fi;
  end;

  gens:=GeneratorsOfGroup(g);
  f:=FieldOfMatrixList(gens);
  reps:=ConstructAllPolreps(gens);
  reps:=List(reps,x->MTX.CollectedFactors(GModuleByMats(x.gens,f)));
  irrs:=[];
  Print("poldec\n");
  for i in reps do
    for j in i do
      register(j[1]);
    od;
  od;

  for i in ShallowCopy(irrs) do
    Print("symext ",Length(i.generators[1]),"\n");
    reps:=MTX.CollectedFactors(GModuleByMats(List(i.generators,x->SymmetricPower(x,2)),i.field));
    for j in reps do
      register(j[1]);
    od;
    #reps:=MTX.CollectedFactors(GModuleByMats(List(i.generators,x->ExteriorPower(x,2)),i.field));
    #for j in reps do
    #  register(j[1]);
    #od;

  od;

  return irrs;



  reps:=List(Cartesian(irrs,irrs),x->MTX.CollectedFactors(ModuleTensor(x[1],x[2])));
  for i in reps do
    for j in i do
      register(j[1]);
    od;
  od;

  return irrs;
end;

REPUSE:=[];
slmaxtest:=function(n,p)
local g,kinds,kind,f,subs,i,is,r;
  
  f:=GF(p);
  g:=SL(n,p);
  subs:=ClassicalMaximals("L",n,p);
  kinds:=KindsForDim(n);

  is:=[1..Length(subs)];
  while Length(kinds)>0 do
    kind:=kinds[1];
    kinds:=kinds{[2..Length(kinds)]};
    r:=RepresKind(GeneratorsOfGroup(g),kind);
    if r.absirr=false then
      Error("not Absolutely irreducible for g");
    fi;
    for i in ShallowCopy(is) do
      r:=RepresKind(GeneratorsOfGroup(subs[i]),kind);
      if r.absirr=false then
	AddSet(REPUSE,kind);
	RemoveSet(is,i);
	if Length(is)=0 then
	  Print(kind,": []\n");
	  return true;
	fi;
      fi;
    od;
    Print(kind,": ",is,"\n");
  od;
  Error("UGH");
  return false;
end;
  



deletethisfct:=function(g)
local n,i,j,r,mo,hom,is,f,subs,l,red,new,subpol,lbas;
  n:=Length(One(g));
  f:=FieldOfMatrixList(GeneratorsOfGroup(g));
  subs:=ClassicalMaximals("L",n,Size(f));
  is:=[1..Length(subs)];
  l:=ConstructAllPolreps(GeneratorsOfGroup(g));
  red:=Filtered(l,x->not MTX.IsAbsolutelyIrreducible(
	GModuleByMats(x.gens,f)));
  if Length(red)>0 then
    Error("notirr!");
  fi;

  subpol:=List(subs,x->ConstructAllPolreps(GeneratorsOfGroup(x)));

  new:=[];

  if Length(One(g))=3 then
    r:=rec(name:="R15",kind:="rep15",gens:=List(GeneratorsOfGroup(g),rep15));
    Add(new,r);
  fi;

  r:=List(Filtered(l,x->Length(x.gens[1])<50),
        x->rec(name:=Concatenation("S2",x.name),
                   kind:="sympow",level:=2,
                   gens:=List(x.gens,y->SymmetricPower(y,2))));
  r:=Filtered(r,x->MTX.IsAbsolutelyIrreducible(
	GModuleByMats(x.gens,f)));
  Append(new,r);
  Print("new ",List(new,x->Length(x.gens[1][1])),"\n");

  r:=List(Filtered(l,x->Length(x.gens[1])<50),
      x->rec(name:=Concatenation("E2",x.name),
                   kind:="extpow",level:=2,
                   gens:=List(x.gens,y->ExteriorPower(y,2))));
  r:=Filtered(r,x->MTX.IsAbsolutelyIrreducible(
	GModuleByMats(x.gens,f)));
  Append(new,r);
  Print("new ",List(new,x->Length(x.gens[1][1])),"\n");

#  r:=List(l,x->List(x,y->SymmetricPower(y,3)));
#  r:=Filtered(r,x->MTX.IsAbsolutelyIrreducible(
#	GModuleByMats(x,f)));
#  Append(new,r);
#  Print("new ",List(new,x->Length(x[1][1])),"\n");
#  Print("new ",List(new,x->Length(x[1][1])),"\n");
#  r:=List(l,x->List(x,y->ExteriorPower(y,3)));
#  r:=Filtered(r,x->MTX.IsAbsolutelyIrreducible(
#	GModuleByMats(x,f)));
#  Append(new,r);
#  Print("new ",List(new,x->Length(x[1][1])),"\n");

  Append(l,new);
  
  Add(l,"e3"); 

  i:=1;
  while i<=Length(l) do

    hom:=0;

    if l[i]="e3" then
      r:=List(lbas,x->rec(name:=Concatenation("E3",x.name),
		      kind:="extpow",level:=2,
		      gens:=List(x.gens,y->ExteriorPower(y,3))));
      r:=Filtered(r,x->MTX.IsAbsolutelyIrreducible(
	    GModuleByMats(x.gens,f)));
      Print("newe3 ",List(r,x->Length(x.gens[1][1])),"\n");
      l:=Concatenation(l{[1..i-1]},r,l{[i+1..Length(l)]});
    fi;

    r:=[];
    for j in [1..Length(subs)] do
      if IsBound(l[i].kind) and l[i].kind="polrep" then
	mo:=subpol[j][i].gens;
      elif IsBound(l[i].kind) and l[i].kind="sympow" then
	mo:=List(GeneratorsOfGroup(subs[j]),x->SymmetricPower(x,l[i].level));
      elif IsBound(l[i].kind) and l[i].kind="extpow" then
	mo:=List(GeneratorsOfGroup(subs[j]),x->ExteriorPower(x,l[i].level));
      elif IsBound(l[i].kind) and l[i].kind="rep15" then
	mo:=List(GeneratorsOfGroup(subs[j]),rep15);
      else
	if hom=0 then
	  hom:=GroupHomomorphismByImagesNC(g,Group(l[i].gens),GeneratorsOfGroup(g),l[i].gens);
	  #if hom=fail then Error("UGH");fi;
	fi;

	mo:=List(GeneratorsOfGroup(subs[j]),x->Image(hom,x));
      fi;
      mo:=GModuleByMats(mo,DefaultFieldOfMatrixGroup(g));
      if MTX.IsAbsolutelyIrreducible(mo) then
	#if Size(Group(mo.generators))>Size(subs[j]) then Error("ZZZ");fi;
	Add(r,j);
      fi;
    od;
    Print(i,":",l[i].name,"  ",Length(l[i].gens[1])," ",r,"\n");
    is:=Intersection(is,r);
    if Length(is)=0 then return true;fi;
    i:=i+1;
  od;
  Error(is);
  return false;
end;

slmaxtestold:=function(g)
local f,reps,red,need,m,i;
  f:=FieldOfMatrixList(GeneratorsOfGroup(g));
  reps:=ConstructAllPolreps(GeneratorsOfGroup(g));
  red:=Filtered(reps,x->not MTX.IsAbsolutelyIrreducible(
	GModuleByMats(x,f)));
  if Length(red)>0 then
    Error("notirr!");
  fi;
  need:=[];
  m:=ClassicalMaximals("L",Length(One(g)),Size(f));
  for i in m do
    reps:=ConstructAllPolreps(GeneratorsOfGroup(i));
    red:=Filtered([1..Length(reps)],x->not MTX.IsAbsolutelyIrreducible(
	  GModuleByMats(reps[x],f)));
    if Length(red)=0 then
      Error("uhuhu");
    fi;
    Add(need,red);
  od;
  return need;
end;

DATA:=[];

ExampleData:=function(gp,id,primes,type)
local t0,t1,m,a;
  if IsFunction(primes) then
    primes:=primes(gp);
  fi;
  t0:=Runtime();
  if IsBool(primes) then
    primes:=InterestingPrimes(gp,type);
  elif IsMatrix(primes) then
    primes:=PrimesForDense(gp,primes,type);
  fi;
  t0:=Runtime()-t0;
  t0:=Int(t0/100+50)*100;
  t1:=Runtime();
  m:=MaxPCSPrimes(gp,primes,type);
  t1:=Runtime()-t1;
  t1:=Int(t1/100+50)*100;
  m:=rec(name:=String(id),primes:=primes,lev:=String(m[1]),index:=String(m[2]),tprim:=t0,tmax:=t1);
  a:=First(DATA,x->x.name=m.name and Int(x.lev)=Int(m.lev) and
      Int(x.index)=Int(m.index));
  if a=fail then
    Add(DATA,m);
  elif a.tmax*13/10<m.tmax or a.tprim*13/10<m.tprim then
    Print("better!\n");
    DATA:=Filtered(DATA,x->x<>a);
    Add(DATA,m);
  else
    Print("not better!\n");
  fi;
  return m;
end;

MatTensorProduct:=function(G,H)
  local gens,i;
  gens:=[];
  for i in GeneratorsOfGroup(G) do
    Add(gens,KroneckerProduct(i,One(H)));
  od;
  for i in GeneratorsOfGroup(H) do
    Add(gens,KroneckerProduct(One(G),i));
  od;
  return Group(gens);
end;

hsed:=[[1,3],[1,2],[2,3],[3,4],[4,4],[6,5],[9,6],[5,5],[2,4],[1,4],[16,8],[12,7],[8,6],[4,5]];

UpperTriangular:=function(n)
local hom,G;
  hom:=SLNZFP(n);
  G:=GeneratorsOfGroup(Range(hom));
  G:=Filtered(G,x->ForAll([1..Length(x)],i->ForAll([1..i-1],j->IsZero(x[i][j]))));
  return Group(G);
end;

FurtherExperiment:=Group(
[[0,0,0,0,0,-1],[1,0,0,0,0,0],[0,1,0,0,0,0],[1,1,1,0,0,-1],[0,0,0,1,0,-1],[0,0,0,0,1,-1]],
[[0,0,0,0,0,-1],[1,0,0,0,0,0],[0,1,0,0,0,0],[15,-6,1,0,0,20],[0,0,0,1,0,-15],[0,0,0,0,1,6]]);

Experiment2:=function(t)
  return Group([[0,0,1],[1,0,0],[0,1,0]]*t^0,[[1,2-t+t^2,3+t^2],
  [0,-2+2*t-t^2,-1+t-t^2],[0,3-3*t+t^2,(-1+t)^2]]*t^0);
end;

FQStructure:=function(g)
local result,m,ff,primes,lastsize,sz,lamo,newmo,max,lev,p,h,str,i,gens,gp,
  psel,a,piso,fs,cs,dep;
  result:=[];
  m:=Size(DefaultRing(One(g)[1][1]));
  primes:=Set(Factors(m));
  ff:=FittingFreeLiftSetup(g);

  h:=g;
  lastsize:=Size(g);
  lamo:=m;
  # module part
  max:=Maximum(List(Collected(Factors(m)),x->x[2]));
  for lev in [max,max-1..2] do
    for p in primes do
      if m mod p^lev=0 then # p^lev occurs
        newmo:=lamo/p;
#        h:=MatrGrpModulo(g,newmo);
        FittingFreeLiftSetup(h);
        sz:=lastsize/Size(h);
        sz:=Factors(sz);
        if Length(Set(sz))<>1 then Error("sz");fi;
        if Length(sz)>1 then
          str:=Concatenation(String(sz[1]),"^",String(Length(sz)));
        else
          str:=String(sz[1]);
        fi;
        a:=Concatenation(String(p),"^",String(lev));
        Add(result,[str,a]);
        lamo:=newmo;
        lastsize:=Size(h);
      fi;
    od;
  od;
  if lamo<>Product(primes) then Error("primes");fi;
  ff:=FittingFreeLiftSetup(h);

  dep:=[Length(ff.pcgs)+1];
  h:=Length(ff.pcgs)+1;
  i:=Length(ff.pcgs);
  while i>0 do
    while i>0 
      and DepthOfPcElement(ff.pcgs,ff.pcgs[i]^RelativeOrders(ff.pcgs)[i])>=h 
      and ForAll([h-1,h-2..i],
        x->DepthOfPcElement(ff.pcgs,Comm(ff.pcgs[x],ff.pcgs[i]))>=h) do
      i:=i-1;
    od;
    Add(dep,i+1);
    h:=i+1;
  od;

  # Step through chief series of Rad(h)
  for i in [Length(ff.depths)-1,Length(ff.depths)-2..1] do
    gens:=ff.pcgs{[ff.depths[i]..ff.depths[i+1]-1]};
    gp:=Group(gens);
    if Length(gens)>1 then
      str:=Concatenation(String(RelativeOrders(ff.pcgs)[ff.depths[i]]),"^",
            String(Length(gens)));
    else
      str:=String(RelativeOrders(ff.pcgs)[ff.depths[i]]);
    fi;
    #psel:=Filtered(primes,x->Size(MatrGrpModulo(gp,x))>1); 
    psel:=[];
    for p in primes do
#      a:=MatrGrpModulo(gp,p);
      if ForAny(GeneratorsOfGroup(a),x->not IsOne(x)) then
        FittingFreeLiftSetup(a);
      fi;
      if Size(a)>1 then Add(psel,p);fi;
    od;
    psel:=Filtered(String(psel),x->x=',' or x in CHARS_DIGITS);
    Add(result,[str,psel]);
  od;

  # and now of radical factor
  cs:=ChiefSeries(Image(ff.factorhom));
  cs:=List(cs,x->PreImage(ff.factorhom,x));
  cs:=Reversed(cs);
  sz:=[];
  for p in primes do
#    a:=MatrGrpModulo(ff.radical,p);
    if ForAny(GeneratorsOfGroup(a),x->not IsOne(x)) then
      FittingFreeLiftSetup(a);
    fi;
    Add(sz,Size(a));
  od;
  for lev in [2..Length(cs)] do
    psel:=[];
    lamo:=false;
    for p in [1..Length(primes)] do
#      a:=MatrGrpModulo(cs[lev],primes[p]);
      if ForAny(GeneratorsOfGroup(a),x->not IsOne(x)) then
        ff:=FittingFreeLiftSetup(a);
      fi;

      if Size(a)>sz[p] then
        fs:=Size(a)/sz[p];
        sz[p]:=Size(a);
        Add(psel,primes[p]);
        if lamo=false then
          if Length(Set(Factors(fs)))>1 then
            piso:=ff.factorhom; # that's where the nonsolvable happens
          else
            piso:=IsomorphismPermGroup(a);
          fi;
#          lamo:=NaturalHomomorphismByNormalSubgroupNC(Image(piso),
#                  Group(List(GeneratorsOfGroup(MatrGrpModulo(cs[lev-1],primes[p])),
#                       x->ImagesRepresentative(piso,x))));

                  #Image(piso,MatrGrpModulo(cs[lev-1],primes[p])));
          lamo:=Image(lamo);
        fi;
      fi;
    od;
    if IsAbelian(lamo) then
      str:=String(Size(lamo));
    else
      str:=DataAboutSimpleGroup(lamo).tomName;
    fi;
    psel:=Filtered(String(psel),x->x=',' or x in CHARS_DIGITS);
    Add(result,[str,psel]);
  od;
  Print(result,"\n");
  str:="";
  i:=1;
  while i<=Length(result) do
    a:=i;
    while i<Length(result) and result[a][2]=result[i+1][2] do
      i:=i+1;
    od;
    Print([a..i],"\n");
    # now range a to i
    if Length(str)>0 then Add(str,'.'); fi;
    Append(str,"\\ppqf{");
    for p in [a..i] do
      if result[p][1]<>"1" then
        if p>a then Add(str,'.'); fi;
        Append(str,result[p][1]);
      fi;
    od;
    Append(str,Concatenation("}{",result[i][2],"}"));
    i:=i+1;
  od;

  return str;
end;

ImageRhoTP:=function(g,t,p)
local a;
  a:=RhoK(t);
#  a:=MatrGrpModulo(a,p);
  return GroupHomomorphismByImagesNC(g,a,
    GeneratorsOfGroup(g),GeneratorsOfGroup(a));
end;

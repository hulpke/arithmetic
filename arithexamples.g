RhoKGamma:=RhoK;

RhoKF:=function(k)
local g;
  g:=RhoK(k);
  return Group(GeneratorsOfGroup(g){[1,2]});
end;

ExampleL1:=function(t)
  return Group([[0,0,1],[1,0,0],[0,1,0]]*t^0,[[1,2-t+t^2,3+t^2],
  [0,-2+2*t-t^2,-1+t-t^2],[0,3-3*t+t^2,(-1+t)^2]]*t^0);
end;

ExampleL2:=function(t)
  return Group(
    [[1,4+3*t^2/4,3*(6-t+t^2)/2],[0,-(4+t+t^2)/2,-3-t^2],
    [0,(4+2*t+t^2)/4,(2+t+t^2)/2]]*t^0,
    [[0,0,1],[1,0,-1],[0,1,1]]);
end;

ExampleL3:=function(k)
  return Group(
    [[1,0,-3-2*k-8*k^2,-1+10*k+32*k^3,-5-16*k^2],
     [0,4*(-1+k),-13-4*k,3+16*(1+k)^2,-4+16*k],
     [0,1-k+4*k^2,3-2*k+8*k^2,-2*(1+3*k+16*k^3),3+16*k^2],
     [0,k,2*k,1-2*k-8*k^2,1+4*k],
     [0,0,3*k,3*(-1+k-4*k^2),-2]]*k^0,
    [[0,0,-3-2*k-8*k^2,-1+10*k+32*k^3,-5-16*k^2],
     [0,1,3+4*k,-13-8*k-16*k^2,4-16*k],
     [0,0,-2*(1+k+4*k^2),6*k+32*k^3,-3-16*k^2],
     [1,0,-2*(1+k),-1+2*k+8*k^2,-1-4*k],
     [2*k,0,1-2*k,-4*k,1]]*k^0);
end;

ExampleLT:=function(k)
  return Group([[k*(3-4*k+4*k^2),-1-4*k-8*k^2+16*k^3-16*k^4,0,0],
    [1-k+k^2,-1-3*k+4*k^2-4*k^3,0,0],
    [k*(1-2*k+2*k^2),-3-4*k-2*k^2+8*k^3-8*k^4,1,0],
    [2*(1-k+k^2),-2*(1+2*k-4*k^2+4*k^3),0,1]],
    [[1,0,-4,0],[0,1,0,-1],[0,0,-1,-1],[0,0,1,0]]);
end;

ExampleRandom:=function(dim,num)
local a,l,i;
  l:=[];
  for i in [1..num] do
    a:=RandomUnimodularMat(dim);
    if DeterminantMat(a)=-1 then a[1]:=-a[1];fi;
    Add(l,a);
  od;
  return Group(l);
end;

TwoGeneratorSLNZ:=function(n)
local a,b;
  a:=IdentityMat(n);
  a[1][2]:=1;
  b:=NullMat(n,n);
  b{[1..n-1]}{[2..n]}:=IdentityMat(n-1);
  b[n][1]:=(-1)^(n-1);
  return Group(a,b);
end;

KroneckerGenlists:=function(g,h)
local mats,i,m,o;
  mats:=[];
  o:=One(h[1]);
  for i in g do
    m:=KroneckerProduct(i,o);
    Add(mats,m);
  od;
  o:=One(g[1]);
  for i in h do
    m:=KroneckerProduct(o,i);
    Add(mats,m);
  od;
  return mats;
end;

KroneckerPlus:=function(a,b,m)
local e,g;
  e:=IdentityMat(a*b);
  e[1][a+1]:=m;
  g:=Concatenation(KroneckerGenlists(
    GeneratorsOfGroup(TwoGeneratorSLNZ(a)),GeneratorsOfGroup(TwoGeneratorSLNZ(b))),[e]);
  return Group(g);
end;

KronDual:=function(a,b,m,n)
local g,h,mats,rev;
  g:=List(GeneratorsOfGroup(Image(SLNZFP(a))),x->x^m);
  h:=List(GeneratorsOfGroup(Image(SLNZFP(b))),x->x^m);
  mats:=KroneckerGenlists(g,h);
  g:=List(GeneratorsOfGroup(Image(SLNZFP(b))),x->x^n);
  h:=List(GeneratorsOfGroup(Image(SLNZFP(a))),x->x^n);
  mats:=Concatenation(mats,List(KroneckerGenlists(g,h)));
  Add(mats,rev);
  return Group(mats);
end;

Companiero:=function(arg)
local g;
  g:=List(arg,CompanionMat);
  g:=Group(g);
  return g;
end;

CompanionBlock:=function(pol1,pol2,pol3)
local g,d1,d2,frax,h,i,j,p;
  d1:=DegreeOfUnivariateLaurentPolynomial(pol1);
  d2:=DegreeOfUnivariateLaurentPolynomial(pol2);
  g:=IdentityMat(d1,1);
  g{[1..d2]}{[1..d2]}:=CompanionMat(pol2);
  g{[d2+1..d1]}{[d2+1..d1]}:=CompanionMat(pol3);
  g:=Group(CompanionMat(pol1),g);
  return g;
end;

FormConjugator:=function(f2)
local factor,l,form,mo,gf,c,frax,i,j,p,h;

  factor:=ValueOption("factor");
  if factor=fail then
    factor:=1;
  else
    Info(InfoArithSub,1,"Form using factor ",factor);
  fi;
  l:=Length(f2)/2;
  form:=NullMat(2*l,2*l);
  form{[1..l]}{l+[1..l]}:=IdentityMat(l,Rationals);
  form{l+[1..l]}{[1..l]}:=-IdentityMat(l,Rationals);
  # now conjugate forms
  mo:=50000*RootInt(factor+1,2);
  #repeat
    mo:=NextPrimeInt(mo);
  #until mo mod congr=1;
  gf:=GF(mo);
  c:=LeftQuotient(
      BaseChangeToCanonical(BilinearFormByMatrix(form*One(gf),gf)),
      BaseChangeToCanonical(BilinearFormByMatrix(f2*One(gf),gf)));
  c:=TransposedMat(c);
  if TransposedMat(c)*f2*One(gf)*c<>form*One(gf) then
    Print("bad c\n");
  fi;
  c:=List(c,x->List(x,Int));

  # reconstruct fractions
  frax:=[1..30*factor];;
  frax:=Concatenation(-frax,frax);
  frax:=Set(List(Cartesian([-500*factor..500*factor],frax),x->x[1]/x[2]));
  frax:=List(frax,x->[Int(NumeratorRat(x)*One(gf)/DenominatorRat(x)),x]);
  h:=QuoInt(mo,2);
  for i in c do
    for j in [1..2*l] do
      p:=First(frax,x->x[1]=i[j]);
      if p=fail then
        return FormConjugator(f2:factor:=2*factor);
      fi;
      i[j]:=p[2];
    od;
  od;
  if TransposedMat(c)*f2*c<>form then
    Print("wrongc!\n");
    return FormConjugator(f2:factor:=2*factor);
  fi;
  # if a preserved F, cac^-1 preserves c^T Fc
  return c;
end;

# a different form of companion matrix for reciprocal polynomials that can
# be found in the russian literature
# Version 2, 2018
ComradeMatrix:=function(pol)
local c,mat,i,deg,degh;
  c:=CoefficientsOfUnivariateLaurentPolynomial(pol);
  c:=ShiftedCoeffs(c[1],c[2]);
  deg:=Length(c)-1;
  if not IsEvenInt(deg) then Error("must be even degree");fi;
  degh:=deg/2;
  mat:=NullMat(deg,deg);
  mat{[2..deg]}{[1..deg-1]}:=IdentityMat(deg-1,Rationals);
  for i in [1..degh] do
    mat[degh+1][degh+1-i]:=c[i];
    mat[deg+1-i][deg]:=-c[i+1];
  od;
  mat[1][deg]:=-1;
  return mat;
end;

LoadPackage("forms");

# basis for form space
BasisFormSpace:=function(mats)
local f;
  f:=Rationals;
  if One(mats[1])[1][1]<>1 then
    f:=DefaultFieldOfMatrix(mats[1]);
  fi;
  return SMTX.BasisModuleHomomorphisms(
    GModuleByMats(List(mats,x->TransposedMat(x)^-1),f),
    GModuleByMats(mats,f));
end;

MonodromyExample:=function(a,b,congr)
local a0,b0,l,c,form,f2,bas,mo,gf,i,j,h,frax,p;
  a0:=CompanionMat(a);
  b0:=CompanionMat(b);


  #a:=ComradeMatrix(a);
  #b:=ComradeMatrix(b);
  a:=CompanionMat(a);
  b:=CompanionMat(b);
  bas:=BasisFormSpace([a,b]);
  if Length(bas)=1 then
    f2:=bas[1];
    f2:=f2*Lcm(List(Flat(f2),DenominatorRat));
  else
    Error("choice");
  fi;
  l:=Length(a)/2;
  form:=NullMat(2*l,2*l);
  form{[1..l]}{l+[1..l]}:=IdentityMat(l,Rationals);
  form{l+[1..l]}{[1..l]}:=-IdentityMat(l,Rationals);

  # now conjugate forms
  mo:=50000;
  repeat
    mo:=NextPrimeInt(mo);
  until mo mod congr=1;
  gf:=GF(mo);
  c:=LeftQuotient(
      BaseChangeToCanonical(BilinearFormByMatrix(form*One(gf),gf)),
      BaseChangeToCanonical(BilinearFormByMatrix(f2*One(gf),gf)));
  c:=TransposedMat(c);
  c:=List(c,x->List(x,Int));

  # reconstruct fractions
  frax:=[1..30];;
  frax:=Concatenation(-frax,frax);
  frax:=Set(List(Cartesian([-500..500],frax),x->x[1]/x[2]));
  frax:=List(frax,x->[Int(NumeratorRat(x)*One(gf)/DenominatorRat(x)),x]);
  h:=QuoInt(mo,2);
  for i in c do
    for j in [1..2*l] do
      p:=First(frax,x->x[1]=i[j]);
      if p=fail then Error("frac!");fi;
      i[j]:=p[2];
    od;
  od;
  if TransposedMat(c)*f2*c<>form then Error("wrongc");fi;

  Error("ZZZ");
  a:=a^c;b:=b^c;
  return Group(a,b);

  #c:=Concatenation([l+1..2*l],[1..l]);
  #c:=PermutationMat(PermList(c),2*l);

  #f2:=KroneckerProduct(IdentityMat(l),[[0,1],[-1,0]]);
end;

GaloisImagePol:=function(aut,pol)
local e,i;
  e:=ShallowCopy(ExtRepPolynomialRatFun(pol));
  for i in [2,4..Length(e)] do
    e[i]:=ImagesRepresentative(aut,e[i]);
  od;
  return PolynomialByExtRep(FamilyObj(pol),e);
end;

MonodromyExampleFancy:=function(field,a,b)
local a0,b0,a1,b1,a2,r,s,sp,l,c,form,f2,bas,mo,gf,i,j,h,frax,p,den,eqs,gb,
  amul,deni,vars,specialize,cancel,ro,gal,cinv,vals,cleanterm,bafi,sel,e;

  bafi:=function(x)
    if not IsCyclotomic(x) then
      Error("ZYK");
    fi;
    return x;
  end;

  cancel:=function(rf)
  local num,den,gcd;
    if not IsRationalFunction(rf) then return rf;fi;
    num:=NumeratorOfRationalFunction(rf);
    den:=DenominatorOfRationalFunction(rf);
    if IsOne(den) then return num;fi;
    gcd:=Gcd(num,den);
    num:=num/gcd;
    den:=den/gcd;
    return num/den;
  end;

  # divide off variables (that will be specialized to nonzero values)
  cleanterm:=function(pol)
  local e,t,i;
    e:=ExtRepPolynomialRatFun(pol);
    t:=[];
    for i in [1,3..Length(e)-1] do
      Add(t,PolynomialByExtRep(FamilyObj(pol),
              [e[i],1]));
    od;
    t:=Gcd(t);
    if not IsOne(t) then
      return pol/t;
    else
      return pol;
    fi;
  end;

  specialize:=function(var,val)
    den:=Value(den,[var],[val]);
    eqs:=List(eqs,x->Value(x,[var],[val]));
    gb:=List(gb,x->Value(x,[var],[val]));
    a2:=List(a2,r->List(r,x->Value(NumeratorOfRationalFunction(x),[var],[val])/
	    Value(DenominatorOfRationalFunction(x),[var],[val])));
    #eqs:=Filtered(List(eqs,cancel),x->not IsZero(x));
    #gb:=Filtered(List(gb,cancel),x->not IsZero(x));
    #a2:=List(a2,r->List(r,cancel));
    Unbind(vars[Position(vars,var)]);
  end;

  a0:=CompanionMat(a);
  b0:=CompanionMat(b);

  r:=Length(a0)/2;
  if IsEvenInt(r) then
    p:=();
    for i in [2,4..r] do
      p:=p*(i,r+i-1);
    od;
  else
    p:=[];
    for i in [2,4..r+1] do
      Add(p,i);
    od;
    for i in [2*r-1,2*r-3..3] do
      Add(p,i);
    od;
    p:=MappingPermListList(p,Concatenation(p{[2..Length(p)]},p{[1]}));
   # p:=MappingPermListList([r+1,r+3..2*r],Concatenation([r+3,r+5..2*r],[r+1]));;
   # for i in [r-1,r-2..2] do
   #   p:=(i,r+i-1)*p;
   # od;
   # for i in [r+2..2*r-1] do
   #   p:=p*(i,i+1);
   # od;
  fi;
  p:=PermutationMat(p,Length(a0));
  b1:=ComradeMatrix(b)^p;
  s:=RationalCanonicalFormTransform(b1); # conjugates b1 to b0

  # generic centralizer of diagonal with different eigenvals, Galois-fixed

  ro:=RootsOfUPol(field,b);
  gal:=GaloisGroup(field);
  ro:=Orbits(gal,ro);

  # sp conjugates diagonal to b1
  #sp:=Concatenation(List(ro,x->NullspaceMat(b1-x*b1^0)));
  sp:=[];
  vals:=[];

  bas:=BasisVectors(Basis(field));
  r:=PolynomialRing(field,Maximum(Length(b1),Length(bas)*Length(ro)));

  for j in [1..Length(ro)] do
    vars:=IndeterminatesOfPolynomialRing(r){[1..Length(bas)]+Length(bas)*(j-1)};
    vars:=vars*bas;
    Add(vals,vars);
    Append(sp,NullspaceMat(b1-ro[j][1]*b1^0));
    for i in ro[j]{[2..Length(ro[j])]} do
      Append(sp,NullspaceMat(b1-i*b1^0));
      Add(vals,GaloisImagePol(RepresentativeAction(gal,ro[j][1],i),vars));

    od;
  od;

  vars:=IndeterminatesOfPolynomialRing(r){[1..Length(b1)]};
  c:=DiagonalMat(vars);
  cinv:=Inverse(c);

  # of b1
  c:=sp^-1*c*sp;
  cinv:=sp^-1*cinv*sp;
  a1:=s*a0/s;
  a2:=cinv*a1*c;

Error("KKK");

  # now get proper Values
  den:=Lcm(List(Flat(a2),DenominatorOfRationalFunction));
  a2:=a2*den;

  bas:=BasisFormSpace([ComradeMatrix(a)^p,b1])[1]; # the form we want
  eqs:=TransposedMat(a2)*bas*a2-den^2*bas;
  eqs:=Set(Flat(eqs));
  eqs:=Filtered(eqs,x->not IsZero(x));
  #den:=Lcm(List(eqs,DenominatorOfRationalFunction));
  #eqs:=eqs*den;
  ## dummy variable
  #Add(eqs,den*vars[Length(b1)+1]-1);

  eqs:=List(eqs,cleanterm);
  gb:=ReducedGrobnerBasis(eqs,MonomialLexOrdering());
  gb:=Set(List(gb,cleanterm));
  gb:=ReducedGrobnerBasis(gb,MonomialLexOrdering());

  # replace back
  den:=Value(den,vars{[1..Length(vals)]},vals);
  a2:=List(a2,r->List(r,x->Value(x,vars{[1..Length(vals)]},vals)));
  c:=List(c,r->List(r,x->Value(x,vars{[1..Length(vals)]},vals)));
  gb:=List(gb,x->Value(x,vars{[1..Length(vals)]},vals));
  gb:=ReducedGrobnerBasis(gb,MonomialLexOrdering());
  SortBy(gb,x->Length(ExtRepPolynomialRatFun(x)));
  Error("ZE");

  # conditions: Denominator 1, stabilize form
  sel:=Tuples([-2..2],Length(vals));;
  sel:=Filtered(sel,x->
    ForAll(gb,z->IsZero(Value(z,vars{[1..Length(vals)]},x)))
    and
    IsOne(Value(den,vars{[1..Length(vals)]},x))
   );
  return List(sel,z->[
    s^(-1)*List(c,r->List(r,x->bafi(Value(x,vars{[1..Length(vals)]},z)))),
    List(a2,r->List(r,x->bafi(Value(x,vars{[1..Length(vals)]},z)))),
    b1]);



  #den:=Value(den,vars{[1..6]},vals);
  #a2:=List(a2,r->List(r,x->Value(x,vars{[1..6]},vals)));

  # now specialize variables to make rational
  bas:=BasisVectors(Basis(field));
  p:=[];
  for i in [1..Length(vars)] do
    for j in [1..Length(bas)] do
      Add(p,Concatenation("y",String(i),String(j)));
    od;
  od;
  r:=PolynomialRing(field,p);
  c:=IndeterminatesOfPolynomialRing(r);
  p:=[];
  for i in [1..Length(vars)] do
    e:=0;
    for j in [1..Length(bas)] do
      e:=e+bas[j]*c[(i-1)*Length(bas)+j];
    od;
    p[i]:=e;
  od;

  den:=Lcm(List(Flat(a2),DenominatorOfRationalFunction));
  amul:=a2*den;
  den:=Value(den,vars{[1..Length(p)]},p);
  amul:=List(amul,r->List(r,x->Value(x,vars{[1..Length(p)]},p)));

  Error("YY");


  eqs:=[];
  deni:=GaloisImagePol(p,den);
  if den<>deni then Error("DENO!"); fi;
  # Galois-fixed
  for p in GeneratorsOfGroup(GaloisGroup(field)) do
    h:=[];
    for i in [1..Length(amul)] do
      h[i]:=[];
      for j in [1..Length(amul[1])] do
        h[i][j]:=NumeratorOfRationalFunction(GaloisImagePol(p,amul[i][j]));
      od;
    od;
    Append(eqs,Flat(amul-h)); # galois-fixed condition
  od;

  Error("XX");





  a1:=ComradeMatrix(a);

  r:=RootsOfUPol(field,a);

  for i in Set(r) do
    Add(sp,[i,NullspaceMat(a0-i*a0^0),NullspaceMat(a1-i*a1^0)]);
  od;


  Error("ZZZ");




  #a:=CompanionMat(a);
  #b:=CompanionMat(b);
  bas:=BasisFormSpace([a,b]);
  if Length(bas)=1 then
    f2:=bas[1];
    f2:=f2*Lcm(List(Flat(f2),DenominatorRat));
  else
    Error("choice");
  fi;
  l:=Length(a)/2;
  form:=NullMat(2*l,2*l);
  form{[1..l]}{l+[1..l]}:=IdentityMat(l,Rationals);
  form{l+[1..l]}{[1..l]}:=-IdentityMat(l,Rationals);

  # now conjugate forms
  mo:=NextPrimeInt(50000);
  gf:=GF(mo);
  c:=LeftQuotient(
      BaseChangeToCanonical(BilinearFormByMatrix(form*One(gf),gf)),
      BaseChangeToCanonical(BilinearFormByMatrix(f2*One(gf),gf)));
  c:=List(c,x->List(x,Int));

  # reconstruct fractions
  frax:=[1..30];;
  frax:=Concatenation(-frax,frax);
  frax:=Set(List(Cartesian([-200..200],frax),x->x[1]/x[2]));
  frax:=List(frax,x->[Int(NumeratorRat(x)*One(gf)/DenominatorRat(x)),x]);
  h:=QuoInt(mo,2);
  for i in c do
    for j in [1..2*l] do
      p:=First(frax,x->x[1]=i[j]);
      if p=fail then Error("frac!");fi;
      i[j]:=p[2];
    od;
  od;
  if c*f2*TransposedMat(c)<>form then Error("wrongc");fi;
  #Error("ZZZ");
  c:=TransposedMat(c);
  a:=a^c;b:=b^c;
  return Group(a,b);

  #c:=Concatenation([l+1..2*l],[1..l]);
  #c:=PermutationMat(PermList(c),2*l);

  #f2:=KroneckerProduct(IdentityMat(l),[[0,1],[-1,0]]);
end;

VonDyckGroup:=function(p,q,r)
local f;
  f:=FreeGroup("a","b");
  return f/[f.1^p,f.2^q,(f.1*f.2)^r];
end;

AdjointSubSL:=function(h)
local adj,mo,a,b,v,sub;
  adj:=ConstructAdjointRep(h,SL);
  mo:=GModuleByMats(adj[1],FieldOfMatrixGroup(h));
  repeat
    a:=PseudoRandom(h);b:=PseudoRandom(h);
    v:=a*b-b*a;
  until not IsZero(v);
  sub:=MTX.SubmoduleGModule(mo,SolutionMat(adj[2],Flat(v)));
  return Length(sub);
end;

BracketSpan:=function(h)
local sp,a,b,v,i;
  sp:=[];
  for i in [1..100] do
    a:=PseudoRandom(h);b:=PseudoRandom(h);
    v:=a*b-b*a;
    v:=Flat(v);
    if not IsZero(v) then
      if Length(sp)=0 or SolutionMat(sp,v)=fail then
        Add(sp,v);
      fi;
    fi;
  od;
  return Length(sp);
end;


NonAbsirrProcess:=function(dim,field,list)
local m,i,myis;

  myis:=function(A,B)
    if Size(A)<>Size(B) then return fail;fi;
    if Length(ConjugacyClasses(A))<>Length(ConjugacyClasses(B)) then return fail;fi;
    if Exponent(A)<>Exponent(B) then return fail;fi;
    if Collected(List(ConjugacyClasses(A),x->[Order(Representative(x)),Size(x)]))
      <>Collected(List(ConjugacyClasses(B),x->[Order(Representative(x)),Size(x)])) then
      return fail;
    fi;
    return true;
  end;
  m:=ClassicalMaximals("L",AbsInt(dim),field);
  field:=GF(field);
  # abs irr.
  m:=Filtered(m,x->MTX.IsAbsolutelyIrreducible(GModuleByMats(GeneratorsOfGroup(x),field)));

  #absirr
  m:=Filtered(m,x->MTX.IsIrreducible(GModuleByMats(ConstructAdjointRep(x,SL)[1],field)));

  #C9



  for i in m do
    Print(First([1..Length(m)],x->IsIdenticalObj(i,m[x]))," / ",Length(m),"\n");
    #SetSize(i,Size(RecognizeGroup(i)));
    #FittingFreeLiftSetup(i);
  od;
  Print("found ",List(m,x->Size(x:cheap)),"\n");

  if dim<0 then return m;fi;

  m:=List(m,x->Image(IsomorphismPermGroup(x:cheap)));
  for i in m do
    if ForAll(list,x->myis(x,i)=fail) then
      Add(list,i);
    fi;
  od;
  if Length(list)>0 then
    Print(field,": ",Length(list)," @ ",Maximum(List(list,Order))," - ",
      Maximum(List(list,x->Maximum(List(ConjugacyClasses(x),y->Order(Representative(y)))))),
      " - ",Lcm(List(list,Exponent)),"\n");
  fi;
end;


pRHOcess:=function(par)
local g,den,p,m;
  g:=RhoK(par);
  den:=Set(Factors(DenominatorRat(par)));
  p:=PrimesNonSurjective(g,SL:badprimes:=Filtered(den,IsPrimeInt));
  m:=MaxPCSPrimes(g,p,SL);
  return [par,p,m];
end;

DWIM:=function()
local result,i,par;
  result:=[];
  par:=Set(List(Cartesian([-20..20],Filtered(Primes,x->x<20)),x->x[1]/x[2]));
  SortBy(par,x->AbsInt(NumeratorRat(x)*DenominatorRat(x)));
  for i in par do
    Print("TRY ",i,"\n\n");
    Add(result,pRHOcess(i));
  od;
  return result;
end;

TransvecOrbitComm:=function(g,seed)
local gens,orb,p,a,img,i,dict,f;
  gens:=GeneratorsOfGroup(g);
  gens:=Union(gens,List(gens,Inverse));
  dict:=NewDictionary(Flat(seed),false,Rationals^(Length(seed)^2));
  orb:=[seed];
  AddDictionary(dict,Flat(seed));
  p:=1;
  repeat
    Print("Extending ",p,", orblen=",Length(orb),"\n");
    for a in gens do
      img:=orb[p]^a;
      f:=Flat(img);
      if KnowsDictionary(dict,f)=false then
        for i in [1..Length(orb)] do
          # first test first row, cheaper
          if orb[i][1]*img=img[1]*orb[i] and orb[i]*img=img*orb[i] then
            Error("commutes");
          fi;
        od;
        Add(orb,img);
        AddDictionary(dict,f);
      fi;
    od;
    p:=p+1;
  until p>Length(orb);
end;


# Symplectic groups (different form) that can have rational parameter
SympleQEx:=function(t,s)
  return Group([[1,t,1/2*t^2,t^3/6],[0,1,t,1/2*t^2],[0,0,1,t],[0,0,0,1]],
  [[1,0,0,0],[0,1,0,0],[0,0,1,0],[s,0,0,1]]);
end;


FreeHumphries:=function(n,v)
local L,a,i,j,k,x,gc,compareLarger,sqabsvalapprox,sgn,p,b,f,y,approx;

  f:=Field(v);
  # power basis
  p:=PrimitiveElement(f);
  b:=Basis(f,List([0..DegreeOverPrimeField(f)-1],a->p^a));

  if Length(b)=1 then
   approx:=p;
   gc:=x->x;
  else
    # approx primitive element
    L:=CoefficientsOfUnivariatePolynomial(MinimalPolynomial(Rationals,p));
    L:=1/L[Length(L)]*L; # normed
    if Length(L)>3 then
      Error("deg >2");
    fi;
    gc:=x->GaloisCyc(x,-1);

    approx:=(-L[2]+ApproximateRoot(L[2]^2-4*L[1],2,
    # Twice as many digits as numbers have
    2+4*Maximum(List(L,x->LogInt(AbsInt(x)+1,10)))))/2;
  fi;
  approx:=List([0..Length(b)-1],i->approx^i);

  # since x^2 is strictly monotonous, compare the squares of the absolute
  # values instead
  sqabsvalapprox:=function(a)
    a:=a*gc(a);
    return approx*Coefficients(b,a);
  end;

  compareLarger:=function(a,b)
    return sqabsvalapprox(a)>sqabsvalapprox(b);
  end;

  x:=X(Rationals,"x");
  y:=X(Rationals,"y");
  L:=[[0,x^2+1,x],[x,0,x+1],[-x+1,x^2,0]]*x^0;

  while Length(L)<n do
    k:=0;
    sgn:=-1;
    repeat
      sgn:=-sgn;
      if sgn=1 then k:=k+1;fi;
      a:=k*L[1];
      for i in [2..Length(L)-1] do
        a:=a+L[i];
      od;
      a:=a+sgn*L[Length(L)];
    until ForAll([1..Length(a)-1],
      x->DegreeOfUnivariateLaurentPolynomial(a[x])
        =DegreeOfUnivariateLaurentPolynomial(L[Length(L)][x])) and
      DegreeOfUnivariateLaurentPolynomial(a[Length(a)])
        =DegreeOfUnivariateLaurentPolynomial(L[Length(L)-1][Length(a)]);
    Add(L,a);
    a:=1;
    for i in [1..Length(L)-2] do
      #a:=NextPrimeInt(a);
      #L[i][Length(L)]:=i*x-a;
      L[i][Length(L)]:=x;
    od;
    L[Length(L)-1][Length(L)]:=y;
    L[Length(L)][Length(L)]:=0*x^0;
    a:=PolynomialCoefficientsOfPolynomial(DeterminantMat(L)-1,y);
    L[Length(L)-1][Length(L)]:=-a[1]/a[2];
    if not IsOne(DeterminantMat(L)) then Error("det!");fi;
  od;

  Display(L:compact);

  L:=List(L,r->List(r,y->Value(y,v)));

  # test
  for i in [1..n] do
    for j in [1..n] do
      if j<>i and not compareLarger(L[i,j]*L[j,i],4) then
        return fail;
      fi;
      for k in [1..n] do
        if i<>j and i<>k and j<>k and not compareLarger(L[i,j]*L[j,k],6*L[i,k]) then
          return fail;
        fi;
      od;
    od;
  od;

  for i in [1..n] do L[i,i]:=1;od;

  p:=List([1..n],x->IdentityMat(n,1));
  for i in [1..n] do p[i][i]:=L[i];od;
  return Group(p,One(p[1]));
end;


CostLimitedFactors:=function(n);
  if ValueOption("cheapfactor")=true then
    a:=PartialFactorization(n);
    p:=Filtered(a,IsPrimeInt);
    a:=Filtered(a,x->not x in p);
    if Length(a)>0 then
      Print("Eliminated huge factors: ",a,"\n");
    fi;
    return p;
  else
    return Factors(n);
  fi;
end;

# create functions for some basic number theoretic operations for the ring
# of integers of an algebraic number field. The input parameter `ring` is
# either Z or Q, or the algebraic number field.
# Supported fields are:
#  - Integers/Rationals (case 1)
#  - quadratic abelian number fields, i.e. Q(ER(d)) (case 3)
#  - all other abelian number fields, i.e. subfields NF(n,stab) of
#    cyclotomic fields (case 4)
#  - fields constructed with `FieldExtension(Rationals,pol)` (respectively
#    `AlgebraicExtension`) for an irreducible pol over the rationals
#    (case 4). The integral basis is taken from the attribute
#    `IntegralBasisNumberField` if this is bound, otherwise it is computed
#    with the Round 2 algorithm.
# primes are prime ideals, given in form of a record with components:
# p: Integer prime below
# fieldsize: Size of quotient field O/I
# redfun: A function that maps elements of O into O/I (with representation
# of O/I chosen by the code, typically a finite field in GAP).
# basimg: The images of the integral basis of O under this reduction.
# In case 4 there are further components:
# residuefield: the field O/P, this is GF(p^deg), unless that would require
#    the computation of a Conway polynomial, in which case it is an
#    AlgebraicExtension of GF(p),
# deg: residue degree f, ramify: ramification index e if e>1, 0 otherwise,
# ramindex: ramification index e (also if e=1),
# idealgens: generators of the ideal: either [alpha] (principal ideal,
# found by search of small elements) or [p,alpha] (two-element form),
# ideal: string describing the generators,
# zbasis: Z-basis of the ideal (in HNF, rows are coefficient vectors with
#         respect to `bas`),
# tau: coefficient vector of tau in O with tau*P in p*O, but not in p*O,
#      so tau/p in P^-1 (used for valuations).
#
# The function `PrepareReductionInfo` returns a record with the
# following components:
# bas: an integral basis of the number field (i.e. Z-basis of ring of integers)
# denominatorfun: a function that returns the Lcm of the Z denominator, if
# an element is not in the ring of integers
# normval: a function returning the absolute value of the norm of an element
#          of the field extension
# primesinnumber: a function returning the list of prime ideals (excluding
# duplicates) that divide a given algebraic integer (i.e. the principal
# ideal).
# primesinprime: A function that for an integer prime p returns the prime
# ideals lying above it. Basically primesinnumber can calculate the norm,
# factor over the integers and then use primesinprime and test which prime
# ideals actually divide.
# In case 4 there are further components:
# degree: degree of the field over Q
# coeffs: function, returns the coefficient vector of a field element with
#         respect to `bas` (faster than `Coefficients(d.bas,a)`)
# multab: structure constants of O wrt. `bas`: multab[i][j] is the
#         coefficient vector of bas[i]*bas[j]
# valuation(a,P): the exponent of the prime ideal P in the fractional ideal (a)
# idealfactors(a): list of pairs [P,exponent] giving the factorization of
#        the fractional ideal (a) into prime ideals.
# other record components can be used for caching.

DeclareAttribute("IntegralBasisNumberField",IsField);

#############################################################################
##
##  Utility functions for general number fields (case 4).
##  Elements of the ring of integers O are represented by their coefficient
##  vectors with respect to the integral basis. `T` always denotes a table
##  of structure constants: T[i][j] is the coefficient vector of b_i*b_j.
##

# matrix of multiplication by the element with coefficient vector v, in row
# convention: coeffs(x*y)=coeffs(x)*NumthMultMat(T,coeffs(y)).
NumthMultMat:=function(T,v)
local m,i;
  m:=v[1]*T[1];
  for i in [2..Length(T)] do
    if not IsZero(v[i]) then
      m:=m+v[i]*T[i];
    fi;
  od;
  return m;
end;

# v^e for coefficient vector v, e>=1
NumthPower:=function(T,v,e)
local r,have;
  have:=false;
  r:=v;
  while e>0 do
    if IsOddInt(e) then
      if have then
        r:=r*NumthMultMat(T,v);
      else
        r:=v;
        have:=true;
      fi;
    fi;
    e:=QuoInt(e,2);
    if e>0 then
      v:=v*NumthMultMat(T,v);
    fi;
  od;
  return r;
end;

# matrix of the Frobenius x -> x^p on O/pO, T must be the structure
# constants mod p.
NumthFrobeniusMat:=function(T,p)
  return List(IdentityMat(Length(T),GF(p)),v->NumthPower(T,v,p));
end;

# trace form matrix Tr(b_i*b_j) for structure constants T
NumthTraceForm:=function(T)
local n,tr;
  n:=Length(T);
  tr:=List(T,TraceMat); # Tr(b_i)
  return List([1..n],i->List([1..n],j->T[i][j]*tr));
end;

# HNF basis of the Z-lattice spanned by the integer vectors in rows
NumthLatticeHNF:=function(rows)
  return Filtered(HermiteNormalFormIntegerMat(rows),r->not IsZero(r));
end;

# Rational basis matrix B (rows) of a full lattice. Returns a basis of the
# same lattice in lower triangular Hermite form, so that the i-th
# vector only involves the first i coordinates (for a power basis: 1 is
# the first vector, the i-th vector is a polynomial of degree i-1 divided
# by an integer).
NumthNiceBasisMat:=function(B)
local den,L;
  den:=Lcm(List(Flat(B),DenominatorRat));
  L:=List(den*B,Reversed);
  L:=NumthLatticeHNF(L);
  L:=Reversed(List(L,Reversed));
  return L/den;
end;

# For a basis `bas` of an abelian number field of conductor N, return a
# function that computes coefficients wrt. `bas`. This reads off the
# coefficients wrt. the Zumbroich basis of CF(N) (which is how cyclotomics
# are stored) and is much faster than `Coefficients` for large conductors.
NumthCyclotomicCoeffsFun:=function(bas,N)
local Z,J,inv;
  Z:=List(bas,b->CoeffsCyc(b,N));
  J:=SemiEchelonMat(Z).heads;
  J:=Filtered([1..N],j->J[j]<>0); # columns with invertible minor
  inv:=(Z{[1..Length(bas)]}{J})^-1;
  return x->CoeffsCyc(x,N){J}*inv;
end;

# Integral basis of an abelian number field K, returned as list of elements.
# We use that the Zumbroich basis of CF(N) is a Z-basis of Z[E(N)] and
# that the ring of integers of K is the intersection of Z[E(N)] with K.
NumthAbelianIntegralBasis:=function(K)
local N,cb,C,cols,D,H;
  N:=Conductor(K);
  cb:=BasisVectors(CanonicalBasis(K));
  # coefficients wrt Zumbroich basis (padded with zeroes)
  C:=List(cb,x->CoeffsCyc(x,N));
  cols:=Filtered([1..N],j->ForAny(C,r->r[j]<>0));
  C:=List(C,r->r{cols});
  # we want the lattice of all v with v*C integral. If the columns of
  # D*C span the same lattice as the columns of the square matrix H, this
  # is the set of v with v*H in D*Z^n.
  D:=Lcm(List(Flat(C),DenominatorRat));
  H:=TransposedMat(NumthLatticeHNF(TransposedMat(D*C)));
  return List(D*H^-1,v->v*cb);
end;

# Integral basis of an algebraic extension F of the rationals by the Round 2
# algorithm (Pohst-Zassenhaus, see Cohen, Algorithm 6.1.8). Returns a matrix
# whose rows are the coefficients of the basis elements wrt CanonicalBasis(F)
# (i.e. the powers of the root of the defining polynomial).
NumthRoundTwo:=function(F)
local cb,vecs,cf,n,k,q,ex,i,j,v,B,orderdata,T,disc,p,one,Fr,e,R,I,Iinv,
      big,ker,U;
  cb:=CanonicalBasis(F);
  vecs:=BasisVectors(cb);
  cf:=CoefficientsOfUnivariatePolynomial(DefiningPolynomial(F));
  n:=Length(cf)-1;
  cf:=cf/cf[n+1]; # monic

  # smallest k such that k*theta is integral
  k:=1;
  for q in Set(CostLimitedFactors(Lcm(List(cf,DenominatorRat)))) do
    if q>1 then
      ex:=0;
      for i in [0..n-1] do
        v:=0;
        j:=DenominatorRat(cf[i+1]);
        while j mod q=0 do
          j:=j/q;
          v:=v+1;
        od;
        ex:=Maximum(ex,QuoInt(v+n-i-1,n-i)); # ceiling of v/(n-i)
      od;
      k:=k*q^ex;
    fi;
  od;

  # start with the equation order Z[k*theta]
  B:=DiagonalMat(List([0..n-1],i->k^i));

  # structure constants for the order with basis B
  orderdata:=function(B)
  local els,Binv;
    els:=List(B,r->r*vecs);
    Binv:=B^-1;
    return List(els,a->List(els,b->Coefficients(cb,a*b)*Binv));
  end;

  T:=orderdata(B);
  disc:=DeterminantMat(NumthTraceForm(T));
  for p in Set(CostLimitedFactors(AbsInt(disc))) do
    while p>1 and disc mod p^2=0 do
      one:=One(GF(p));
      # p-radical I of the order
      Fr:=NumthFrobeniusMat(List(T,m->m*one),p);
      e:=1;
      while p^e<n do e:=e+1;od;
      R:=NullspaceMat(Fr^e);
      I:=NumthLatticeHNF(Concatenation(List(R,r->List(r,Int)),
                                       p*IdentityMat(n)));
      # ring of multipliers of I is U/p with U={x | x*I in p*I}
      Iinv:=I^-1;
      big:=List(T,m->Concatenation(I*m*Iinv)*one);
      ker:=NullspaceMat(big);
      if Length(ker)=0 then
        break; # order is p-maximal
      fi;
      U:=NumthLatticeHNF(Concatenation(List(ker,r->List(r,Int)),
                                       p*IdentityMat(n)));
      B:=U*B/p;
      T:=orderdata(B);
      disc:=disc/p^(2*Length(ker));
    od;
  od;
  return NumthNiceBasisMat(B);
end;

# string for an element, as in the quadratic case use `Quadratic` if possible
NumthElmString:=function(a)
local q;
  if IsCyc(a) then
    q:=Quadratic(a);
    if q<>fail then return q.display;fi;
  fi;
  return String(a);
end;

# Generators for the prime ideal P (record as above). Returns [p] if P=(p),
# [alpha] if a small generator of P was found and [p,alpha] otherwise.
# alpha is chosen from P such that the exponent of p in the norm of alpha is
# the residue degree f, thus v_P(alpha)=1 and v_Q(alpha)=0 for all other
# primes Q over p, and (p,alpha)=P.
NumthIdealGenerators:=function(d,P)
local n,p,f,red,lll,normv,vp,try,i,j,s,cnt,twoel,principal,v,m;
  n:=d.degree;
  p:=P.p;
  f:=P.deg;
  if f=n then return [p];fi; # inert

  # LLL reduced Z-basis of P, so we find small elements first
  lll:=LLLReducedGramMat(P.zbasis*d.gram*TransposedMat(P.zbasis));
  red:=lll.transformation*P.zbasis;

  normv:=v->AbsInt(DeterminantMat(NumthMultMat(d.multab,v)));
  vp:=function(m)
  local k;
    k:=0;
    while m mod p=0 do
      m:=m/p;
      k:=k+1;
    od;
    return k;
  end;

  twoel:=fail;
  principal:=fail;
  try:=function(v)
    if IsZero(v) or principal<>fail then return;fi;
    m:=normv(v);
    if m=p^f then
      principal:=v;
    elif twoel=fail and vp(m)=f then
      twoel:=v;
    fi;
  end;

  # small elements: basis vectors, sums/differences of two, random
  for i in [1..n] do
    try(red[i]);
  od;
  for i in [1..n] do
    for j in [i+1..n] do
      for s in [1,-1] do
        try(red[i]+s*red[j]);
      od;
    od;
  od;
  cnt:=0;
  while principal=fail and cnt<100+10*n do
    try(List([1..n],x->Random([-2..2]))*red);
    cnt:=cnt+1;
  od;
  # if needed keep searching for a two-element generator
  s:=2;
  while principal=fail and twoel=fail do
    for cnt in [1..100] do
      try(List([1..n],x->Random([-s..s]))*red);
    od;
    s:=s+1;
  od;

  if principal<>fail then
    v:=principal;
  else
    v:=twoel;
  fi;
  if v[PositionNonZero(v)]<0 then v:=-v;fi;
  v:=v*BasisVectors(d.bas);
  if principal<>fail then
    return [v];
  else
    return [p,v];
  fi;
end;

# Decomposition of the rational prime p in the ring of integers described by
# the record d (case 4). Works for all p (also for indices of p in the
# equation order, and for common index divisors) by decomposing the algebra
# A=O/pO: The fixed points of the Frobenius on A are spanned by the primitive
# idempotents of A, the prime ideals above p correspond to the local
# components eps*A, and P/pO=(1-eps)A+Rad(A).
NumthPrimeDecomposition:=function(d,p)
local n,F,one,T,mm,Fr,k,rad,W,oneA,ids,w,new,eps,we,roots,c,c2,f,
      l,Pbar,ef,deg,e,Phi,proj,cands,y,pw,pr,i,sol,pol,rho,resfield,basimg,
      tau,r;

  n:=d.degree;
  F:=GF(p);
  one:=One(F);
  T:=List(d.multab,m->ImmutableMatrix(F,m*one));
  mm:=v->NumthMultMat(T,v);
  oneA:=d.one*one;

  Fr:=NumthFrobeniusMat(T,p);
  k:=1;
  while p^k<n do k:=k+1;od;
  rad:=NullspaceMat(Fr^k); # radical of A
  W:=NullspaceMat(Fr-IdentityMat(n,F)); # F_p-span of primitive idempotents

  # split the idempotent 1 into primitive idempotents, using the eigenvalue
  # decomposition (in F_p) of the elements of W.
  ids:=[oneA];
  for w in W do
    if Length(ids)<Length(W) then
      new:=[];
      for eps in ids do
        we:=w*mm(eps);
        roots:=Set(RootsOfUPol(F,MinimalPolynomial(F,mm(we))));
        if Length(roots)=1 then
          Add(new,eps);
        else
          for c in roots do
            # idempotent for eigenvalue c, within eps*A
            f:=eps;
            for c2 in Difference(roots,[c]) do
              f:=f*mm(we-c2*eps)/(c-c2);
            od;
            if not IsZero(f) then
              Add(new,f);
            fi;
          od;
        fi;
      od;
      ids:=new;
    fi;
  od;
  if Length(ids)<>Length(W) then Error("idempotent splitting failed");fi;

  l:=[];
  for eps in ids do
    ef:=RankMat(mm(eps)); # dim eps*A = e*f
    Pbar:=Filtered(Concatenation(mm(oneA-eps),rad),x->not IsZero(x));
    if Length(Pbar)>0 then
      Pbar:=BaseMat(Pbar);
    fi;
    deg:=n-Length(Pbar);
    e:=ef/deg;

    # map A -> A/Pbar = residue field, given by the annihilator of Pbar
    if Length(Pbar)=0 then
      Phi:=IdentityMat(n,F);
    else
      Phi:=TransposedMat(NullspaceMat(TransposedMat(Pbar)));
    fi;
    proj:=v->v*Phi;

    # find a generator y of the residue field, map it to a root of its
    # minimal polynomial in GF(p^deg) and get the images of the basis
    cands:=Concatenation([oneA],IdentityMat(n,F));
    i:=0;
    basimg:=fail;
    repeat
      i:=i+1;
      if i<=Length(cands) then
        y:=cands[i];
      else
        y:=Random(F^n);
      fi;
      pw:=[oneA];
      while Length(pw)<=deg do
        Add(pw,pw[Length(pw)]*mm(y));
      od;
      pr:=List(pw,proj);
      if RankMat(pr{[1..deg]})=deg then
        sol:=SolutionMat(pr{[1..deg]},pr[deg+1]);
        pol:=UnivariatePolynomial(F,Concatenation(-sol,[one]));
        if deg=1 or IsCheapConwayPolynomial(p,deg) then
          resfield:=GF(p^deg);
          rho:=RootsOfUPol(resfield,pol)[1];
        else
          # avoid computing a Conway polynomial for huge fields
          resfield:=AlgebraicExtension(F,pol);
          rho:=RootOfDefiningPolynomial(resfield);
        fi;
        rho:=List([0..deg-1],j->rho^j);
        basimg:=List(IdentityMat(n,F),b->SolutionMat(pr{[1..deg]},proj(b))*rho);
      fi;
    until basimg<>fail;

    # anti-uniformizer: tau with tau*Pbar=0 in A
    if Length(Pbar)=0 then
      tau:=ShallowCopy(d.one);
    else
      tau:=NullspaceMat(List([1..n],
             i->Concatenation(List(Pbar,u->mm(u)[i]))))[1];
      tau:=List(tau,Int);
    fi;

    r:=rec(p:=p,deg:=deg,fieldsize:=p^deg,
           ramindex:=e,
           residuefield:=resfield,
           basimg:=basimg,
           redfun:=d.makeredfun(basimg),
           zbasis:=NumthLatticeHNF(Concatenation(List(Pbar,v->List(v,Int)),
                                                 p*IdentityMat(n))),
           tau:=tau,
           taumat:=NumthMultMat(d.multab,tau));
    if e=1 then
      r.ramify:=0;
    else
      r.ramify:=e;
    fi;
    Add(l,r);
  od;
  # determine generators only once all primes over p are known
  for r in l do
    r.idealgens:=NumthIdealGenerators(d,r);
    r.ideal:=Concatenation("( ",JoinStringsWithSeparator(
                             List(r.idealgens,NumthElmString),", ")," )");
  od;
  return l;
end;

# exponent of the prime ideal P in the fractional ideal (a), a nonzero
NumthValuation:=function(d,P,a)
local c,den,v,y,p;
  if IsZero(a) then return infinity;fi;
  p:=P.p;
  c:=d.coeffs(a);
  den:=Lcm(List(c,DenominatorRat));
  c:=den*c;
  v:=0;
  # multiplication by tau/p keeps elements integral iff they are in P, and
  # reduces v_P by one.
  repeat
    y:=c*P.taumat;
    if ForAll(y,i->i mod p=0) then
      c:=y/p;
      v:=v+1;
    else
      y:=fail;
    fi;
  until y=fail;
  while den mod p=0 do
    den:=den/p;
    v:=v-P.ramindex;
  od;
  return v;
end;

# set up the record d for an abelian number field or an algebraic extension
# of the rationals (case 4).
NumthGeneralSetup:=function(d,ring)
local cb,coeffs,rawc,B,Binv,a,n,bas,multab,tr,G,lll,Tm,Tminv,oldpin;
  if IsAlgebraicExtension(ring) then
    if LeftActingDomain(ring)<>Rationals then
      Error("only extensions of the rationals are supported");
    fi;
    d.isabelian:=false;
    cb:=CanonicalBasis(ring);
    if HasIntegralBasisNumberField(ring) then
      # oracle
      bas:=IntegralBasisNumberField(ring);
      if IsBasis(bas) then bas:=BasisVectors(bas);fi;
      B:=List(bas,x->Coefficients(cb,x));
    else
      B:=NumthRoundTwo(ring);
      bas:=List(B,v->v*BasisVectors(cb));
    fi;
    Binv:=B^-1;
    coeffs:=function(x)
      if IsRat(x) then x:=x*One(ring);fi;
      return Coefficients(cb,x)*Binv;
    end;
    d.omega:=RootOfDefiningPolynomial(ring);
    d.minpol:=DefiningPolynomial(ring);
    d.gram:=IdentityMat(Length(B));
  else
    d.isabelian:=true;
    bas:=NumthAbelianIntegralBasis(ring);
    coeffs:=NumthCyclotomicCoeffsFun(bas,Conductor(ring));
    d.omega:=PrimitiveElement(ring);
    d.minpol:=MinimalPolynomial(Rationals,d.omega);
  fi;

  n:=Length(bas);
  multab:=List(bas,a->List(bas,b->coeffs(a*b)));
  if not ForAll(Flat(multab),IsInt) then
    Error("basis is not a basis of an order");
  fi;

  if d.isabelian then
    # LLL reduce the basis with respect to T2(x)=Tr(x*ComplexConjugate(x)),
    # so that basis elements (and ideal generators found) are small.
    tr:=List(multab,TraceMat);
    G:=List(bas,b->coeffs(GaloisCyc(b,-1)));
    G:=List([1..n],i->List([1..n],j->G[j]*multab[i]*tr));
    lll:=LLLReducedGramMat(G);
    Tm:=List(lll.transformation,ShallowCopy);
    # cosmetics: rational basis elements positive, 1 first if it occurs
    for a in [1..n] do
      if IsRat(Tm[a]*bas) and Tm[a]*bas<0 then
        Tm[a]:=-Tm[a];
      fi;
    od;
    a:=PositionProperty(Tm,r->IsOne(r*bas));
    if a<>fail and a>1 then
      a:=Concatenation([a],Difference([1..n],[a]));
      Tm:=Tm{a};
    fi;
    Tminv:=Tm^-1;
    bas:=List(Tm,r->r*bas);
    multab:=List(Tm,r->List(Tm,s->s*NumthMultMat(multab,r)*Tminv));
    rawc:=coeffs;
    coeffs:=x->rawc(x)*Tminv;
    d.gram:=Tm*G*TransposedMat(Tm);
  fi;

  d.degree:=n;
  d.field:=ring;
  d.bas:=BasisNC(ring,bas);
  d.coeffs:=coeffs;
  d.multab:=multab;
  d.one:=d.coeffs(One(ring));
  d.discriminant:=DeterminantMat(NumthTraceForm(d.multab));

  d.denominatorfun:=function(a)
    return Lcm(List(d.coeffs(a),DenominatorRat));
  end;

  d.normval:=function(a)
    return AbsInt(DeterminantMat(NumthMultMat(d.multab,d.coeffs(a))));
  end;

  d.makeredfun:=basimg->function(elm)
                        local c;
                          c:=d.coeffs(elm);
                          if not ForAll(c,IsInt) then
                            c:=List(c,
                              x->x mod FamilyObj(basimg)!.Characteristic);
                          fi;
                          return c*basimg; # linear comb
                        end;

  d.doprimedeco:=function(p)
    if p=1 then return [p];fi;
    return NumthPrimeDecomposition(d,p);
  end;

  # also accept algebraic integers, not only rational integers
  oldpin:=d.primesinnumber;
  d.primesinnumber:=function(x)
  local l;
    if IsRat(x) then return oldpin(x);fi;
    l:=Filtered(Set(CostLimitedFactors(d.normval(x))),p->p>1);
    return Filtered(Concatenation(List(l,d.primesinprime)),
                    P->IsZero(P.redfun(x)));
  end;

  d.valuation:=function(x,P)
    return NumthValuation(d,P,x);
  end;

  d.idealfactors:=function(x)
  local den,l,res,P,v;
    if IsZero(x) then Error("zero has no factorization");fi;
    den:=d.denominatorfun(x);
    l:=Set(Concatenation(CostLimitedFactors(d.normval(den*x)),CostLimitedFactors(den)));
    l:=Filtered(l,p->p>1);
    res:=[];
    for P in Concatenation(List(l,d.primesinprime)) do
      v:=NumthValuation(d,P,x);
      if v<>0 then
        Add(res,[P,v]);
      fi;
    od;
    return res;
  end;

  # as in the quadratic case: list of generators of the prime ideals
  # dividing a, with multiplicity. Requires these ideals to be principal.
  d.factorsinnumbers:=function(x)
  local f,i;
    f:=[];
    for i in d.idealfactors(x) do
      if Length(i[1].idealgens)>1 then
        Error("Divide! No generator known for prime ideal ",i[1].ideal,
              " -- use `idealfactors`");
      fi;
      Append(f,ListWithIdenticalEntries(i[2],i[1].idealgens[1]));
    od;
    return f;
  end;

  d.redfuns:=[];
  # reduction modulo a prime ideal: Argument is a prime ideal record, an
  # inert rational prime, or a generator of a prime ideal.
  d.makereductionfunc:=function(number)
  local pos,P,l,nrm,p;
    pos:=Position(d.moduli,number);
    if pos=fail then
      if IsRecord(number) then
        P:=number;
      elif IsInt(number) then
        l:=d.primesinprime(AbsInt(number));
        if Length(l)<>1 or l[1].deg<>n then Error("not prime!");fi;
        P:=l[1];
      else
        nrm:=d.normval(number);
        p:=SmallestRootInt(nrm);
        if not IsPrimeInt(p) then Error("not prime!");fi;
        P:=First(d.primesinprime(p),
                 x->x.fieldsize=nrm and IsZero(x.redfun(number)));
        if P=fail then Error("not prime!");fi;
      fi;
      Add(d.moduli,number);
      pos:=Length(d.moduli);
      d.pinfo[pos]:=P;
      d.redfuns[pos]:=P.redfun;
    fi;
    return d.redfuns[pos];
  end;

end;

PrepareReductionInfo:=function(ring)
local d,den,c,makeredfun,a,basimg;
  if IsList(ring) then
    den:=ring[2];
    ring:=ring[1];
  else
    den:=1;
  fi;
  d:=rec(moduli:=[],pinfo:=[],primeinfo:=[],liftfuns:=[]); # data record, carrying the info

  d.primesinprime:=function(p)
  local a;
    a:=First(d.primeinfo,x->x[1]=p);
    if a<>fail then return a[2];fi;
    a:=d.doprimedeco(p);
    Add(d.primeinfo,[p,a]);
    return a;
  end;

  d.primesinnumber:=function(a)
  local b;
    a:=AbsInt(a);
    # allow to skip factorization issues
    if ValueOption("cheapfactor")=true then
      b:=PartialFactorization(a);
      a:=Set(Filtered(b,IsPrimeInt));
    else
      a:=Set(CostLimitedFactors(a));
    fi;
    if a=[1] then return a;fi;
    return Concatenation(List(a,d.primesinprime));
  end;

  if ring=Integers or ring=Rationals then

    d.case:=1;
    d.discriminant:=1;
    d.bas:=[1];
    d.normval:=AbsInt;
    d.doprimedeco:=p->rec(p:=p,deg:=1,fieldsize:=p,
      ideal:=Concatenation("(",String(p),")"),
      ramify:=0,redfun:=x->x*Z(p)^0);

  # test for algebraic extension first, as `IsAbelianNumberField` has no
  # method for these.
  elif IsAlgebraicExtension(ring) or
    (IsAbelianNumberField(ring) and DegreeOverPrimeField(ring)>2) then

    # general number field
    d.case:=4;
    NumthGeneralSetup(d,ring);

  elif IsAbelianNumberField(ring) then
    d.case:=3;

    # quadratic field. Find out which root
    c:=Conductor(ring);
    if DegreeOverPrimeField(ring)=2 then
      if ForAll(GeneratorsOfField(ring),x->GaloisCyc(x,-1)=x) then
        # real, root of positive
        if c mod 4=0 then c:=c/4; fi;
      else
        # complex, root of negative
        if c mod 4=0 then c:=c/4; fi;
        c:=-c;
      fi;
      # now the field is sqrt(c)
      if c mod 4=1 then
        d.bas:=Basis(ring,[1,(1+ER(c))/2]);
      else
        d.bas:=Basis(ring,[1,ER(c)]);
      fi;
      d.minpol:=MinimalPolynomial(Rationals,d.bas[2]);
      basimg:=a->[a^0,a];
      d.discriminant:=Discriminant(d.minpol);
      d.omega:=(d.discriminant+ER(d.discriminant))/2;
      d.degree:=2;
    else
      Error("field not yet done");
    fi;

    d.denominatorfun:=function(a)
      return Lcm(List(Coefficients(d.bas,a),DenominatorRat));
    end;

    d.discriminant:=Discriminant(d.minpol);
    d.field:=Field(d.omega);

    d.normval:=x->AbsInt(Norm(Field(x),x));
    makeredfun:=a->function(elm)
                   local c;
                    c:=Coefficients(d.bas,elm);
                    if not ForAll(c,IsInt) then
                      c:=List(c,x->x mod FamilyObj(a)!.Characteristic);
                    fi;
                    return c*a; # linear comb
                  end;

    d.doprimedeco:=function(p)
    local pol,l,i,m,a,r,it,ig,im,elm,co;

      if p=1 then return [p];fi;
      pol:=PolynomialModP(d.minpol,p);
      l:=[];
      for i in Collected(CostLimitedFactors(pol)) do
        m:=i[1];
        a:=RootsOfUPol(GF(p^DegreeOfLaurentPolynomial(m)),m)[1];
        a:=basimg(a); # basis images, given that minpol is for bas[2]
        if i[2]=1 then r:=0; else r:=i[2];fi;
        r:=rec(p:=p,deg:=DegreeOfLaurentPolynomial(m),ramify:=r,
          fieldsize:=p^DegreeOfLaurentPolynomial(m),
          residuefield:=GF(p^DegreeOfLaurentPolynomial(m)),
          basimg:=a,
          redfun:=makeredfun(a)); # wrapped to keep the right `a`.

        # find ideal generators
        it:=Iterator(ring);
        NextIterator(it); # zero
        ig:=[p];
        im:=ZIdealBasis(d.bas,d.bas,ig);
        im:=im.mat;
        if AbsInt(DeterminantMat(im))<>r.fieldsize then

          # form nullspace of map
          co:=Basis(GF(r.fieldsize));
          ig:=List(d.bas,x->List(Coefficients(co,r.redfun(x)),Int));
          im:=NullspaceMat(ig);
          im:=List(im,x->x*Lcm(List(x,DenominatorRat))); # integral
          ig:=List(im,x->x*d.bas);
          im:=ZIdealBasis(d.bas,d.bas,ig);
          im:=im.mat;
          if AbsInt(DeterminantMat(im))<>r.fieldsize then
            Add(ig,p);
            im:=ZIdealBasis(d.bas,d.bas,ig);
            im:=im.mat;
          fi;

          while AbsInt(DeterminantMat(im))<>r.fieldsize do
            repeat
              elm:=NextIterator(it);
              co:=Coefficients(d.bas,elm);
              if co[1]<0 then
                elm:=-elm;
                co:=-co;
              fi;
            until AllIntcoeffs(co) and IsZero(r.redfun(elm));
            if Length(im)=0 or not AllIntcoeffs(SolutionMat(im,co)) then
              Add(ig,elm);
              im:=ZIdealBasis(d.bas,d.bas,ig);
              im:=im.mat;
            fi;
          od;
        fi;

        if Length(ig)>1 and Length(d.bas)=2 then
          co:=QuadSingleIdealGen(ig,d);
          if co<>fail then
            im:=ZIdealBasis(d.bas,d.bas,[co]);
            im:=im.mat;
            if AbsInt(DeterminantMat(im))=r.fieldsize then
              ig:=[co];
            else
              Error("quadgen");
            fi;
          fi;

        fi;

        r.idealgens:=ig;
        co:="( ";
        for elm in ig do
          if elm<>ig[1] then
            Append(co,", ");
          fi;
          im:=Quadratic(elm);
          if im<>fail then
            im:=im.display;
          else
            im:=String(elm);
          fi;
          Append(co,im);
        od;
        Append(co," )");
        r.ideal:=co;
        Add(l,r);
      od;
      return l;
    end;


    d.redfuns:=[];
    d.makereductionfunc:=function(number)
    local pos,one,pol,x,root;
      pos:=Position(d.moduli,number);
      if pos=fail then
        Add(d.moduli,number);
        pos:=Length(d.moduli);

        # build reduction info
        if IsInt(number) and IsPrimeInt(number) then
          pol:=PolynomialModP(d.minpol,number);
          if not IsIrreducible(pol) then Error("not prime!");fi;
          root:=RootsOfUPol(GF(number^2),pol)[1];
          d.pinfo[pos]:=[root,d.bas,[One(GF(number)),root],number^2];
          d.redfuns[pos]:=function(a)
            return Coefficients(d.bas,a)*d.pinfo[pos][3];
          end;
        elif IsCyclotomic(number) and d.factorsinnumbers([number])=[number] then
          x:=AbsInt(Norm(Field(number),number));
          root:=Coefficients(d.bas,number);
          root:=-root[1]/root[2] mod x;
          root:=root*One(GF(x));
          d.pinfo[pos]:=[root,d.bas,[One(GF(x)),root],x];
          d.redfuns[pos]:=function(a)
            return Coefficients(d.bas,a)*d.pinfo[pos][3];
          end;
        else
          d.redfuns[pos]:=makeredfun(number.basimg);
         
#          d.redfuns[pos]:=IdealQuotientNumorder(d.bas,[number]);
#          d.pinfo[pos]:=[fail,fail,fail,Size(Range(d.redfuns[pos]))];
        fi;
      fi;

      return d.redfuns[pos];
    end;

    d.factorsinnumbers:=function(a)
    local p,f,i;
      p:=d.primesinnumber(Norm(a)); # all primes occurring
      f:=[];
      for i in p do
        if Length(i.idealgens)>1 then Error("Divide!"); fi;
        i:=i.idealgens[1];
        while ForAll(Coefficients(d.bas,a/i),IsInt) do
          Add(f,i);
          a:=a/i;
        od;
      od;
      return f;
    end;

    ## BAD, does not work
    #d.gcdexfun:=function(a,b)
    #  return NormGcdex(d,a,b);
    #end;

  else
    Error("not yet done");
  fi;

  return d;


end;

#############################################################################
##
##  SturmSequence( <f> )
##
##  Returns the Sturm sequence  f_0 = f, f_1 = f', f_{i+1} = -rem(f_{i-1}, f_i)
##  of the univariate rational polynomial <f>, stopping at the last nonzero
##  term (which is, up to a constant, Gcd(f, f')).
##
BindGlobal( "SturmSequence", function( f )
local seq, a, b, r;
  if not IsUnivariatePolynomial( f ) then
    Error( "<f> must be a univariate polynomial" );
  fi;
  seq := [ f ];
  a := f;
  b := Derivative( f );
  while not IsZero( b ) do
    Add( seq, b );
    r := -EuclideanRemainder( a, b );
    a := b;
    b := r;
  od;
  return seq;
end );

#############################################################################
##
##  SignChanges( <list> )
##
##  Number of sign changes in a list of rationals, ignoring zeros.
##
BindGlobal( "SignChanges", function( l )
  l := List( Filtered( l, x -> not IsZero( x ) ), SignInt );
  return Number( [ 2 .. Length( l ) ], i -> l[i] <> l[i-1] );
end );

#############################################################################
##
##  NrRealRootsSturm( <f> )
##  NrRealRootsSturm( <f>, <a>, <b> )
##
##  Number of distinct real roots of the rational polynomial <f>; with
##  rationals <a> < <b> given, the number of distinct roots in (a, b].
##  The value at -infinity / +infinity is read off from the leading
##  coefficient and the parity of the degree of each term.
##
BindGlobal( "NrRealRootsSturm", function( arg )
local f, seq, atMinusInf, atPlusInf, a, b;
  f := arg[1];
  if IsZero( f ) then
    Error( "the zero polynomial has infinitely many roots" );
  fi;
  # make f squarefree; this does not change the set of roots, and makes the
  # interval version valid also when an endpoint is a root
  f := Quotient( f, Gcd( f, Derivative( f ) ) );
  seq := SturmSequence( f );

  if Length( arg ) = 1 then
    atPlusInf  := List( seq, LeadingCoefficient );
    atMinusInf := List( seq,
      g -> (-1)^DegreeOfLaurentPolynomial( g ) * LeadingCoefficient( g ) );
    return SignChanges( atMinusInf ) - SignChanges( atPlusInf );
  elif Length( arg ) = 3 then
    a := arg[2];
    b := arg[3];
    if not a < b then
      Error( "need <a> < <b>" );
    fi;
    return SignChanges( List( seq, g -> Value( g, a ) ) )
         - SignChanges( List( seq, g -> Value( g, b ) ) );
  else
    Error( "usage: NrRealRootsSturm( <f> [, <a>, <b>] )" );
  fi;
end );


#############################################################################
##
##  NamedBasisFromElements( <F>, <L>, <names> )
##
##  <F>      an algebraic extension of the rationals, e.g. AlgebraicExtension
##  <L>      a list of elements of <F>
##  <names>  a list of strings, <names>[i] being the name of <L>[i]
##
##  Tries to find a Q-basis B of <F> consisting of 1 and monomials
##  L[1]^e1 * ... * L[k]^ek in the elements of <L>. Monomials are tried by
##  increasing total degree; within a degree, products of distinct elements
##  are tried before products involving powers. A monomial is kept if it is
##  linearly independent of those chosen so far.
##
##  Returns a list [ B, Bnames ] where Bnames[j] is a string such as "1",
##  "a", "a*b" or "a^2*c" describing B[j]. If the elements of <L> do not
##  generate <F> (as an algebra), a warning is printed and B is a basis of
##  the subalgebra Q[L] only.
##
##  If B is complete, Basis( F, B ) gives a GAP basis object, so that
##  Coefficients( Basis( F, B ), x ) expresses x in terms of B.
##
BindGlobal( "NamedBasisFromElements", function( F, L, names )
local n, k, coeffs, rows, rank, B, Bnames, Bexps, layer, newlayer,
      cands, e, i, x, v, monname, squarefree;

  if Length( L ) <> Length( names ) then
    Error( "<L> and <names> must have the same length" );
  fi;
  n := DegreeOverPrimeField( F );
  k := Length( L );

  # coefficient vector of an element w.r.t. the power basis of F
  coeffs := x -> Coefficients( Basis( F ), x );

  # name of a monomial given by its exponent vector
  monname := function( e )
  local parts, i;
    parts := [];
    for i in [ 1 .. Length( e ) ] do
      if e[i] = 1 then
        Add( parts, names[i] );
      elif e[i] > 1 then
        Add( parts, Concatenation( names[i], "^", String( e[i] ) ) );
      fi;
    od;
    if parts = [] then
      return "1";
    fi;
    return JoinStringsWithSeparator( parts, "*" );
  end;

  squarefree := e -> ForAll( e, a -> a <= 1 );

  B      := [ One( F ) ];
  Bnames := [ "1" ];
  Bexps  := [ ListWithIdenticalEntries( k, 0 ) ];
  rows   := [ coeffs( One( F ) ) ];
  rank   := 1;
  layer  := [ Bexps[1] ];   # exponent vectors of basis elements of last degree

  # Candidates of degree d are (basis element of degree d-1) * L[i]. This
  # suffices: by induction, the span of all monomials of degree <= d equals
  # the span of the basis elements chosen of degree <= d.
  while rank < n and layer <> [] do
    cands := [];
    for e in layer do
      for i in [ 1 .. k ] do
        v := ShallowCopy( e );
        v[i] := v[i] + 1;
        AddSet( cands, v );
      od;
    od;
    # earlier elements of <L> first (descending lexicographic order), and
    # products of distinct elements before those involving powers
    Sort( cands, function( u, v ) return u > v; end );
    cands := Concatenation( Filtered( cands, squarefree ),
                            Filtered( cands, e -> not squarefree( e ) ) );

    newlayer := [];
    for e in cands do
      if rank = n then
        break;
      fi;
      x := Product( [ 1 .. k ], i -> L[i]^e[i], One( F ) );
      v := coeffs( x );
      if RankMat( Concatenation( rows, [ v ] ) ) > rank then
        Add( rows, v );
        rank := rank + 1;
        Add( B, x );
        Add( Bnames, monname( e ) );
        Add( Bexps, e );
        Add( newlayer, e );
      fi;
    od;
    layer := newlayer;
  od;

  if rank < n then
    Info( InfoWarning, 1, "NamedBasisFromElements: the elements only span a ",
          "subalgebra of dimension ", rank, " < ", n );
  fi;
  return [ Basis(F,B), Bnames ];
end );

InstallMethod(String,"AlgElm",true,[IsKroneckerConstRep],1,
function(a)
local fam,b,s,i,c,nam,den;
  fam:=FamilyObj(a);
  if not IsBound(fam!.nicePrintBasis) then TryNextMethod();fi;
  s:="";
  b:=fam!.nicePrintBasis[1];
  c:=Coefficients(b,a);
  den:=Lcm(List(c,DenominatorRat));
  if den<>1 then
    c:=c*den;
  fi;

  nam:=fam!.nicePrintBasis[2];
  for i in [1..Length(c)] do
    if not IsZero(c[i]) then
      t:=String(c[i]);
      if Length(s)>0 and t[1]<>'-' then Add(s,'+');fi;
      if IsOne(b[i]) then
        Append(s,t);
      elif IsOne(c[i]) then
        Append(s,nam[i]);
      elif IsOne(-c[i]) then
        Add(s,'-');
        Append(s,nam[i]);
      else
        Append(s,t);
        Add(s,'*');
        Append(s,nam[i]);
      fi;
    fi;
  od;
  if den<>1 then
    s:=Concatenation("1/",String(den),"*(",s,")");
  fi;

  return s;
end);

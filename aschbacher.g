#############################################################################
##
##  aschbacher.g
##
##  AschbacherClasses( <G> [, <F>] [, <opt>] )
##
##  Determines in which of the Aschbacher classes C1,...,C8 (in the sense of
##  Bray, Holt, Roney-Dougal, "The maximal subgroups of the low-dimensional
##  finite classical groups", Section 2.2, Case L, i.e. ambient group GL(n,q))
##  the matrix group <G> <= GL(n,q) lies.  Class C8 is split into
##
##     C8_1 : similarities of a non-degenerate symplectic or
##            (q odd) symmetric bilinear form,
##     C8_2 : similarities of a non-degenerate hermitian form (q a square).
##
##  The classes are tested via the defining properties of Section 2.2:
##
##     C1   reducible                               (Def. 2.2.1)
##     C2   imprimitive: preserves V = V_1 + ... + V_t, t > 1  (Def. 2.2.3)
##     C3   semilinear over GF(q^s), s prime dividing n         (Def. 2.2.5)
##     C4   preserves V = V_1 (x) V_2, 1 < dim V_1 < dim V_2    (Def. 2.2.9)
##     C5   absolutely irreducible and conjugate into Z.GL(n,q_0)
##                                                  (Def. 2.2.11)
##     C6   has an absolutely irreducible normal subgroup R that is
##          extraspecial of order r^(1+2m) (or of symplectic type
##          4o2^(1+2m)), n = r^m, with q as in Table 2.9 (Case L)
##                                                  (Def. 2.2.13)
##     C7   preserves V = V_1 (x) ... (x) V_t, dim V_i = m >= 3, possibly
##          permuting the factors                    (Def. 2.2.15)
##     C8   preserves a non-degenerate form up to scalars (Table 2.11)
##
##  Several classes may hold at the same time.  If <G> is irreducible, does
##  not contain SL(n,q) and lies in none of the classes, it lies in class S
##  (by Aschbacher's theorem); as a sanity check we verify that G/Z(G) is
##  almost simple.
##
##  The result is a record with components
##
##     classes        list of names of classes in which G was shown to lie
##     notInClasses   classes that were proven not to contain G
##     undecided      classes for which no decision could be made (see below)
##     irreducible, absolutelyIrreducible, containsSL
##     C1, C2, ...    certificates, for each class in <classes>:
##        C1:   rec( submodule )     basis of a proper invariant subspace
##        C2:   rec( blocks, t, m [,stabilizer] )  bases of the V_i
##        C3:   rec( degree, fieldGenerator, centralizer )
##              X:=fieldGenerator generates a field GF(q)[X] = GF(q^s)
##              inside Mat(n,q) normalised by G, centralised by centralizer
##        C4:   rec( dims, basis )   for P:=basis, P*g*P^-1 is a Kronecker
##              product of a dims[1] and a dims[2] matrix for all g in G
##        C5:   rec( subfield, conjugator )  X*g*X^-1 in Z.GL(n,subfield)
##        C6:   rec( prime, normalSubgroup, type )
##        C7:   rec( m, t, basis, swaps )  P*g*P^-1 is a Kronecker
##              product, possibly multiplied by the factor swap
##        C8_1: rec( form, type [, sign] [,quadraticForm] , multipliers )
##              g*form*TransposedMat(g) = multiplier(g)*form
##        C8_2: rec( form, multipliers )  hermitian form, i.e.
##              g*form*TransposedMat(Frobenius(g)) = multiplier(g)*form
##     tensorDecompositions   all tensor decompositions found (also those
##                            of shape m (x) m)
##     remarks        explanatory remarks
##
##  Options (record as further argument): cap, subalgebraCap, niceLimit,
##  refuteTries, see ASCH.DefaultOptions.  <F> (optional) is the field over
##  which G is to be considered, default DefaultFieldOfMatrixGroup(G).
##
##  Example:
##     gap> Read("aschbacher.g");
##     gap> r:=AschbacherClasses(Sp(4,3));; r.classes; r.C8_1.type;
##     [ "C8_1" ]
##     "symplectic"
##     gap> AschbacherClasses(Sp(4,3),GF(9)).classes;
##     [ "C5", "C8_1", "C8_2" ]
##
##  Methods and exactness
##
##  Group theoretic tasks (derived subgroup, normal subgroups of prime
##  index, maximal subgroups, O_r) use a faithful permutation action on the
##  orbits of the standard basis vectors (if of length <= opt.niceLimit, else
##  GAP's default nice monomorphism), so the function is meant for groups for
##  which this is feasible.  Randomisation (MeatAxe, choice of generators)
##  only affects running times, except in the refutation step described
##  below, which can only turn "undecided" into "no".  Every "yes" comes
##  with a certificate that is easy to verify.
##
##  * C1 (MeatAxe), C5, C6, C8_1, C8_2 are decided exactly.
##    C5: the scalar multiples of the generators that must have traces in
##        the subfield are determined, and the F_q0-span of the group they
##        generate is computed; it has dimension n^2 iff G is realisable
##        over F_q0 modulo scalars.
##    C6: G-invariant normal subgroups of O_r(G) of the right order.
##    C8: forms fixed by G' are a G-module; common eigenvectors of G on it
##        give all forms preserved up to scalars.
##  * C2, C3, C4, C7: for irreducible G every G-invariant unital subalgebra
##    B of Mat(n,q) is semisimple: if Z(B) is not a field, G is imprimitive
##    (blocks = Z(B)-homogeneous components); if Z(B) is a proper extension
##    field, G is semilinear; if Z(B)=F_q and B is proper, B = Mat(k,q)
##    gives a tensor decomposition.  We compute the algebras generated by
##    all minimal submodules of Mat(n,q)/scalars under conjugation.
##    - C2, C3: every block system (extension field) algebra contains one of
##      these algebras, so this decides C2 and C3.  If there are more than
##      opt.subalgebraCap minimal submodules, exact group theoretic tests
##      are used instead (subgroups of index dividing n with Frobenius
##      reciprocity; normal subgroups of prime index with Clifford theory).
##    - C4, C7 (t=2): if G is absolutely irreducible, primitive and not
##      semilinear, all invariant subalgebras are central simple and the
##      search is complete.  Otherwise, if no decomposition was found, we
##      search (opt.refuteTries random elements) for an element g whose
##      spectrum is not the product of an n1- and an n2-element multiset
##      (for C7 we use g^2, which lies in the kernel of the action on the
##      factors).  Such an element proves that G is not in the class; if
##      none is found the class is reported as undecided.
##      C7 with t>=3 factors (n>=27) is not implemented.
##  * For reducible groups only C1 is examined.
##
#############################################################################

ASCH:=rec();

ASCH.DefaultOptions:=rec(cap:=100000,subalgebraCap:=1500,niceLimit:=300000,
                        refuteTries:=200);

# degree over F of the centralising field of an irreducible module
# (MTX.DegreeSplittingField gives the degree over the prime field)
ASCH.CentDegree:=function(M,F)
  MTX.IsAbsolutelyIrreducible(M);
  return MTX.DegreeSplittingField(M)/DegreeOverPrimeField(F);
end;

# module from a (possibly empty) list of matrices
ASCH.Module:=function(gens,n,F)
  if Length(gens)=0 then
    return GModuleByMats([],n,F);
  fi;
  return GModuleByMats(gens,F);
end;

ASCH.Gens:=function(G)
local g;
  g:=Filtered(GeneratorsOfGroup(G),x->not IsOne(x));
  return g;
end;

# Install a faithful permutation representation (action on the orbits of
# the standard basis vectors) as nice monomorphism, provided these orbits
# have total length at most limit. This avoids degree reduction heuristics
# that can be very slow for some (e.g. cyclic) groups.
ASCH.SetNiceMono:=function(G,n,F,limit)
local gens,pts,dict,queue,v,w,g,hom;
  gens:=GeneratorsOfGroup(G);
  pts:=[];
  dict:=NewDictionary(ImmutableVector(F,One(G)[1]),false);
  for v in One(G) do
    v:=ImmutableVector(F,v);
    if not KnowsDictionary(dict,v) then
      AddDictionary(dict,v);
      Add(pts,v);
      queue:=[v];
      while Length(queue)>0 do
        w:=Remove(queue);
        for g in gens do
          v:=w*g;
          if not KnowsDictionary(dict,v) then
            AddDictionary(dict,v);
            Add(pts,v);
            Add(queue,v);
            if Length(pts)>limit then
              return false;
            fi;
          fi;
        od;
      od;
    fi;
  od;
  pts:=Set(pts);
  hom:=ActionHomomorphism(G,pts,OnRight,"surjective");
  IsInjective(hom);
  SetNiceMonomorphism(G,hom);
  SetIsHandledByNiceMonomorphism(G,true);
  return true;
end;

ASCH.Reshape:=function(v,n)
  return List([1..n],i->v{[(i-1)*n+1..i*n]});
end;

# all vectors of F^h whose first nonzero entry is one
ASCH.ProjectivePoints:=function(F,h)
local res,pos,t,els;
  els:=AsList(F);
  res:=[];
  for pos in [1..h] do
    for t in Tuples(els,h-pos) do
      Add(res,Concatenation(ListWithIdenticalEntries(pos-1,Zero(F)),
                            [One(F)],t));
    od;
  od;
  return res;
end;

# homogeneous components of a semisimple module
ASCH.HomogeneousComponents:=function(MN)
local comps,f,homs;
  comps:=[];
  for f in MTX.CollectedFactors(MN) do
    homs:=MTX.Homomorphisms(f[1],MN);
    Add(comps,BaseMat(Concatenation(homs)));
  od;
  return comps;
end;

# normal subgroups N of G with G/N cyclic of prime order s
ASCH.PrimeIndexNormalSubgroups:=function(G,s)
local D,hom,E;
  D:=ClosureGroup(DerivedSubgroup(G),List(GeneratorsOfGroup(G),g->g^s));
  if Index(G,D)=1 then
    return [];
  fi;
  hom:=NaturalHomomorphismByNormalSubgroup(G,D);
  E:=Image(hom,G);
  return List(MaximalSubgroups(E),M->PreImage(hom,M));
end;

# unital algebra generated by gens, or fail if dimension exceeds maxdim
ASCH.AlgebraClosure:=function(gens,n,F,maxdim)
local one,mb,basis,queue,b,s,c,v;
  one:=IdentityMat(n,F);
  mb:=MutableBasis(F,[Concatenation(one)]);
  basis:=[one];
  queue:=[one];
  while Length(queue)>0 do
    b:=Remove(queue);
    for s in gens do
      c:=b*s;
      v:=Concatenation(c);
      if not IsContainedInSpan(mb,v) then
        CloseMutableBasis(mb,v);
        Add(basis,c);
        Add(queue,c);
        if Length(basis)>maxdim then
          return fail;
        fi;
      fi;
    od;
  od;
  return basis;
end;

# write M as Kronecker product A (x) C with A n1 x n1, C n2 x n2, or fail
ASCH.KroneckerFactor:=function(M,n1,n2)
local block,i0,j0,C,k,l,A,i,j;
  block:=function(i,j)
    return M{[(i-1)*n2+1..i*n2]}{[(j-1)*n2+1..j*n2]};
  end;
  i0:=PositionProperty([1..n1],i->ForAny([1..n1],j->not IsZero(block(i,j))));
  if i0=fail then
    return fail;
  fi;
  j0:=PositionProperty([1..n1],j->not IsZero(block(i0,j)));
  C:=block(i0,j0);
  k:=PositionProperty(C,r->not IsZero(r));
  l:=PositionProperty(C[k],x->not IsZero(x));
  A:=List([1..n1],i->List([1..n1],j->block(i,j)[k][l]/C[k][l]));
  if KroneckerProduct(A,C)=M then
    return [A,C];
  fi;
  return fail;
end;

# an element generating the subfield of degree s inside the field F[Y],
# which is of degree d over F
ASCH.SubfieldGenerator:=function(Y,d,s,F)
local q,z,X;
  q:=Size(F);
  if d=s then
    return Y;
  fi;
  repeat
    z:=Sum([0..d-1],i->Random(F)*Y^i);
    # trace from GF(q^d) to GF(q^s)
    X:=Sum([0..d/s-1],j->z^(q^(s*j)));
  until Degree(MinimalPolynomial(F,X))=s;
  return X;
end;

# Representatives (up to G-conjugacy, possibly with repetitions) of all
# subgroups of G of index t>1 dividing n: follow chains of maximal subgroups.
ASCH.SubgroupsIndexDividing:=function(G,n)
local iso,P,res,recurse;
  if IsSolvableGroup(G) then
    iso:=IsomorphismPcGroup(G);
  else
    iso:=NiceMonomorphism(G);
  fi;
  P:=Image(iso,G);
  res:=[];
  recurse:=function(U,idx)
  local M,j;
    for M in MaximalSubgroupClassReps(U) do
      j:=idx*Index(U,M);
      if n mod j=0 and not ForAny(res,x->x[2]=j and x[1]=M) then
        Add(res,[M,j]);
        recurse(M,j);
      fi;
    od;
  end;
  recurse(P,1);
  return List(res,x->PreImage(iso,x[1]));
end;

#############################################################################
##
##  C2
##
ASCH.TestImprimitive:=function(G,n,F,d,opt)
local q,D,MD,comps,capped,H,t,m,MH,f,homs,h,c,W,blocks,T,seen,tw;
  q:=Size(F);
  if n=1 then
    return false;
  fi;
  # quick test: Clifford theory for the derived subgroup
  D:=DerivedSubgroup(G);
  MD:=ASCH.Module(ASCH.Gens(D),n,F);
  if not MTX.IsIrreducible(MD) then
    comps:=ASCH.HomogeneousComponents(MD);
    if Length(comps)>1 then
      return rec(blocks:=comps,t:=Length(comps),m:=n/Length(comps));
    fi;
  fi;
  # complete test: block stabilisers are subgroups of index t dividing n,
  # block W irreducible H-submodule of dimension n/t and
  # Hom_H(W,V) = End_G(V) is of dimension d (Frobenius reciprocity)
  capped:=false;
  for H in ASCH.SubgroupsIndexDividing(G,n) do
    t:=Index(G,H);
    if t>1 and n mod t=0 then
      m:=n/t;
      MH:=ASCH.Module(ASCH.Gens(H),n,F);
      T:=RightTransversal(G,H);
      for f in MTX.CollectedFactors(MH) do
        if MTX.Dimension(f[1])=m then
          homs:=MTX.Homomorphisms(f[1],MH);
          h:=Length(homs);
          if h=d then
            if (q^h-1)/(q-1)>opt.cap then
              capped:=true;
            else
              seen:=[];
              for c in ASCH.ProjectivePoints(F,h) do
                W:=Sum([1..h],i->c[i]*homs[i]);
                tw:=Immutable(TriangulizedMat(W));
                if not tw in seen then
                  AddSet(seen,tw);
                  blocks:=List(T,g->W*g);
                  if RankMat(Concatenation(blocks))=n then
                    return rec(blocks:=List(blocks,BaseMat),t:=t,m:=m,
                               stabilizer:=H);
                  fi;
                fi;
              od;
            fi;
          fi;
        fi;
      od;
    fi;
  od;
  if capped then
    return fail;
  fi;
  return false;
end;

#############################################################################
##
##  C3
##
##  G irreducible.  If G is not absolutely irreducible, End_G(V) is a field.
##  If G is absolutely irreducible, G is semilinear of prime degree s iff
##  there is N normal in G of index s with N irreducible and End_N(V) =
##  GF(q^s) (Clifford theory for the cyclic quotient G/N).
##
ASCH.TestSemilinear:=function(G,n,F,M,absirr)
local d,s,Y,N,MN;
  if not absirr then
    d:=ASCH.CentDegree(M,F);
    s:=Factors(d)[1];
    Y:=MTX.FieldGenCentMat(M);
    return rec(degree:=s,fieldGenerator:=ASCH.SubfieldGenerator(Y,d,s,F),
               centralizer:=G);
  fi;
  for s in PrimeDivisors(n) do
    for N in ASCH.PrimeIndexNormalSubgroups(G,s) do
      MN:=ASCH.Module(ASCH.Gens(N),n,F);
      if MTX.IsIrreducible(MN) and not MTX.IsAbsolutelyIrreducible(MN) then
        d:=ASCH.CentDegree(MN,F);
        Y:=MTX.FieldGenCentMat(MN);
        return rec(degree:=s,
                   fieldGenerator:=ASCH.SubfieldGenerator(Y,d,s,F),
                   centralizer:=N);
      fi;
    od;
  od;
  return false;
end;

#############################################################################
##
##  C4 / C7: tensor decompositions
##

# Given a unital subalgebra B (basis of matrices) of Mat(n,F), test whether
# B is central simple of dimension k^2, 1<k<n, and if so return a basis P
# such that P*b*P^-1 = b' (x) One for b in B.
ASCH.TensorBasisFromAlgebra:=function(B,n,F)
local k,MB,cf,W,homs,P,i,j;
  k:=RootInt(Length(B),2);
  if k^2<>Length(B) or n mod k<>0 or k=1 or k=n then
    return fail;
  fi;
  MB:=ASCH.Module(B,n,F);
  cf:=MTX.CollectedFactors(MB);
  if Length(cf)<>1 then
    return fail;
  fi;
  W:=cf[1][1];
  if MTX.Dimension(W)<>k or not MTX.IsAbsolutelyIrreducible(W) then
    return fail;
  fi;
  homs:=MTX.Homomorphisms(W,MB);
  if Length(homs)<>n/k then
    return fail;
  fi;
  P:=[];
  for i in [1..k] do
    for j in [1..n/k] do
      Add(P,homs[j][i]);
    od;
  od;
  if RankMat(P)<n then
    return fail;
  fi;
  return ImmutableMatrix(F,P);
end;

# basis of the centre of the algebra with basis B (list of matrices)
ASCH.CentreOfAlgebra:=function(B,n,F)
local rows,ns;
  rows:=List(B,Bi->Concatenation(List(B,Bj->Concatenation(Bi*Bj-Bj*Bi))));
  ns:=NullspaceMat(rows);
  return List(ns,c->Sum([1..Length(B)],i->c[i]*B[i]));
end;

# Search for unital subalgebras F < B < Mat(n,F) normalised by the group
# generated by gens: for every minimal submodule S of Mat(n,F)/F (under
# conjugation) compute the algebra generated by S.  If the group is
# irreducible, every invariant unital subalgebra is semisimple and
#  - if its centre is not a field, the homogeneous components of V under
#    the centre form a system of imprimitivity,
#  - if its centre is a proper extension field, the group is semilinear,
#  - if its centre is F, it is central simple and gives a tensor
#    decomposition.
# Every proper invariant subalgebra contains such an algebra, so the search
# detects imprimitivity and semilinearity completely; tensor decompositions
# are detected completely if the group is primitive and not semilinear.
ASCH.InvariantSubalgebras:=function(gens,n,F,opt)
local q,N,U,vecI,compl,Ubar,subs,f,homs,h,seen,c,W,res,Sb,S,B,P,k,ok,
      known,ZB,MZ,comps,maxdim;
  q:=Size(F);
  N:=n^2;
  res:=rec(capped:=false,tensor:=[],blocks:=[],fields:=[]);
  U:=ASCH.Module(List(gens,g->KroneckerProduct(TransposedMat(g^-1),g)),N,F);
  vecI:=Concatenation(IdentityMat(n,F));
  compl:=IdentityMat(N,F){[2..N]};
  Ubar:=MTX.InducedActionFactorModule(U,[vecI],compl);
  # irreducible submodules of Ubar
  # (if there are too many, skip the isotypic type and remember that the
  # search is incomplete)
  subs:=[];
  for f in MTX.CollectedFactors(Ubar) do
    homs:=MTX.Homomorphisms(f[1],Ubar);
    h:=Length(homs);
    if h>0 and Length(subs)+(q^h-1)/(q-1)>opt.subalgebraCap then
      res.capped:=true;
    elif h>0 then
      seen:=[];
      for c in ASCH.ProjectivePoints(F,h) do
        W:=TriangulizedMat(Sum([1..h],i->c[i]*homs[i]));
        AddSet(seen,Immutable(W));
      od;
      Append(subs,seen);
    fi;
  od;
  maxdim:=Maximum(n,Int(N/4));
  known:=[];
  for Sb in subs do
    S:=List(Sb,x->ASCH.Reshape(x*compl,n));
    B:=ASCH.AlgebraClosure(S,n,F,maxdim);
    if B<>fail then
      B:=Immutable(TriangulizedMat(List(B,Concatenation)));
      if not B in known then
        AddSet(known,B);
        B:=List(B,x->ImmutableMatrix(F,ASCH.Reshape(x,n)));
        ZB:=ASCH.CentreOfAlgebra(B,n,F);
        if Length(ZB)=1 then
          P:=ASCH.TensorBasisFromAlgebra(B,n,F);
          if P<>fail then
            k:=RootInt(Length(B),2);
            ok:=ForAll(gens,g->ASCH.KroneckerFactor(P*g*P^-1,k,n/k)<>fail);
            if ok then
              Add(res.tensor,rec(dims:=[k,n/k],basis:=P));
            fi;
          fi;
        else
          MZ:=ASCH.Module(ZB,n,F);
          comps:=ASCH.HomogeneousComponents(MZ);
          if Length(comps)>1 then
            if Length(res.blocks)=0 and Length(Set(comps,Length))=1 then
              Add(res.blocks,comps);
            fi;
          elif Length(res.fields)=0 then
            Add(res.fields,ZB);
          fi;
        fi;
      fi;
    fi;
  od;
  return res;
end;

# eigenvalues (with multiplicity) of g, or fail if the splitting field
# has more than limit elements
ASCH.Spectrum:=function(g,F,limit)
local pol,L,K,roots;
  pol:=CharacteristicPolynomial(F,F,g);
  L:=Lcm(List(Factors(PolynomialRing(F),pol),Degree));
  if Size(F)^L>limit then
    return fail;
  fi;
  K:=GF(Characteristic(F),DegreeOverPrimeField(F)*L);
  roots:=RootsOfUPol(K,pol);
  if Length(roots)<>Length(g) then
    return fail;
  fi;
  return roots;
end;

# is the multiset E the multiset of products of a multiset of size n1 and
# one of size n2? (Scaling allows to assume that 1 lies in the first one.)
ASCH.MultisetFactors:=function(E,n1,n2)
local rem,try,Y,combs;
  rem:=function(L,S)  # multiset difference, or fail if S not contained in L
  local l,s,p;
    l:=ShallowCopy(L);
    for s in S do
      p:=Position(l,s);
      if p=fail then
        return fail;
      fi;
      Remove(l,p);
    od;
    return l;
  end;
  try:=function(R,Y,k)
  local x,y,R2;
    if k=0 then
      return Length(R)=0;
    fi;
    for y in Set(Y) do
      x:=R[1]/y;
      R2:=rem(R,x*Y);
      if R2<>fail and try(R2,Y,k-1) then
        return true;
      fi;
    od;
    return false;
  end;
  combs:=Set(Combinations(E,n2));
  for Y in combs do
    if try(rem(E,Y),Y,n1-1) then
      return true;
    fi;
  od;
  return false;
end;

# Try to prove that G preserves no tensor decomposition with dimensions in
# dimslist, by finding elements whose spectrum does not factor. If squares
# is true, test squares of elements (for decompositions whose factors may
# be swapped). Returns true if all dimensions in dimslist were refuted.
ASCH.RefuteTensor:=function(G,n,F,dimslist,squares,tries)
local remaining,i,g,E,gens;
  remaining:=ShallowCopy(dimslist);
  gens:=GeneratorsOfGroup(G);
  for i in [1..tries] do
    if i<=Length(gens) then
      g:=gens[i];
    else
      g:=PseudoRandom(G);
    fi;
    if squares then
      g:=g^2;
    fi;
    E:=ASCH.Spectrum(g,F,2^16);
    if E<>fail then
      remaining:=Filtered(remaining,d->ASCH.MultisetFactors(E,d[1],d[2]));
      if Length(remaining)=0 then
        return true;
      fi;
    fi;
  od;
  return false;
end;

# permutation matrix swapping the two tensor factors of F^m (x) F^m
ASCH.SwapMat:=function(m,F)
local perm;
  perm:=PermList(List([0..m^2-1],x->(x mod m)*m+QuoInt(x,m)+1));
  return PermutationMat(perm,m^2,F);
end;

#############################################################################
##
##  C5
##

# the F0-span of the group generated by hgens, or fail if dim > n^2
ASCH.SubfieldSpan:=function(hgens,n,F,F0)
local B,flat,one,mb,basis,queue,b,h,c,v;
  B:=Basis(AsField(F0,F));
  flat:=m->Concatenation(List(Concatenation(m),x->Coefficients(B,x)));
  one:=IdentityMat(n,F);
  mb:=MutableBasis(F0,[flat(one)]);
  basis:=[one];
  queue:=[one];
  while Length(queue)>0 do
    b:=Remove(queue);
    for h in hgens do
      c:=b*h;
      v:=flat(c);
      if not IsContainedInSpan(mb,v) then
        CloseMutableBasis(mb,v);
        Add(basis,c);
        Add(queue,c);
        if Length(basis)>n^2 then
          return fail;
        fi;
      fi;
    od;
  od;
  return basis;
end;

# hgens generate an abs. irreducible group with all traces in F0.
# Return X with X*h*X^-1 in GL(n,F0).
ASCH.SubfieldConjugator:=function(hgens,n,F,F0)
local B,r,M0,bas,sub,X;
  B:=Basis(AsField(F0,F));
  r:=Length(B);
  M0:=ASCH.Module(List(hgens,h->BlownUpMat(B,h)),n*r,F0);
  bas:=IdentityMat(n*r,F0);
  while MTX.Dimension(M0)>n do
    sub:=TriangulizedMat(MTX.ProperSubmoduleBasis(M0));
    bas:=sub*bas;
    M0:=MTX.InducedActionSubmodule(M0,sub);
  od;
  X:=List(bas,w->List([1..n],i->w{[(i-1)*r+1..i*r]}*BasisVectors(B)));
  return ImmutableMatrix(F,X);
end;

ASCH.TestSubfieldQ0:=function(G,n,F,q0,newgens,zerotr,opt)
local q,F0,inF0,scaled,N,reps,cands,g,k,h,o,l,combos,combo,hgens,X,ok,
      mats,x,pos;
  q:=Size(F);
  F0:=GF(q0);
  inF0:=x->x^q0=x;
  scaled:=List(newgens,g->TraceMat(g)^-1*g);
  N:=(q-1)/(q0-1);
  reps:=List([0..N-1],i->Z(q)^i);
  cands:=[];
  for g in zerotr do
    o:=Order(g);
    k:=1;
    h:=g;
    while k<o and IsZero(TraceMat(h)) do
      k:=k+1;
      h:=h*g;
    od;
    if IsZero(TraceMat(h)) then
      Add(cands,reps);
    else
      Add(cands,Filtered(reps,c->inF0(c^k*TraceMat(h))));
    fi;
  od;
  if Product(List(cands,Length))>opt.cap then
    return fail;
  fi;
  if Length(cands)=0 then
    combos:=[[]];
  else
    combos:=Cartesian(cands);
  fi;
  for combo in combos do
    hgens:=Concatenation(scaled,
                         List([1..Length(zerotr)],i->combo[i]*zerotr[i]));
    if ASCH.SubfieldSpan(hgens,n,F,F0)<>fail then
      X:=ASCH.SubfieldConjugator(hgens,n,F,F0);
      # verify
      ok:=true;
      for g in ASCH.Gens(G) do
        x:=X*g*X^-1;
        pos:=PositionNonZero(x[1]);
        x:=x[1][pos]^-1*x;
        if not ForAll(x,r->ForAll(r,inF0)) then
          ok:=false;
        fi;
      od;
      if ok then
        return rec(subfield:=F0,conjugator:=X);
      fi;
      Error("subfield conjugator could not be verified -- this is a bug");
    fi;
  od;
  return false;
end;

ASCH.TestSubfield:=function(G,n,F,opt)
local p,e,gens,newgens,zerotr,g,w,found,i,dd,res,capped;
  p:=Characteristic(F);
  e:=DegreeOverPrimeField(F);
  if e=1 then
    return false;
  fi;
  gens:=ASCH.Gens(G);
  # try to get a generating set of elements with nonzero trace
  newgens:=[];
  zerotr:=[];
  for g in gens do
    if not IsZero(TraceMat(g)) then
      Add(newgens,g);
    else
      found:=false;
      for i in [1..30] do
        w:=PseudoRandom(G);
        if not IsZero(TraceMat(w)) and not IsZero(TraceMat(g*w)) then
          Add(newgens,w);
          Add(newgens,g*w);
          found:=true;
          break;
        fi;
      od;
      if not found then
        Add(zerotr,g);
      fi;
    fi;
  od;
  capped:=false;
  for dd in Filtered(DivisorsInt(e),x->x<e) do
    res:=ASCH.TestSubfieldQ0(G,n,F,p^dd,newgens,zerotr,opt);
    if res=fail then
      capped:=true;
    elif res<>false then
      return res;
    fi;
  od;
  if capped then
    return fail;
  fi;
  return false;
end;

#############################################################################
##
##  C6
##
ASCH.C6FieldOK:=function(n,r,q)
local p,e;
  p:=SmallestRootInt(q);
  e:=LogInt(q,p);
  if r<>2 then
    return e=OrderMod(p,r) and IsOddInt(e);
  elif n=2 then
    return e=1 and p<>2;
  else
    return e=1 and p mod 4=1;
  fi;
end;

ASCH.CheckR:=function(R,r,m,n,F)
local MR,Z,type;
  MR:=ASCH.Module(ASCH.Gens(R),n,F);
  if not MTX.IsAbsolutelyIrreducible(MR) then
    return fail;
  fi;
  Z:=Centre(R);
  if not ForAll(GeneratorsOfGroup(Z),
       z->IsDiagonalMat(z) and Length(Set(DiagonalOfMat(z)))=1) then
    return fail;
  fi;
  if Size(R)=r^(1+2*m) and Size(Z)=r and DerivedSubgroup(R)=Z
     and IsElementaryAbelian(R/Z) and Exponent(R) in [r,4] then
    if r=2 then
      if Size(Group(Filtered(AsList(R),x->Order(x)<=2)))=Size(R) then
        type:="extraspecial 2^(1+2m)_+";
      else
        type:="extraspecial 2^(1+2m)_-";
      fi;
    else
      type:="extraspecial of exponent r";
    fi;
    return type;
  elif r=2 and Size(R)=2^(2+2*m) and Size(Z)=4 and IsCyclic(Z)
     and IsElementaryAbelian(R/Z) and Size(DerivedSubgroup(R))=2 then
    return "symplectic type 4o2^(1+2m)";
  fi;
  return fail;
end;

ASCH.TestExtraspecial:=function(G,n,F)
local c,r,m,P,sizes,iso,Ppc,pcg,auts,sz,cands,C,R,type;
  c:=Collected(Factors(n));
  if n=1 or Length(c)<>1 then
    return false;
  fi;
  r:=c[1][1];
  m:=c[1][2];
  P:=PCore(G,r);
  if Size(P)<r^(1+2*m) then
    return false;
  fi;
  sizes:=[r^(1+2*m)];
  if r=2 then
    Add(sizes,2^(2+2*m));
  fi;
  iso:=IsomorphismPcGroup(P);
  Ppc:=Image(iso,P);
  pcg:=GeneratorsOfGroup(Ppc);
  auts:=List(ASCH.Gens(G),g->GroupHomomorphismByImagesNC(Ppc,Ppc,pcg,
         List(pcg,x->Image(iso,PreImagesRepresentative(iso,x)^g))));
  for sz in sizes do
    if Size(P) mod sz=0 then
      cands:=SubgroupsSolvableGroup(Ppc,rec(actions:=auts,normal:=true,
               consider:=ExactSizeConsiderFunction(sz)));
      for C in Filtered(cands,x->Size(x)=sz) do
        R:=Group(List(GeneratorsOfGroup(C),x->PreImagesRepresentative(iso,x)),
                 One(G));
        type:=ASCH.CheckR(R,r,m,n,F);
        if type<>fail then
          return rec(prime:=r,normalSubgroup:=R,type:=type);
        fi;
      od;
    fi;
  od;
  return false;
end;

#############################################################################
##
##  C8
##

# common eigenspaces (with eigenvalues in F) of commuting matrices
ASCH.CommonEigenspaces:=function(mats,F,dim)
local spaces,M,new,sp,B,R,ev,K;
  spaces:=[[IdentityMat(dim,F),[]]];
  for M in mats do
    new:=[];
    for sp in spaces do
      B:=sp[1];
      R:=List(B,b->SolutionMat(B,b*M));
      for ev in Set(RootsOfUPol(F,CharacteristicPolynomial(F,F,R))) do
        K:=NullspaceMat(R-ev*One(R));
        if Length(K)>0 then
          Add(new,[K*B,Concatenation(sp[2],[ev])]);
        fi;
      od;
    od;
    spaces:=new;
  od;
  return spaces;
end;

# spaces of forms B (flattened) with g*B*g' = lambda(g)*B, where the
# action on flattened forms is given by act(g). G' fixes such forms.
ASCH.InvariantFormSpaces:=function(gens,dgens,act,n,F)
local N,one,mats,fix,R;
  N:=n^2;
  one:=IdentityMat(N,F);
  if Length(dgens)=0 then
    fix:=one;
  else
    mats:=List(dgens,h->act(h)-one);
    fix:=NullspaceMat(List([1..N],i->Concatenation(List(mats,A->A[i]))));
  fi;
  if Length(fix)=0 then
    return [];
  fi;
  R:=List(gens,g->List(fix,b->SolutionMat(fix,b*act(g))));
  return List(ASCH.CommonEigenspaces(R,F,Length(fix)),
              x->[x[1]*fix,x[2]]);
end;

ASCH.IsSquare:=function(x,F)
  return IsZero(x) or LogFFE(x,PrimitiveRoot(F)) mod 2=0;
end;

ASCH.ArfInvariant:=function(Q,B,F)
local n,qf,bf,rem,arf,e,pos,f,a,v;
  n:=Length(B);
  qf:=v->v*Q*v;
  bf:=function(u,v) return u*B*v; end;
  rem:=List(IdentityMat(n,F),ShallowCopy);
  arf:=Zero(F);
  while Length(rem)>0 do
    e:=rem[1];
    pos:=PositionProperty(rem,x->not IsZero(bf(e,x)));
    f:=rem[pos]/bf(e,rem[pos]);
    arf:=arf+qf(e)*qf(f);
    rem:=rem{Difference([2..Length(rem)],[pos])};
    rem:=List(rem,v->v-bf(v,f)*e+bf(v,e)*f);
  od;
  return arf;
end;

# char 2: quadratic form polarising to B, preserved up to the multipliers
ASCH.QuadraticFormChar2:=function(gens,lambdas,B,n,F)
local cols,rhs,g,l,i,j,k,col,s,sol,Q;
  cols:=[];
  rhs:=[];
  for l in [1..Length(gens)] do
    g:=gens[l];
    for i in [1..n] do
      col:=List([1..n],j->g[i][j]^2);
      col[i]:=col[i]-lambdas[l];
      s:=Zero(F);
      for j in [1..n] do
        for k in [j+1..n] do
          s:=s+g[i][j]*g[i][k]*B[j][k];
        od;
      od;
      Add(cols,col);
      Add(rhs,-s);
    od;
  od;
  sol:=SolutionMat(TransposedMat(cols),rhs);
  if sol=fail then
    return fail;
  fi;
  Q:=List([1..n],i->List([1..n],function(j)
       if j<i then return Zero(F); elif j=i then return sol[i];
       else return B[i][j]; fi; end));
  return ImmutableMatrix(F,Q);
end;

ASCH.Multipliers:=function(gens,B,bar)
local l,g,x,pos;
  l:=[];
  for g in gens do
    x:=g*B*TransposedMat(bar(g));
    pos:=PositionNonZero(B[PositionProperty(B,r->not IsZero(r))]);
    Add(l,x[PositionProperty(B,r->not IsZero(r))][pos]/
          B[PositionProperty(B,r->not IsZero(r))][pos]);
  od;
  return l;
end;

ASCH.TestForms:=function(G,n,F)
local q,p,gens,dgens,res,act,spaces,sp,forms,sym,alt,B,lam,disc,Q,arf,
      e,q0,bar,herm,H,alpha,x;
  q:=Size(F);
  p:=Characteristic(F);
  gens:=ASCH.Gens(G);
  dgens:=ASCH.Gens(Group(SmallGeneratingSet(DerivedSubgroup(G)),One(G)));
  res:=rec();
  # bilinear forms
  act:=g->KroneckerProduct(TransposedMat(g),TransposedMat(g));
  spaces:=ASCH.InvariantFormSpaces(gens,dgens,act,n,F);
  for sp in spaces do
    forms:=List(sp[1],v->ASCH.Reshape(v,n));
    if p<>2 then
      sym:=Filtered(List(forms,x->x+TransposedMat(x)),x->not IsZero(x));
      alt:=Filtered(List(forms,x->x-TransposedMat(x)),x->not IsZero(x));
    else
      sym:=[];
      alt:=Filtered(List(forms,x->x+TransposedMat(x)),x->not IsZero(x));
      if Length(alt)=0 then
        # symmetric forms of irreducible groups are alternating
        alt:=Filtered(forms,x->ForAll([1..n],i->IsZero(x[i][i])));
      fi;
    fi;
    if Length(alt)>0 and n>2 and not IsBound(res.symplectic) then
      B:=ImmutableMatrix(F,alt[1]);
      if RankMat(B)=n then
        lam:=ASCH.Multipliers(gens,B,x->x);
        res.symplectic:=rec(form:=B,type:="symplectic",multipliers:=lam);
        if p=2 then
          Q:=ASCH.QuadraticFormChar2(gens,lam,B,n,F);
          if Q<>fail then
            res.symplectic.quadraticForm:=Q;
            arf:=ASCH.ArfInvariant(Q,B,F);
            e:=DegreeOverPrimeField(F);
            if IsZero(Sum([0..e-1],i->arf^(2^i))) then
              res.symplectic.quadraticFormSign:=1;
            else
              res.symplectic.quadraticFormSign:=-1;
            fi;
          fi;
        fi;
      fi;
    fi;
    if Length(sym)>0 and not IsBound(res.orthogonal) then
      B:=ImmutableMatrix(F,sym[1]);
      if RankMat(B)=n then
        lam:=ASCH.Multipliers(gens,B,x->x);
        res.orthogonal:=rec(form:=B,multipliers:=lam);
        if IsOddInt(n) then
          res.orthogonal.type:="orthogonal";
          res.orthogonal.sign:=0;
        else
          disc:=(-1)^(n/2)*DeterminantMat(B);
          if ASCH.IsSquare(disc,F) then
            res.orthogonal.type:="orthogonal plus";
            res.orthogonal.sign:=1;
          else
            res.orthogonal.type:="orthogonal minus";
            res.orthogonal.sign:=-1;
          fi;
        fi;
      fi;
    fi;
  od;
  # hermitian forms
  e:=DegreeOverPrimeField(F);
  if IsEvenInt(e) then
    q0:=p^(e/2);
    bar:=m->List(m,r->List(r,x->x^q0));
    act:=g->KroneckerProduct(TransposedMat(g),TransposedMat(bar(g)));
    spaces:=ASCH.InvariantFormSpaces(gens,dgens,act,n,F);
    if p=2 then
      alpha:=One(F);
    else
      alpha:=Z(q)^((q0+1)/2);
    fi;
    for sp in spaces do
      # B^bar' lies in the eigenspace for the conjugate multipliers, so a
      # hermitian form needs multipliers in GF(q0)
      if not IsBound(res.hermitian) and ForAll(sp[2],x->x^q0=x) then
        forms:=List(sp[1],v->ASCH.Reshape(v,n));
        B:=forms[1];
        H:=B+TransposedMat(bar(B));
        if IsZero(H) then
          H:=alpha*B;
        fi;
        H:=ImmutableMatrix(F,H);
        if RankMat(H)=n and H=TransposedMat(bar(H)) then
          res.hermitian:=rec(form:=H,subfield:=GF(q0),
                             multipliers:=ASCH.Multipliers(gens,H,bar));
        fi;
      fi;
    od;
  fi;
  # verify
  for x in ["symplectic","orthogonal","hermitian"] do
    if IsBound(res.(x)) then
      B:=res.(x).form;
      if x="hermitian" then
        bar:=m->List(m,r->List(r,y->y^q0));
      else
        bar:=m->m;
      fi;
      if not ForAll([1..Length(gens)],i->gens[i]*B*TransposedMat(bar(gens[i]))
                    =res.(x).multipliers[i]*B) then
        Error("form could not be verified -- this is a bug");
      fi;
    fi;
  od;
  return res;
end;

#############################################################################
##
##  main function
##
AschbacherClasses:=function(arg)
local G,F,opt,n,q,p,gens,res,M,absirr,d,imp,sem,tens,complete,K,Kres,Kok,
      sa,ZB,e,Y,s,
      MK,m,P,SW,g,x,ok,forms,c6,sub,addIn,addNot,addUnd,dec,Zc,hom,soc,
      lst,a;

  G:=arg[1];
  F:=DefaultFieldOfMatrixGroup(G);
  opt:=ShallowCopy(ASCH.DefaultOptions);
  for a in arg{[2..Length(arg)]} do
    if IsField(a) then
      F:=a;
    elif IsRecord(a) then
      for x in RecNames(a) do
        opt.(x):=a.(x);
      od;
    fi;
  od;
  n:=DimensionOfMatrixGroup(G);
  q:=Size(F);
  p:=Characteristic(F);
  gens:=List(ASCH.Gens(G),x->ImmutableMatrix(F,x));
  G:=Group(gens,ImmutableMatrix(F,One(G)));

  res:=rec(dimension:=n,field:=F,classes:=[],notInClasses:=[],undecided:=[],
           remarks:=[]);
  addIn:=function(c) AddSet(res.classes,c); end;
  addNot:=function(c) AddSet(res.notInClasses,c); end;
  addUnd:=function(c) AddSet(res.undecided,c); end;
  dec:=function(name,val,cert)
    if val=fail then
      addUnd(name);
    elif val=false then
      addNot(name);
    else
      addIn(name);
      res.(name):=cert;
    fi;
  end;

  if n=1 then
    Add(res.remarks,"dimension 1: Aschbacher classes are not defined");
    return res;
  fi;

  M:=ASCH.Module(gens,n,F);

  # C1
  if not MTX.IsIrreducible(M) then
    res.irreducible:=false;
    res.absolutelyIrreducible:=false;
    res.containsSL:=false;
    addIn("C1");
    res.C1:=rec(submodule:=ImmutableMatrix(F,MTX.ProperSubmoduleBasis(M)));
    for x in ["C2","C3","C4","C5","C6","C7","C8_1","C8_2"] do
      addUnd(x);
    od;
    Add(res.remarks,"group is reducible; only class C1 was examined");
    return res;
  fi;
  res.irreducible:=true;
  addNot("C1");
  absirr:=MTX.IsAbsolutelyIrreducible(M);
  res.absolutelyIrreducible:=absirr;
  if absirr then
    d:=1;
  else
    d:=ASCH.CentDegree(M,F);
  fi;

  ASCH.SetNiceMono(G,n,F,opt.niceLimit);

  # contains SL?
  res.containsSL:=Size(G) mod Size(SL(n,q))=0 and
                  ForAll(GeneratorsOfGroup(SL(n,q)),x->x in G);
  if res.containsSL then
    for x in ["C2","C3","C4","C5","C6","C7","C8_1","C8_2","S"] do
      addNot(x);
    od;
    Add(res.remarks,"group contains SL(n,q)");
    return res;
  fi;

  # invariant subalgebras of Mat(n,q): decide C2, C3 and find tensor
  # decompositions
  sa:=ASCH.InvariantSubalgebras(gens,n,F,opt);

  # C2
  if Length(sa.blocks)>0 then
    imp:=rec(blocks:=sa.blocks[1],t:=Length(sa.blocks[1]),
             m:=n/Length(sa.blocks[1]));
  elif not sa.capped then
    imp:=false;
  else
    imp:=ASCH.TestImprimitive(G,n,F,d,opt);
  fi;
  dec("C2",imp,imp);

  # C3
  if Length(sa.fields)>0 then
    ZB:=sa.fields[1];
    e:=Length(ZB);
    repeat
      Y:=Sum(ZB,z->Random(F)*z);
    until Degree(MinimalPolynomial(F,Y))=e;
    s:=Factors(e)[1];
    Y:=ASCH.SubfieldGenerator(Y,e,s,F);
    sem:=rec(degree:=s,fieldGenerator:=Y,
             centralizer:=Stabilizer(G,Y,function(x,g) return x^g; end));
  elif not sa.capped then
    sem:=false;
  else
    sem:=ASCH.TestSemilinear(G,n,F,M,absirr);
  fi;
  dec("C3",sem,sem);

  # C4 and C7 (t=2)
  res.tensorDecompositions:=[];
  if IsPrimeInt(n) then
    addNot("C4");
    addNot("C7");
  else
    tens:=rec(found:=sa.tensor);
    res.tensorDecompositions:=tens.found;
    complete:=absirr and imp=false and sem=false and not sa.capped;
    # C4
    lst:=Filtered(tens.found,x->x.dims[1]<>x.dims[2]);
    if Length(lst)>0 then
      dec("C4",true,lst[1]);
    elif not ForAny(DivisorsInt(n),x->1<x and x^2<n) then
      addNot("C4");
    elif complete then
      addNot("C4");
    elif ASCH.RefuteTensor(G,n,F,List(Filtered(DivisorsInt(n),x->1<x and
           x^2<n),x->[x,n/x]),false,opt.refuteTries) then
      addNot("C4");
      Add(res.remarks,Concatenation("C4 excluded by elements whose ",
        "spectrum is not a product of spectra of the factor dimensions"));
    else
      addUnd("C4");
    fi;
    # C7
    m:=RootInt(n,2);
    lst:=Filtered(tens.found,x->x.dims[1]=x.dims[2]);
    if m^2=n and Length(lst)>0 and m=2 then
      Add(res.remarks,Concatenation("tensor decomposition 2 (x) 2 found; ",
        "in Case L this lies in class C8 (orthogonal similarities)"));
    fi;
    if m^2=n and m>=3 and Length(lst)>0 then
      dec("C7",true,rec(m:=m,t:=2,basis:=lst[1].basis,swaps:=false));
    elif m^2=n and m>=3 then
      # factors may be swapped: kernel K of index 2 preserves both
      SW:=ASCH.SwapMat(m,F);
      Kok:=complete;
      for K in ASCH.PrimeIndexNormalSubgroups(G,2) do
        if not "C7" in res.classes then
          Kres:=ASCH.InvariantSubalgebras(
                  List(ASCH.Gens(K),x->ImmutableMatrix(F,x)),n,F,opt);
          for P in Filtered(Kres.tensor,x->x.dims[1]=x.dims[2]) do
            ok:=ForAll(gens,g->
                  ASCH.KroneckerFactor(P.basis*g*P.basis^-1,m,m)<>fail or
                  ASCH.KroneckerFactor(P.basis*g*P.basis^-1*SW,m,m)<>fail);
            if ok and not "C7" in res.classes then
              dec("C7",true,rec(m:=m,t:=2,basis:=P.basis,swaps:=true));
            fi;
          od;
          if not "C7" in res.classes and Kok then
            MK:=ASCH.Module(ASCH.Gens(K),n,F);
            # search for K complete if K abs. irreducible, primitive and
            # not semilinear
            Kok:=not Kres.capped and MTX.IsIrreducible(MK)
                 and MTX.IsAbsolutelyIrreducible(MK)
                 and Length(Kres.blocks)=0 and Length(Kres.fields)=0;
          fi;
        fi;
      od;
      if not "C7" in res.classes then
        if Kok then
          addNot("C7");
        elif ASCH.RefuteTensor(G,n,F,[[m,m]],true,opt.refuteTries) then
          addNot("C7");
          Add(res.remarks,Concatenation("C7 excluded by elements whose ",
            "squares have spectra that are not products of spectra"));
        else
          addUnd("C7");
        fi;
      fi;
    elif ForAny([3..n],x->n=x^LogInt(n,x) and LogInt(n,x)>=3) then
      Add(res.remarks,"C7 with t>=3 factors is not implemented");
      addUnd("C7");
    else
      addNot("C7");
    fi;
  fi;

  # C5
  if absirr then
    sub:=ASCH.TestSubfield(G,n,F,opt);
    dec("C5",sub,sub);
  else
    addNot("C5");
  fi;

  # C6
  if absirr then
    c6:=ASCH.TestExtraspecial(G,n,F);
    if c6<>false then
      c6.minimalField:=ASCH.C6FieldOK(n,c6.prime,q);
      res.extraspecialNormalSubgroup:=c6;
      if c6.minimalField then
        dec("C6",true,c6);
      else
        addNot("C6");
        Add(res.remarks,Concatenation("G has an absolutely irreducible ",
          "normal r-subgroup of extraspecial/symplectic type, but q does not ",
          "satisfy the conditions of Table 2.9 (so G is in C5 or C8)"));
      fi;
    else
      addNot("C6");
    fi;
  else
    addNot("C6");
  fi;

  # C8
  forms:=ASCH.TestForms(G,n,F);
  if IsBound(forms.symplectic) then
    dec("C8_1",true,forms.symplectic);
  elif IsBound(forms.orthogonal) then
    dec("C8_1",true,forms.orthogonal);
  else
    addNot("C8_1");
  fi;
  if IsBound(forms.symplectic) and IsBound(forms.orthogonal) then
    res.C8_1.otherForm:=forms.orthogonal;
  fi;
  if p=2 and IsBound(forms.symplectic) and
     IsBound(forms.symplectic.quadraticForm) then
    Add(res.remarks,Concatenation("G also preserves a quadratic form up to ",
      "scalars (see C8_1.quadraticForm); for q even this lies in Sp"));
  fi;
  if n=2 then
    Add(res.remarks,Concatenation("n=2: preserving an alternating form up ",
      "to scalars is automatic, so the symplectic type is not reported"));
  fi;
  if IsBound(forms.hermitian) then
    dec("C8_2",true,forms.hermitian);
  else
    addNot("C8_2");
  fi;

  # class S
  if Length(res.classes)=0 then
    if Length(res.undecided)=0 then
      addIn("S");
      Zc:=Centre(G);
      hom:=NaturalHomomorphismByNormalSubgroup(G,Zc);
      soc:=Socle(Image(hom,G));
      res.S:=rec(almostSimple:=IsSimpleGroup(soc) and not IsAbelian(soc),
                 socle:=soc);
      if not res.S.almostSimple then
        Error("G/Z(G) is not almost simple -- this contradicts ",
              "Aschbacher's theorem, so there is a bug");
      fi;
    else
      addUnd("S");
    fi;
  else
    addNot("S");
  fi;
  return res;
end;

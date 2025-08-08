# Functionality for arithmetic groups, based on papers by AD,DF,AH
ARITHVERSION:="1.15";
# April 2024

DeclareInfoClass("InfoArithSub");
SetInfoLevel(InfoArithSub,1);

#
if LoadPackage("matgrp")=fail then
  Error(
    "The ``matgrp'' package is required, but is currently not installed, or some of its dependencies\n",
    "(recog,recogbase,genss,forms,orb,io) have not been installed or (orb,io) not been compiled.");
fi;

Print("Arithmetic group routines, Version ",ARITHVERSION,", Alexander Hulpke\n");

PrintToGlobals:=function(file,l)
local i;
  if Length(Intersection(["file","i","l"],l))>0 then Error("variable names");fi;
  PrintTo(file,"# Global Variable save ",l,"\n");
  for i in l do
    AppendTo(file,i,":=",EvalString(i));
    AppendTo(file,";\n");
    if IsGroup(EvalString(i)) and HasSize(EvalString(i))
     and IsFinite(EvalString(i)) then
      AppendTo(file,"SetSize(i,",Size(EvalString(i)),");\n");
    fi;
  od;
end;

MyListString:=function(l)
local s,i,q,first;
  s:="[";
  first:=true;
  for i in l do
    if first then first:=false;
    else Add(s,',');fi;
    Add(s,' ');
    if IsRat(i) then Append(s,String(i));
    else
      q:=Quadratic(i,true);
      if q=fail then
        Append(s,String(i));
      else
        Append(s,q.display);
      fi;
    fi;
  od;
  Append(s," ]");
  return s;
end;

SmallerGensetFpSub:=function(u)
local p,gens,sel,i,v,t;
  p:=Parent(u);
  gens:=GeneratorsOfGroup(u);
  for i in [Length(gens),Length(gens)-1..1] do
    sel:=gens{Difference([1..Length(gens)],[i])};
    v:=Subgroup(p,sel);
    t:=TryCosetTableInWholeGroup(v:silent:=true);
    if t<>fail and Length(t[1])=IndexInWholeGroup(u) then
      Print("Elim ",i,":",gens[i],"\n");
      gens:=sel;
    fi;
  od;
  return gens;
end;

# Part 0: Number Theory

Char0ScalarDomainMatrixList:=function(L)
local den,i,I,F,c;
  L:=Set(Filtered(Flat(L),x->not IsInt(x)));
  den:=1;
  for i in Filtered(L,IsRat) do
    den:=Lcm(den,DenominatorRat(i));
  od;
  L:=Filtered(L,x->not IsRat(L));
  if Length(L)=0 then
    if den=1 then
      return [Integers,1];
    else
      return [Rationals,1];
    fi;
  fi;
  I:=[];
  F:=Rationals;
  for i in L do
    c:=CoefficientsOfUnivariatePolynomial(MinimalPolynomial(Rationals,i));
    while not ForAll(c,IsInt) do
      c:=First(Reversed(c),x->not IsInt(x));
      c:=DenominatorRat(c);
      den:=Lcm(den,c);
      i:=i*c;
      c:=CoefficientsOfUnivariatePolynomial(MinimalPolynomial(Rationals,i));
    od;
    if not i in F then
      Add(I,i);
      F:=Field(I);
    fi;
  od;
  return [F,den];
end;

AllIntcoeffs:=function(c)
  return c<>fail and ForAll(c,IsInt);
end;

#Discriminant of a lattice: det (Tr(e_i,e_j))
MyDiscriminantOfLattice:=function(lat)
local d;
  if Length(lat)=Length(lat[1]) then
    d:=DeterminantMat(lat);
    if d<>0 then
      # use that [Tr(e_i,e_j)]=lat*TransposedMat(lat), thus it is Det(lat)^2
      return d^2;
    fi;
  elif Length(lat)<Length(lat[1]) then
    d:=lat*TransposedMat(lat);
    return DeterminantMat(d);
  else
    d:=TransposedMat(lat)*lat;
    return DeterminantMat(d);
  fi;
end;

# euclideanAlgorithm for Norm euclidean
NormEuclideanAlgorithm:=function(red,a,b)
local u,v,w,q,r,NI;

  NI:=function(q)
  local r;
    q:=Coefficients(red.bas,q);
    if red.eucl=1 then
      q:=List(q,RoundCyc);
      q:=q*red.bas;
    elif red.eucl=2 then
      # recode in std base
      q:=[q[1]+q[2]/2,q[2]/2];
      r:=RoundCyc(2*q[2]);
      q:=[RoundCyc(q[1]-r/2),r];
      q:=q*red.bas;
    else
      Error("not usable");
    fi;
    return q;
  end;

  u:=a;
  v:=b;
  while not IsZero(v) do
    #v := EuclideanRemainder( R, u, v );
    q:=u/v;
    w:=u-NI(q)*v;
    if AbsInt(Norm(red.field,w))>=AbsInt(Norm(red.field,v)) then
      return fail;
      Error("not smaller");
    fi;
    u:=v;
    v:=w;
  od;
  return u;
end;

IntegerFactorsOver:=function(a,set)
local s;
  while a>1 do
    s:=First(set,x->a mod x =0);
    if s=fail then return false;fi;
    a:=a/s;
  od;
  return true;
end;

ZIdealBasis:=function(bas,ringgens,idgens)
local gens,m,i,j,addtest,denom;

  denom:=ValueOption("denom");
  if denom=fail then
    denom:=[];
  fi;
  addtest:=function(a)
  local c,s,den;
    c:=Coefficients(bas,a);
    if not ForAll(c,x->DenominatorRat(x)=1
      or ForAll(Factors(DenominatorRat(x)),y->y in denom)) then 
      Error("not Z basis");
    fi;
    if Length(m)=0 then
      Add(gens,a);
      Add(m,c);
    else
      s:=SolutionMat(m,c);
      if s=fail or not ForAll(s,x->DenominatorRat(x)=1 or
          IntegerFactorsOver(DenominatorRat(x),denom)) then 
#if s<>fail then Error("EEE");fi;
        Add(gens,a);
        Add(m,c);
#Print("\n\na:",m," ",DeterminantMat(m*TransposedMat(m)),"\n\n");
        #m:=LLLReducedBasis(m).basis; # reduce coeffs
        den:=1;
        for i in Flat(m) do
          den:=Lcm(den,DenominatorRat(i));
        od;

        if den=1 then
          m:=Filtered(HermiteNormalFormIntegerMat(m),x->not IsZero(x));
        else
Print("den=",den,"\n");
          m:=m*den;
          m:=Filtered(HermiteNormalFormIntegerMat(m),x->not IsZero(x));
          m:=m/den;
        fi;

#Print("\n\nb:",m," ",DeterminantMat(m*TransposedMat(m)),"\n\n");
      fi;
    fi;

  end;

  gens:=[];
  m:=[];
  # generators
  for i in idgens do
    addtest(i);
  od;


  # close under ring action
  for i in gens do
    for j in ringgens do
      addtest(i*j);
    od;
  od;

  # close under multiplication (if not done before)
  for i in gens do
    for j in gens do
      addtest(i*j);
    od;
  od;
  return rec(gens:=gens,mgens:=List(m,x->x*bas),mat:=m);
end;


# single generator in quadratic PID -- somewhat hack
QuadSingleIdealGen:=function(id,red)
local nid,sum,i,j,sgn,t,fa,common,bas;
  bas:=red.bas;
  # first try LLL
  j:=List(id,x->Coefficients(bas,x));
  j:=LLLReducedBasis(j).basis;
  for i in j do
    t:=i*bas;
    if AllIntcoeffs(Coefficients(bas,id[1]/t))
          and AllIntcoeffs(Coefficients(bas,id[2]/t)) then
#Print("found:",i,"\n");
      return t;
    fi;
  od;

  # short Vectors
  fa:=10;
  fa:=Minimum(List(j,x->x*x));
  j:=List(id,x->Reversed(Coefficients(bas,x)));
  j:=Filtered(HermiteNormalFormIntegerMat(j),x->not IsZero(x));
  j:=List(j,Reversed);

  repeat
    fa:=fa*10;
    sgn:=ShortestVectors(j*TransposedMat(j),fa).vectors;
    for i in sgn do
      t:=i*j*bas;
      if AllIntcoeffs(Coefficients(bas,id[1]/t))
            and AllIntcoeffs(Coefficients(bas,id[2]/t)) then
        return t;
      fi;
    od;
  until Length(sgn)>10^4;

  # now take primes we get from the norm
  nid:=List(j,x->x*bas);
  fa:= Gcd(List(nid,x->Norm(Field(x),x)));
  fa:=Filtered(Set(PartialFactorization(fa)),x->x<=10^100 and IsPrimeInt(x));
  common:=[];
  for i in fa do
    for j in red.primesinnumber(i) do
      while ForAll(nid,x->AllIntcoeffs(Coefficients(bas,x/j))) do
        Add(common,j);
        nid:=List(nid,x->x/j);
      od;
    od;
  od;

  if Length(common)>0 then
    fa:=Product(common); # already known common factors
    sgn:=Gcd(List(nid,x->Norm(Field(x),x)));
    j:=QuadSingleIdealGen(Concatenation([sgn],nid),red);
    if IsList(j) and j[1]=fail then return [fail,j[2]*fa];fi;
    return j*fa;
  else
    return [fail,Gcd(List(nid,x->Norm(Field(x),x)))];
  fi;

  Error("UUU");

  for sum in [1..Maximum(id[1],10000)] do
    for i in [0..sum] do
      for sgn in [1,-1] do
        j:=sum-i;
        t:=sgn*i*id[1]+j*id[2];
        if ForAll(id,x->AllIntcoeffs(Coefficients(bas,x/t))) then
#Print("found",[i,j],"\n");
          return t;
        fi;
      od;
    od;
  od;
  Error("not found");
end;

# Fundamental unit of Q(sqrt(D)), Cohen Alg. 5.7.2
FundUnitQuadratic:=function(D)
local d,u,v,u1,v1,u2,v2,p,b,t,A,q;
  if D<0 then return fail;fi;
  d:=RootInt(D);
  if (D-d) mod 2=0 then b:=d;else b:=d-1;fi;
  u1:=-b;u2:=2;v1:=1;v2:=0;p:=b;q:=2;
  repeat
    A:=Int((p+d)/q);
    t:=p;
    p:=A*q-p;
    if t=p and v2<>0 then
      # Even Period
      u:=AbsInt((u2^2+v2^2*D)/q);
      v:=AbsInt(2*u2*v2/q);
      return (u+v*ER(D))/2;
    else
      t:=A*u2+u1;u1:=u2;u2:=t;
      t:=A*v2+v1;v1:=v2;v2:=t;t:=q;q:=(D-p^2)/q;
      if q=t and v2<>0 then
         #Odd period
         u:=AbsInt((u1*u2+D*v1*v2)/q);
         v:=AbsInt((u1*v2+u2*v1)/q);
         return (u+v*ER(D))/2;
      fi;
    fi;
  until false;
end;



#############################################################################
##
#F  LLLReducedBasis( [<L>, ]<vectors>[, <y>][, \"linearcomb\"][, <lllout>] )
##
MyLLLReducedBasis:=function( arg )
      local mmue,      # buffer $\mue$
            L,         # the lattice
            y,         # sensitivity $y$ (default $y = \frac{3}{4}$)
            kmax,      # $k_{max}$
            b,         # list $b$ of vectors
            H,         # basechange matrix $H$
            mue,       # matrix $\mue$ of scalar products
            B,         # list $B$ of norms of $b^{\ast}$
            BB,        # buffer $B$
            q,         # buffer $q$ for function `RED'
            i,         # loop variable $i$
            j,         # loop variable $j$
            k,         # loop variable $k$
            l,         # loop variable $l$
            n,         # number of vectors in $b$
            lc,        # boolean: option `linearcomb'?
            lllout,    # record with info about initial part of $b$
            scpr,      # scalar product of lattice `L'
            RED,       # reduction subprocedure; `RED( l )'
                       # means `RED( k, l )' in Cohen's book
            r;         # number of zero vectors found up to now

    RED := function( l )

    # Terminate for $\|\mue_{k,l}\| \leq \frac{1}{2}$.
    if 1 < mue[k][l] * 2 or mue[k][l] * 2 < -1 then

      # Let $q = `Round( mue[k][l] )'$ (is never zero), \ldots
#T Round ?
      q:= Int( mue[k][l] );
      if AbsoluteValue( mue[k][l] - q ) * 2 > 1 then
        q:= q + SignInt( mue[k][l] );
      fi;

      # \ldots and subtract $q b_l$ from $b_k$;
      AddRowVector( b[k], b[l], - q );

      # adjust `mue', \ldots
      mue[k][l]:= mue[k][l] - q;
      for i in [ r+1 .. l-1 ] do
        if mue[l][i] <> 0 then
          mue[k][i]:= mue[k][i] - q * mue[l][i];
        fi;
      od;

      # \ldots and the basechange.
      if lc then
        AddRowVector( H[k], H[l], - q );
      fi;

    fi;
    end;


    # Check the input parameters.
    if   IsLeftModule( arg[1] ) then
      L:= arg[1];
      scpr:= ScalarProduct;
      arg:= arg{ [ 2 .. Length( arg ) ] };
    elif IsFunction(arg[1]) then
      L:= "L";
      scpr:=arg[1];
      arg:= arg{ [ 2 .. Length( arg ) ] };
    elif IsList( arg[1] ) then
      # There is no lattice given, take standard scalar product.
      L:= "L";
      scpr:= StandardScalarProduct;
    else
      Error( "usage: LLLReducedBasis( [<L>], <vectors> [,<y>]",
             "[,\"linearcomb\"] )" );
    fi;

    b:= List( arg[1], ShallowCopy );

    # Preset the ``sensitivity'' (value between $\frac{1}{4}$ and $1$).
    if IsBound( arg[2] ) and IsRat( arg[2] ) then
      y:= arg[2];
      if y <= 1/4 or 1 < y then
        Error( "sensitivity `y' must satisfy 1/4 < y <= 1" );
      fi;
    else
      y:= 3/4;
    fi;

    # Get the optional `\"linearcomb\"' parameter
    # and the optional `lllout' record.
    lc     := false;
    lllout := false;

    for i in [ 2 .. Length( arg ) ] do
      if arg[i] = "linearcomb" then
        lc:= true;
      elif IsRecord( arg[i] ) then
        lllout:= arg[i];
      fi;
    od;


    # step 1 (Initialize.)
    n := Length( b );
    r := 0;
    i := 1;
    if lc then
      H:= IdentityMat( n );
    fi;

    if lllout = false or lllout.B = [] then

      k    := 2;
      mue  := [ [] ];
      kmax := 1;

      # Handle the case of leading zero vectors in the input.
      while i <= n and IsZero( b[i] ) do
        i:= i+1;
      od;
      if n < i then

        r:= n;
        k:= n+1;

      elif 1 < i then

        q    := b[i];
        b[i] := b[1];
        b[1] := q;
        if lc then
          q    := H[i];
          H[i] := H[1];
          H[1] := q;
        fi;

      fi;

      if 0 < n then
        B:= [ scpr( L, b[1], b[1] ) ];
      else
        B:= [];
      fi;

      Info( InfoZLattice, 1,
            "LLLReducedBasis called with ", n, " vectors, y = ", y );

    else

      # Note that the first $k_{max}$ vectors are all nonzero.

      mue  := List( lllout.mue, ShallowCopy );
      kmax := Length( mue );
      k    := kmax + 1;
      B    := ShallowCopy( lllout.B );

      Info( InfoZLattice, 1,
            "LLLReducedBasis (incr.) called with ",
            n, " = ", kmax, " + ", n - kmax, " vectors, y = ", y );

    fi;

    while k <= n do

      # step 2 (Incremental Gram-Schmidt)

      # If $k \leq k_{max}$ go to step 3.
      # Otherwise \ldots
      if kmax < k then

        Info( InfoZLattice, 2,
              "LLLReducedBasis: Take ", Ordinal( k ), " vector" );

        # \ldots set $k_{max} \leftarrow k$
        # and for $j = 1, \ldots, k-1$ set
        # $\mue_{k,j} \leftarrow b_k \cdot b_j^{\ast} / B_j$ if
        # $B_j \not= 0$ and $\mue_{k,j} \leftarrow 0$ if $B_j = 0$, \ldots
        kmax:= k;
        mue[k]:= [];
        for j in [ r+1 .. k-1 ] do
          mmue:= scpr( L, b[k], b[j] );
          for i in [ r+1 .. j-1 ] do
            mmue:= mmue - mue[j][i] * mue[k][i];
          od;
          mue[k][j]:= mmue;
        od;

        # (Now `mue[k][j]' contains $\mue_{k,j} B_j$ for all $j$.)
        for j in [ r+1 .. k-1 ] do
          mue[k][j]:= mue[k][j] / B[j];
        od;

        # \ldots then set $b_k^{\ast} \leftarrow
        # b_k - \sum_{j=1}^{k-1} \mue_{k,j} b_j^{\ast}$ and
        # $B_k \leftarrow b_k^{\ast} \cdot b_k^{\ast}$.
        B[k]:= scpr( L, b[k], b[k] );
        for j in [ r+1 .. k-1 ] do
          B[k]:= B[k] - mue[k][j]^2 * B[j];
        od;

      fi;

      # step 3 (Test LLL condition)
      RED( k-1 );
      while B[k] < ( y - mue[k][k-1] * mue[k][k-1] ) * B[k-1] do

        # Execute Sub-algorithm SWAPG$( k )$\:
        # Exchange the vectors $b_k$ and $b_{k-1}$,
        q      := b[k];
        b[k]   := b[k-1];
        b[k-1] := q;

        # $H_k$ and $H_{k-1}$,
        if lc then
          q      := H[k];
          H[k]   := H[k-1];
          H[k-1] := q;
        fi;

        # and if $k > 2$, for all $j$ such that $1 \leq j \leq k-2$
        # exchange $\mue_{k,j}$ with $\mue_{k-1,j}$.
        for j in [ r+1 .. k-2 ] do
          q           := mue[k][j];
          mue[k][j]   := mue[k-1][j];
          mue[k-1][j] := q;
        od;

        # Then set $\mue \leftarrow \mue_{k,k-1}$
        mmue:= mue[k][k-1];

        # and $B \leftarrow B_k + \mue^2 B_{k-1}$.
        BB:= B[k] + mmue^2 * B[k-1];

        # Now, in the case $B = 0$ (i.e. $B_k = \mue = 0$),
        if BB = 0 then

          # exchange $B_k$ and $B_{k-1}$
          B[k]   := B[k-1];
          B[k-1] := 0;

          # and for $i = k+1, k+2, \ldots, k_{max}$
          # exchange $\mue_{i,k}$ and $\mue_{i,k-1}$.
          for i in [ k+1 .. kmax ] do
            q           := mue[i][k];
            mue[i][k]   := mue[i][k-1];
            mue[i][k-1] := q;
          od;

        # In the case $B_k = 0$ and $\mue \not= 0$,
        elif B[k] = 0 and mmue <> 0 then

          # set $B_{k-1} \leftarrow B$,
          B[k-1]:= BB;

          # $\mue_{k,k-1} \leftarrow \frac{1}{\mue}
          mue[k][k-1]:= 1 / mmue;

          # and for $i = k+1, k+2, \ldots, k_{max}$
          # set $\mue_{i,k-1} \leftarrow \mue_{i,k-1} / \mue$.
          for i in [ k+1 .. kmax ] do
            mue[i][k-1]:= mue[i][k-1] / mmue;
          od;

        else

          # Finally, in the case $B_k \not= 0$,
          # set (in this order) $t \leftarrow B_{k-1} / B$,
          q:= B[k-1] / BB;

          # $\mue_{k,k-1} \leftarrow \mue t$,
          mue[k][k-1]:= mmue * q;

          # $B_k \leftarrow B_k t$,
          B[k]:= B[k] * q;

          # $B_{k-1} \leftarrow B$,
          B[k-1]:= BB;

          # then for $i = k+1, k+2, \ldots, k_{max}$ set
          # (in this order) $t \leftarrow \mue_{i,k}$,
          # $\mue_{i,k} \leftarrow \mue_{i,k-1} - \mue t$,
          # $\mue_{i,k-1} \leftarrow t + \mue_{k,k-1} \mue_{i,k}$.
          for i in [ k+1 .. kmax ] do
            q           := mue[i][k];
            mue[i][k]   := mue[i][k-1] - mmue * q;
            mue[i][k-1] := q + mue[k][k-1] * mue[i][k];
          od;

        fi;

        # Terminate the subalgorithm.

        if k > 2 then k:= k-1; fi;

        # Here we have always `k > r' since the loop is entered
        # for `k > r+1' only (because of `B[k-1] \<> 0'),
        # so the only problem might be the case `k = r+1',
        # namely `mue[ r+1 ][r]' is used then; but this is bound
        # provided that the initial list of vectors did not start
        # with zero vectors, and its (perhaps not updated) value
        # does not matter because this would mean just to subtract
        # a multiple of a zero vector.

        RED( k-1 );

      od;

      if B[ r+1 ] = 0 then
        r:= r+1;
        Unbind( b[r] );
      fi;

      for l in [ k-2, k-3 .. r+1 ] do
        RED( l );
      od;
      k:= k+1;

    # step 4 (Finished?)
    # If $k \leq n$ go to step 2.

    od;

    # Otherwise, let $r$ be the number of initial vectors $b_i$
    # which are equal to zero, output $p \leftarrow n - r$,
    # the vectors $b_i$ for $r+1 \leq i \leq n$ (which form an LLL-reduced
    # basis of $L$), the transformation matrix $H \in GL_n(\Z)$
    # and terminate the algorithm.

    # Check whether the last calls of `RED' have produced new zero vectors
    # in `b'; unfortunately this cannot be read off from `B'.
    while r < n and IsZero( b[ r+1 ] ) do
#T if this happens then is `B' outdated???
#T but `B' contains the norms of the orthogonal basis,
#T so this should be impossible!
#T (but if it happens then also `LLLReducedGramMat' should be adjusted!)
Print( "reached special case of increasing r in the last moment\n" );
if B[r+1] <> 0 then
  Print( "strange situation in LLL!\n" );
fi;
      r:= r+1;
    od;

    Info( InfoZLattice, 1,
          "LLLReducedBasis returns basis of length ", n-r );

    mue:= List( [ r+1 .. n ], i -> mue[i]{ [ r+1 .. i-1 ] } );
    MakeImmutable( mue );
    B:= B{ [ r+1 .. n ] };
    MakeImmutable( B );

    if lc then
      return rec( basis          := b{ [ r+1 .. n ] },
                  relations      := H{ [  1  .. r ] },
                  transformation := H{ [ r+1 .. n ] },
                  mue            := mue,
                  B              := B );
    else
      return rec( basis          := b{ [ r+1 .. n ] },
                  mue            := mue,
                  B              := B );
    fi;

end;



MyHNF:=function(mat,red)
local i,a,b,c,p,q,s,bas,l,split,quot,ni,adda,lno,intred,intered,denfactor,pivot;

  bas:=red.bas;

  # are there pesky denominators?
  a:=List(Union(List(Set(Flat(mat)),x->Coefficients(bas,x))),DenominatorRat);
  denfactor:=Lcm(a);
  if denfactor<>1 then mat:=mat*denfactor;fi;

  intered:=function(list,reducewith)
  local i,split,sub,idx;

    list:=List(list,x->Concatenation(List(x,y->Coefficients(bas,y))));

    list:=Filtered(reducewith(list),x->not IsZero(x));
    i:=Length(bas);

    split:=List([1,1+i..Length(list[1])-i+1],x->[x..x+i-1]);
    for i in split do
      # avoid too biased 1+big*Root entries, even out
      idx:=Filtered([1..Length(list)],x->PositionNonZero(list[x]) in i);
      sub:=list{idx}{i};
      if ForAny(sub,x->x[1]=1 and ForAll([2..Length(i)],j->x[j]=0)) then
        # Element 1 will reduce the rest.
        #Print("ONE!\n");
      elif Length(idx)>0 and Maximum(Flat(sub))-Minimum(Flat(sub))>10^5 then
        list{idx}:=MyLLLReducedBasis(function(s,x,y) return x{i}*y{i};end,list{idx}).basis;
      fi;
    od;
    list:=List(list,x->List(split,y->x{y}*bas));
    return list;
  end;

  l:=Filtered(mat,x->not IsZero(x));
  a:=ShallowCopy(l);

  # also multiples with basis to ensure we get full dimension before initial
  # Z-reduction
  for i in Filtered(bas,x->not IsRat(x)) do
    Append(l,a*i);
  od;
  l:=intered(l,HermiteNormalFormIntegerMat); #Z-reduction

  pivot:=List([1..Length(l[1])],x->fail);
  adda:=function(v)
  local i,p;
    Add(a,v);
    p:=PositionNonZero(v);
    pivot[p]:=Length(a);
  end;

  # now reduce the O-dependents

  # unit pivot
  a:=[];
  b:=[];
  c:=[];
  lno:=List(l,x->AbsInt(Norm(red.field,x[PositionNonZero(x)])));
  while Length(l)>0 do

    # are there too many short at end, if so Z-reduce again
    if (Length(l[1])-Minimum(List(l,PositionNonZero))+5)*Length(bas)<Length(l) then
      #Print("intermediate Z-reduction at depth ", Minimum(List(l,PositionNonZero)),"\n");
      l:=intered(l,HermiteNormalFormIntegerMat);
      lno:=List(l,x->AbsInt(Norm(red.field,x[PositionNonZero(x)])));
    fi;

    # take smallest pivot value
    p:=Position(lno,Minimum(lno));
#Print(p," : ",
#Length(l),List(l,PositionNonZero),List(a,PositionNonZero),List(b,PositionNonZero),"\n");
    i:=l[p];
    q:=Difference([1..Length(l)],[p]);
    l:=l{q};
    lno:=lno{q};

#rest:=l{[Position(l,i)+1..Length(l)]};
#    Print("neti\n");
#    while not IsZero(i) do

      p:=PositionNonZero(i);
      if not ForAll(Coefficients(bas,i[p]),IsInt) then
        Error("non integer coeff");
      elif pivot[p]<>fail then
        i:=i-i[p]*a[pivot[p]];
        if not IsZero(i) then
          Add(l,i);
          Add(lno,AbsInt(Norm(red.field,i[PositionNonZero(i)])));
        fi;
      elif ForAll(Coefficients(bas,i[p]^-1),IsInt) then
        # unit pivot
        i:=1/i[p]*i;
        adda(i);
        i:=0*i;
      else
        q:=PositionProperty(b,x->PositionNonZero(x)=p);
        if q=fail then
          Add(b,i);
          i:=i*0;
        elif IsBound(red.gcdexfun) then
          quot:=red.gcdexfun(i[p],b[q][p]); 
          s:=quot[2]*i+quot[3]*b[q];
          i:=quot[4]*i+quot[5]*b[q];
          if i[p]<>0 then Error("not zeroed out");fi;
          if ForAll(Coefficients(red.bas,s[p]^-1),IsInt) then
            # unit, move result to a
            s:=1/s[p]*s;
            adda(s);
            b:=b{Difference([1..Length(b)],[q])};
          else
            # new, smaller. Replace
            b[q]:=s;
          fi;
          if not IsZero(i) then
            Add(l,i);
            Add(lno,AbsInt(Norm(red.field,i[PositionNonZero(i)])));
          fi;
        else
Error("TRY CASE");
#          Print("p:",LogInt(AbsInt(Norm(i[p])),10)," ",
#            LogInt(AbsInt(Norm(b[q][p])),10),"\n");

          # rounded quotient
          quot:=i[p]/b[q][p];
          quot:=List(Coefficients(red.bas,quot),x->Int(x+1/2))*red.bas;
          if Norm(i[p]-quot*b[q][p])<Norm(i[p]) then
            i:=i-quot*b[q];
          elif Norm(i[p])<Norm(b[q][p]) then
            # swap, to make the norm smaller
            s:=b[q];
            b[q]:=i;
            i:=s;
          else
            Add(c,i);
            i:=0*i;
          fi;
        fi;
      fi;
#Print(Length(a)," ",Length(b)," ",Length(c)," ",
#RankMat(Concatenation(a,b,c,[i],rest)), "\n");
#    od;
  od;
  a:=Concatenation(a,b,c);
  SortBy(a,PositionNonZero);
  if denfactor<>1 then
    a:=1/denfactor*a;
  fi;
  return a;
  return Reversed(Set(Concatenation(a,b,c)));
end;

RoundedRat:=function(r)
local a,s;
  if r<0 then
    a:=-r;
    s:=-1;
  else 
    a:=r;
    s:=1;
  fi;
  return s*Int(a+1/2);
end;

NormGcdex:=function(red,oa,ob)
local a,b,na,nb,q,c,r,nr,car,i,os,s,ot,t,print,prev;
  a:=oa;
  b:=ob;
  os:=1;s:=0;
  ot:=0;t:=1;

  na:=AbsInt(Norm(red.field,a));
  nb:=AbsInt(Norm(red.field,b));
  prev:=LogInt(nb,10)-100;
  print:=prev>5000;

  while b<>0 do
    if print then
      c:=LogInt(nb,10);
      if c<prev then
        Print("NormGcdex ",c," digits\n");fi;
        prev:=Maximum(0,c-100);
      fi;
    q:=a/b;
    c:=List(Coefficients(red.bas,q),RoundedRat);
    q:=c*red.bas;
    r:=a-q*b;
    nr:=AbsInt(Norm(red.field,r));
    if nr>=nb then
      car:=Tuples([-1..1],2)+c;
      i:=1;
      q:=fail;
      while i<=Length(car) and q=fail do
        q:=car[i]*red.bas;
        r:=a-q*b;
        nr:=AbsInt(Norm(red.field,r));
        if not nr<nb then
          q:=fail;
        fi;
        i:=i+1;
      od;
      if q=fail then Error("Norm not smaller");fi;
    fi;
    a:=b;
    na:=nb;
    b:=r;
    nb:=nr;
    #(old_s, s) := (s, old_s − quotient × s)
    i:=s;
    s:=os-q*s;
    os:=i;
    #(old_t, t) := (t, old_t − quotient × t)
    i:=t;
    t:=ot-q*t;
    ot:=i;
  od;

  return [a,os,ot,s,t];

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
    a:=Set(Factors(AbsInt(a)));
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
    elif ring=NF(7,[ 1, 6 ]) then
      # Q(E(7)+E(7)^-1)
      a:=E(7)+E(7)^-1;
      d.bas:=Basis(ring,[1,a,a^2]);
      basimg:=a->[a^0,a,a^2];
      d.omega:=a;
      d.minpol:=MinimalPolynomial(Rationals,d.bas[2]);

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
                    return Coefficients(d.bas,elm)*a; # linear comb
                  end;

    d.doprimedeco:=function(p)
    local pol,l,i,m,a,r,it,ig,im,elm,co;

      if p=1 then return [p];fi;
      pol:=PolynomialModP(d.minpol,p);
      l:=[];
      for i in Collected(Factors(pol)) do
        m:=i[1];
        a:=RootsOfUPol(GF(p^DegreeOfLaurentPolynomial(m)),m)[1];
        a:=basimg(a); # basis images, given that minpol is for bas[2]
        if i[2]=1 then r:=0; else r:=i[2];fi;
        r:=rec(p:=p,deg:=DegreeOfLaurentPolynomial(m),ramify:=r,
          fieldsize:=p^DegreeOfLaurentPolynomial(m),
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

    # BAD, does not work
    d.gcdexfun:=function(a,b)
      return NormGcdex(d,a,b);
    end;

  else
    Error("not yet done");
  fi;

  return d;








  Error("old code");

#  if ring=Integers or ring=Rationals then
#    d.case:=1; # integers
#    d.discriminant:=1;
#    d.makereductionfunc:=function(prime)
#    local one,pos;
#      pos:=Position(d.moduli,prime);
#      if pos=fail then Add(d.moduli,prime); pos:=Length(d.moduli); fi;
#      if not IsBound(d.redfuns[pos]) then
#        one:=One(Integers mod prime);
#        d.redfuns[pos]:=a->a*one;
#      fi;
#      return d.redfuns[pos];
#    end;
#
#    d.convertparam:=prime->prime;
#
#    d.bas:=[1];
#
#    d.makeliftfunc:=function(prime)
#      return Int;
#    end;
#    d.denominatorfun:=DenominatorRat;
#    d.factorsinnumbers:=function(nums)
#      if not IsList(nums) then nums:=[nums];fi;
#      if Length(nums)=0 then return [];fi;
#      nums:=AbsInt(Lcm(nums));
#      nums:=Set(Factors(nums));
#      nums:=Difference(nums,[1]);
#      return nums;
#    end;
#    d.partialFactorization:=x->PartialFactorization(x,6);
#
#    d.primalityTest:=IsPrimeInt;
#
#    d.commonPrimesPlus:=Gcd;

#  elif ring=GaussianIntegers or ring=GaussianRationals then
#    d.bas:=Basis(CF(4),[1,E(4)]);
#    d.case:=2;
#    d.discriminant:=2;
#
#    d.makereductionfunc:=function(prime)
#    local pos,one,pol,x,root;
#      pos:=Position(d.moduli,prime);
#      if pos=fail then
#        Add(d.moduli,prime);
#        pos:=Length(d.moduli);
#        # build reduction info
#        if IsInt(prime) then
#          if prime<0 then prime:=-prime;fi;
#          x:=X(GF(prime),1);
#          pol:=x^2+1;
#          if not IsIrreducible(pol) then Error("not prime!");fi;
#          root:=RootsOfUPol(GF(prime^2),pol)[1];
#          d.pinfo[pos]:=[root,d.bas,[One(GF(prime)),root],prime^2];
#          d.redfuns[pos]:=function(a)
#            return Coefficients(d.bas,a)*d.pinfo[pos][3];
#          end;
#        elif IsCyclotomic(prime) then
#          x:=AbsInt(Norm(prime));
#          root:=Coefficients(d.bas,prime);
#          root:=-root[1]/root[2] mod x;
#          root:=root*One(GF(x));
#          d.pinfo[pos]:=[root,d.bas,[One(GF(x)),root],x];
#          d.redfuns[pos]:=function(a)
#            return Coefficients(d.bas,a)*d.pinfo[pos][3];
#          end;
#        else
#          Error("different ideal");
#        fi;
#      fi;
#
#      return d.redfuns[pos];
#    end;
#
#    d.convertparam:=function(prime)
#      d.makereductionfunc(prime); # set up
#      return d.pinfo[Position(d.moduli,prime)][4];
#    end;
#    d.denominatorfun:=function(a)
#      return Lcm(List(Coefficients(d.bas,a),DenominatorRat));
#    end;
#
#    d.factorsinnumbers:=function(num)
#    local a,an,b,c,n,i;
#      if not IsList(num) then num:=[num];fi;
#      if Length(num)=0 then return [];fi;
#      a:=Set(Concatenation(List(num,x->Factors(GaussianIntegers,x))));
#
#      # find associated ones. Use norm to avoid many pairs
#
#      # Norm 1 is unit
#      an:=List(a,Norm);
#      b:=[];
#      for n in Difference(an,[1]) do
#        c:=[];
#        for i in a{Filtered([1..Length(an)],x->an[x]=n)} do # ones of right norm
#          if not ForAny(c,x->i/x in GaussianIntegers) then
#            Add(b,i);
#            Add(c,i);
#          fi;
#        od;
#      od;
#      #Print("Factor ",num," -> ",b,"\n");
#      return b;
#    end;
#
#    d.partialFactorization:=function(a)
#      #Print("Not partial but full factor\n");
#      return d.factorsinnumbers(a);
#    end;
#
#    d.primalityTest:=x->1= Length(Factors(GaussianIntegers,x));
#
#    d.commonPrimesPlus:=function(arg)
#    local f,a,i,b,l;
##Print("commonPrimes :",a," ",b,"\n");
#      if Length(arg)=1 then l:=arg[1]; else l:=arg;fi;
#      a:=l[1];
#      i:=1;
#      while i<Length(l) do
#        i:=i+1;
#        b:=l[i];
#        if IsInt(a) and IsInt(b) then
#          a:=Gcd(a,b);
#        elif a=0 then a:=b;
#        elif b<>0 then
#          f:=d.factorsinnumbers([Gcd(Norm(a),Norm(b))]);
#          f:=Filtered(f,x->not IsZero(x));
#          f:=Filtered(f,x->a/x in GaussianIntegers and b/x in GaussianIntegers);
#          a:=Product(f,1);
#        fi;
#      od;
#      return a;
#    end;
#
#  elif IsAbelianNumberField(ring) and DegreeOverPrimeField(ring)=2 then

    d.case:=3;
    # quadratic field. Find out which root
    c:=Conductor(ring);
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
      d.eucl:=2;
    else
      d.bas:=Basis(ring,[1,ER(c)]);
      d.eucl:=1;
    fi;
    d.fundunit:=FundUnitQuadratic(c);

    # Norm-euclidean
    # https://encyclopediaofmath.org/wiki/Euclidean_field#:~:text=The%20norm%2DEuclidean%20quadratic%20fields,57%2C%20or%2073%2C%20cf.
    if not c in
      [-1,-2,2,-3,3,5,6,-7,7,-11,11,13,17,19,21,29,33,37,41,57,73] then
      d.eucl:=0;
    fi;
    d.minpol:=MinimalPolynomial(Rationals,d.bas[2]);
    d.discriminant:=Discriminant(d.minpol);
    d.omega:=(d.discriminant+ER(d.discriminant))/2;
    d.field:=Field(d.omega);
    d.primefacs:=[];


    d.factorprime:=function(p)
    local pos,id,f,b;
      pos:=PositionSorted(d.primefacs,[p,-infinity]);
      if pos<=Length(d.primefacs) and d.primefacs[pos][1]=p then
        return d.primefacs[pos][2];
      fi;
      # Prop. 5.1.4 in Cohen
      if d.discriminant mod p=0 then
        if p=2 and d.discriminant mod 16=12 then
          id:=[p,1+d.omega];
        else
          id:=[p,d.omega];
        fi;
        id:=QuadSingleIdealGen(id,d);
        f:=[id,id];
      elif Jacobi(d.discriminant,p)=-1 then
        f:=[p];
      else # Legendre=1
        f:=d.discriminant mod (4*p);
        #b:=First([1..4*p],x->x^2 mod (4*p)=f);
        id:=Cartesian(List(RootsOfUPol(X(GF(p))^2-(f mod p)),Int),
              Filtered([0..4],x->x^2 mod 4=(f mod 4)));
        id:=List(id,x->ChineseRem([p,4],x));
        b:=First(id,x->x^2 mod (4*p)=f);
        if b=fail then Error("bfail");fi;

        id:=[p,d.omega-(d.discriminant+b)/2];
        id:=QuadSingleIdealGen(id,d);
        f:=[id];
        id:=[p,d.omega-(d.discriminant-b)/2];
        id:=QuadSingleIdealGen(id,d);
        Add(f,id);
      fi;
      AddSet(d.primefacs,[p,f]);
      return f;
    end;



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
          d.redfuns[pos]:=IdealQuotientNumorder(d.bas,[number]);
          d.pinfo[pos]:=[fail,fail,fail,Size(Range(d.redfuns[pos]))];
        fi;
      fi;

      return d.redfuns[pos];
    end;




    d.convertparam:=function(number)
      d.makereductionfunc(number); # set up
      return d.pinfo[Position(d.moduli,number)][4];
    end;
    d.denominatorfun:=function(a)
      return Lcm(List(Coefficients(d.bas,a),DenominatorRat));
    end;

    d.factorsinnumbers:=function(num)
    local a,an,b,c,n,i,j,try,oi;
      if not IsList(num) then num:=[num];fi;
      if Length(num)=0 then return [];fi;

      a:=[];
      for i in Filtered(num,x->Norm(x)<>1) do
        # factor over Z and then split primes and check which ones do
        c:=i;
        if not IsRat(c) then
          c:=Norm(d.field,c);
          try:=true;
        else
          try:=false;
        fi;
        c:=List(Factors(c),AbsInt); # Z-primes
        if try then
          c:=Union(List(Set(c),d.factorprime));
          b:=[];
          oi:=i;
          for j in c do
            while AllIntcoeffs(Coefficients(d.bas,i/j)) do
              i:=i/j;
              Add(b,j);
            od;
          od;
#Print(i," factors ",b,"\nproduct:",Product(b),", QN:",
#  Norm(d.field,oi/Product(b)),"\n");
          Append(a,b);
        else
          c:=Concatenation(List(c,d.factorprime));
#Print(i," factors ",c,"\nproduct:",Product(c),", QN:",
#  Norm(d.field,i/Product(c)),"\n");
          Append(a,c);
        fi;
      od;
      Sort(a);
      if Length(a)=1 and Length(num)=1
        and ForAll(Coefficients(d.bas,a[1]/num[1]),IsInt) then
        return num;
      fi;

      if ForAll(a,IsCyclotomic) then
        # find associated ones. Use norm to avoid many pairs

        # Norm 1 is unit
        an:=List(a,x->Norm(d.field,x));
        b:=[];
        for n in Difference(an,[1]) do
          c:=[];
          for i in a{Filtered([1..Length(an)],x->an[x]=n)} do # ones of right norm
            if not ForAny(List(c,x->i/x),x->AllIntcoeffs(Coefficients(d.bas,x))) then
              Add(b,i);
              Add(c,i);
            fi;
          od;
        od;
        #Print("Factor ",num," -> ",b,"\n");
      else
        b:=a;
      fi;
      return b;
    end;

    d.partialFactorization:=function(a)
      #Print("Not partial but full factor\n");
      return d.factorsinnumbers(a);
    end;

    d.primalityTest:=function(num)
      local f;
      f:=d.factorsinnumbers(num);
      if Length(f)>1 then return false;fi;
      return Norm(d.field,num/f[1])=1;
    end;

    d.commonPrimesPlus:=function(arg)
    local f,a,i,b,l,e,j,common,k;
      if Length(arg)=1 then l:=arg[1]; else l:=arg;fi;
      e:=List(l,x->Norm(Field(x),x));
      l:=Concatenation([Gcd(e)],l);

      if d.eucl>0 then
        repeat
#Print(List(l{[1]},x->AbsInt(Norm(Field(x),x))));
          SortBy(l,x->AbsInt(Norm(Field(x),x)));
          a:=l[1];
          b:=[a];
          for i in [2..Length(l)] do
            e:=NormEuclideanAlgorithm(d,a,l[i]);
            if e=fail then Add(b,l[i]);
            else a:=e;fi;
          od;
          b[1]:=a;
          if Length(l)=Length(b) then
            # Euclidean failed
            e:=AbsInt(Norm(Field(a),a));
            if e=1 then return 1;fi; # unit
#Print("failed:",e,"\n");

            i:=PartialFactorization(e);
            if ForAll(i,IsPrimeInt) then
              l:=l{[2..Length(l)]};
              a:=d.factorsinnumbers(a);
              a:=Filtered(a,x->ForAll(l,y->ForAll(Coefficients(d.bas,y/x),IsInt)));
              a:=Product(a);
#Print("done:",Norm(Field(a),a),"\n");
              return a;
            else
              b:=Filtered(i,IsPrimeInt);
              if Length(b)=0 then
                Error("TURTU");
              fi;
              common:=1;
              for i in b do
                for j in d.factorsinnumbers(i) do
                  if ForAll(l,x->ForAll(Coefficients(d.bas,x/j),IsInt)) then
                    common:=common*j;
                    l:=List(l,x->x/j);
                  fi;
                  for k in [1..Length(l)] do
                    while ForAll(Coefficients(d.bas,l[k]/j),IsInt) do
                      l[k]:=l[k]/j;
                    od;
                  od;
                od;
              od;
              if l[1]=a then
                Error("immernoch");
              else
                Error();
                a:=common*d.commonPrimesPlus(l);
                Print("rone:",Norm(Field(a),a),"\n");
                return a;
              fi;
            fi;
          fi;
          l:=b;
        until Length(l)=1;
        return a;
      fi;

      return QuadSingleIdealGen(l,d);


#      m:=Filtered(l,x->not IsInt(x));
#      if Length(m)>0 then
#        f:=Field(m[1]);
#        m:=List(m,x->Norm(f,x));
#        m:=Gcd(m);
#      else
#        m:=1;
#      fi;
#
#      f:=Gcd(Concatenation([m],Filtered(l,IsInt)));
#      f:=d.factorsinnumbers([f]);
#
#      a:=[];
#      for i in f do
#        if ForAll(l,x->AllIntcoeffs(Coefficients(d.bas,x/i))) then
#          Add(a,i);
#        fi;
#      od;
#      return a;
    end;

#  else
#    Error("cannot yet do");
#  fi;
#  return d;


end;



# Part 1: Density testing

IsTransvection:=mat->RankMat(mat-mat^0)=1 and IsZero((mat-mat^0)^2);

# find proper kind, using an `arg' type argument list, returning SL or SP
CheckProperKind:=function(arglist,len)
local kind,form,n;
  if Length(arglist)>=len then
    kind:=arglist[len];

    if kind=0 then
      kind:=SL; # SL
      # determine proper kind
      n:=Length(One(arglist[1]));
      if IsEvenInt(n) then
        form:=NullMat(n,n,0);
        form{[1..n/2]}{[n/2+1..n]}:=IdentityMat(n/2,Rationals);
        form{[n/2+1..n]}{[1..n/2]}:=-IdentityMat(n/2,Rationals);
        if ForAll(GeneratorsOfGroup(arglist[1]),
          x->TransposedMat(x)*form*x=form) then
          Info(InfoArithSub,1,"Detected Form SP");
          kind:=SP;
        fi;
      fi;
    fi;

    if kind<>1 and kind<>2 and kind<>SL and kind<>SP then
      Error("Arithmetic groups of type ",kind," are not yet supported");
    fi;
    if kind=SL or kind=1 then
      kind:=SL;
    elif kind=2 or kind=SP then
      kind:=SP;
    fi;
  else
    kind:=SL;
  fi;

  # test degree
  if DegreeOfMatrixGroup(arglist[1])<2 then
    Error("The functions only work for degree >=3");
  fi;

  # test determinant
  if ForAny(GeneratorsOfGroup(arglist[1]),x->not IsOne(DeterminantMat(x))) then
    Error("The group is generated with a matrix of determinant <> 1");
  fi;

  return kind;
end;

ASPseudoRandom:=function(H)
local epi,e,r;
  r:=ValueOption("radius");
  if r=fail then r:=50;fi;
  epi:=EpimorphismFromFreeGroup(H);
  e:=PseudoRandom(Source(epi):radius:=r);
  return Image(epi,e);
end;

GenericAbsirr:=function(G)
local nsq,bas,basm,b,g,a,basmo,v,prime,red,modfun,cvparam;
  red:=PrepareReductionInfo(Char0ScalarDomainMatrixList(
    GeneratorsOfGroup(G)));

  prime:=11;
  prime:=red.primesinprime(prime)[1];
  modfun:=prime.redfun;
  cvparam:=prime.fieldsize;

  nsq:=Length(One(G))^2;
  bas:=[Flat(One(G))];
  basmo:=[];
  for b in bas do
    v:=List(b,modfun);
    ConvertToVectorRep(v,cvparam);
    Add(basmo,v);
  od;
  basm:=[One(G)];
  b:=1;
  while b<=Length(bas) do
    for g in GeneratorsOfGroup(G) do
      a:=basm[b]*g;
      v:=List(Flat(a),modfun);
      ConvertToVectorRep(v,cvparam);
      # try to test mod prime first if dimension is larger
      if SolutionMat(basmo,v)=fail or
        SolutionMat(bas,Flat(a))=fail then
        Add(basm,a);
        Add(bas,Flat(a));
        Add(basmo,List(Flat(a),modfun));
        if Length(bas)=nsq then
          return true;
        fi;
      fi;
    od;
    b:=b+1;
  od;
  return false;
end;

# kind is SL or SP
IsDenseIR1:=function(arg)
local G,kind,n,w1,w2,p,gal,r,t;

  G:=arg[1];
  kind:=CheckProperKind(arg,2);

  n:=Length(One(G));
  r:=0;
  repeat
    r:=r+1;
    if r>5 then return false;fi;
    w1:=ASPseudoRandom(G);
    w2:=ASPseudoRandom(G);
  until Order(w2)=infinity and w1*w2<>w2*w1;

  if kind=SL then
    t:=TransitiveIdentification(SymmetricGroup(n));
  else
    t:=TransitiveIdentification(WreathProduct(Group((1,2)),SymmetricGroup(n/2)));
  fi;

  p:=CharacteristicPolynomial(w1);
  if (not IsIrreducible(p)) or GaloisType(p)<>t then
    #Print("galtype w1=",GaloisType(p),"\n");
    return false;
  fi;

  p:=CharacteristicPolynomial(w2);
  if (not IsIrreducible(p)) or GaloisType(p)<>t then
    #Print("galtype w2=",GaloisType(p),"\n");
    return false;
  fi;

  # test irreducible
  if GenericAbsirr(G) then
    return true;
  else
    return false;
  fi;

end;

# kind is SL or SP
IsDenseIR2:=function(arg)
local G,kind,n,unflat,bas,i,j,m,V,act,form,mats;

  G:=arg[1];
  kind:=CheckProperKind(arg,2);


  unflat:=m->List([1..n],x->m{[1+n*(x-1)..n*x]});
  n:=Length(One(G));
  if IsFinite(G) then return false;fi;
  if kind=SL then
    #trace 0
    bas:=[];
    for i in [1..n] do
      for j in [1..n] do
        m:=NullMat(n,n);
        m[i][j]:=1;
        if i=j then
          m[n][n]:=-1;
        fi;
        if i<n or j<n then
          Add(bas,m);
        fi;
      od;
    od;
  else
    # symmetric
    bas:=[];
    for i in [1..n] do
      for j in [i..n] do
        m:=NullMat(n,n);
        m[i][j]:=1;
        if i<>j then
          m[j][i]:=1;
        fi;
        Add(bas,m);
      od;
    od;
    form:=NullMat(n,n);
    form{[1..n/2]}{[n/2+1..n]}:=IdentityMat(n/2);
    form{[n/2+1..n]}{[1..n/2]}:=-IdentityMat(n/2);
    bas:=List(bas,x->LeftQuotient(form,x));
  fi;
  bas:=List(bas,Flat);
  act:=function(m,g) return Flat(unflat(m)^g);end;
  mats:=List(GeneratorsOfGroup(G),x->List(bas,b->SolutionMat(bas,act(b,x))));
  return GenericAbsirr(Group(mats));
end;

PrimesForDense:="forward declare";
NumberNotAbsIrr:="forward declare";

IsDenseDFH:=function(arg)
local G,kind;
  G:=arg[1];
  kind:=CheckProperKind(arg,2);
  return PrimesForDense(G,arg[Length(arg)],kind:densitytest);
end;

# Part 2: Level and Index

# utility function

# basis enveloping algebra
RegModZSpan:=function(gens,seed,omodfun,red)
local n,matsplit,b,cnt,HM,si,new,bc,i,j,d,process,stack,max,prime,
fp,fpgens,words,k,sol,det,odet,reducer,dens,bas,modfun,spare;

  if red=fail then bas:=fail; else bas:=red.bas;fi;

  reducer:=function(M)
    if dens then
      return LLLReducedBasis(M).basis;
    else
      return HermiteNormalFormIntegerMat(M);
    fi;
  end;

  dens:=not (ForAll(Flat(seed),IsInt) and ForAll(Flat(gens),IsInt));

  # reduction if not rational
  if not (ForAll(Flat(seed),IsRat) and ForAll(Flat(gens),IsRat)) then
    reducer:=function(M)
      M:=MyHNF(M,red);
      M:=Filtered(M,x->not IsZero(M));
      return M;
    end;
  fi;

  if omodfun=false then
    modfun:=x->x;
  else
    modfun:=omodfun;
  fi;

  n:=Length(gens[1]);

  matsplit:=l->List([1..n],x->l{[n*(x-1)+1..n*x]});

  # first work modulo `oneirr' to get full rank
  fp:=FreeGroup(Length(gens));
  fpgens:=GeneratorsOfGroup(fp);
  bc:=List(seed,r->List(r,modfun));
  i:=0;
  words:=List(bc,x->[0,One(fp)]);
  spare:=[];
  while Length(bc)<Length(bc[1]) do
    i:=i+1;
    if i>Length(bc) then
      if omodfun=false then
	return bc;
      fi;
      Info(InfoArithSub,2,"not full rank mod irr");
      return fail; # wrong generators -- not full rank
    fi;
    si:=matsplit(bc[i]);
    for j in [1..Length(gens)] do
      for k in [1,-1] do
	#new:=Concatenation(si*(gens[j]*oneirr)^k);
        new:=Concatenation(si*List(gens[j],r->List(r,modfun))^k);
	if SolutionMat(bc,new)=fail then
	  Add(bc,new);
	  words[Length(bc)]:=[i,fpgens[j]^k];
        else
          Add(spare,[i,fpgens[j]^k]);
	fi;
      od;
    od;
  od;

  Info(InfoArithSub,3,"Zspan");

  # next, form these images over Z.
  b:=ShallowCopy(seed);
  i:=Length(b);
  while i<Length(bc) do
    i:=i+1;
    si:=matsplit(b[words[i][1]]);
    new:=si*MappedWord(words[i][2],fpgens,gens);
    Add(b,Concatenation(new));
  od;

  Info(InfoArithSub,3,"Detfix");

#Print(Length(gens),"generat\n");
#Error();

  # check that we got all images in
  HM:=reducer(b);
#det:=MyDiscriminantOfLattice(HM);
  for i in [1..Length(b)] do
    si:=matsplit(b[i]);
    for j in [1..Length(gens)] do
      for k in [1,-1] do
	# did we do this image already -- if so unneeded
	if not [i,fpgens[j]^k] in words then
	  new:=Concatenation(si*gens[j]^k);
	  sol:=SolutionMat(HM,new);
	  if sol=fail or
            #non-integer cases - Z
            (bas=fail and not ForAll(sol,IsInt)) or
            #non-integer cases - O
             (bas<>fail and not ForAll(sol,
               x->ForAll(Coefficients(red.bas,x),IsInt))) then
            Info(InfoArithSub,4,"Add Vector");
#odet:=det;
	    HM:=reducer(Concatenation(HM,[new]));
#det:=MyDiscriminantOfLattice(HM);
#Print("not in ",odet/det,"\n");
	  fi;
	fi;
      od;
    od;
  od;
  Info(InfoArithSub,3,"Zlatt Done");
  return HM;
end;



# Part 3: Orbit/Stabilizer

OrbitStabRepsMultistage:=
  function(pcgs,pcgsimgs,pcisom,solvsz,solvtriv,gens,imgs,fgens,
           factorhom,gpsz,actfun,domain,obj)

local stabilizergen,st,stabrsub,stabrsubsz,ratio,subsz,vp,stabrad,
      stabfacgens,s,orblock,orb,rep,p,repwords,i,j,k,repword,
      imgsinv,img,stabfac,reps,stage,genum,orbstabs,stabfacimg,
      fgrp,solsubsz,failcnt,stabstack,relo,dict;

  stabilizergen:=function()
  local im,i,fe,gpe;

    if stage=1 then
      Error("solv stage is gone");
    else
      # in radical factor, still it could be the identity
      if Length(repword)>0 then
        # build the factor group element
        fe:=One(Image(factorhom));
        for i in repword do
          fe:=fe*fgens[i];
        od;
        for i in Reversed(repwords[p]) do
          fe:=fe/fgens[i];
        od;
        if not fe in stabfac then
          # not known -- add to generators
          Add(stabfacimg,fe);

          if IsRecord(st) then
            if st.left<>fail then
              Error("cannot happen");
              st:=st.left/st.right;
            else
              gpe:=One(Source(factorhom));
              for i in repwords[st.vp] do
                gpe:=gpe*gens[i];
              od;
              gpe:=gpe*gens[st.genumr];
              for i in Reversed(repwords[st.right]) do
                gpe:=gpe/gens[i];
              od;

              # vector image under st
              im:=orb[1];
              for i in repwords[st.vp] do
                im:=actfun(im,imgs[i]);
              od;
              im:=actfun(im,imgs[st.genumr]);
              for i in Reversed(repwords[st.right]) do
                im:=actfun(im,imgsinv[i]);
              od;
            fi;

            # make sure st really stabilizes by dividing off solvable bit
            st:=gpe/reps[LookupDictionary(dict,im)];
          fi;

          Add(stabfacgens,st);
          stabfac:=ClosureGroup(stabfac,fe);
          subsz:=stabrsubsz*Size(stabfac);
          ratio:=gpsz/subsz/Length(orb);
          if ratio=1 then vp:=Length(orb);fi;
          Assert(1,GeneratorsOfGroup(stabfac)=stabfacimg);

        fi;
      fi;
    fi;

    # radical stabilizer element. TODO: Use PCGS to remove
    # duplicates
  end;

  fgrp:=Group(fgens,One(Range(factorhom)));
  imgsinv:=List(imgs,Inverse);

  # now compute orbit, being careful to get stabilizers in steps

  dict:=NewDictionary(obj,true,domain);
  orb:=[obj];
  AddDictionary(dict,obj,1);
  reps:=[One(Source(factorhom))];
  stabstack:=[];
  stabrad:=[];
  stabrsub:=solvtriv;
  stabrsubsz:=Size(solvtriv);
  stabfac:=TrivialSubgroup(fgrp);
  subsz:=stabrsubsz*Size(stabfac);
  stabfacgens:=[];
  stabfacimg:=[];
  repwords:=[[]];

  # now do a two-stage orbit algorithm. first solvable, then via the
  # factor group. Both times we can check that we have the correct orbit.

  # ratio 1: full orbit/stab known, ratio <2 stab cannot grow any more.
  ratio:=5;
  vp:=1; # position in orbit to process

  # solvable iteration
  stage:=1;
  for genum in [Length(pcgs),Length(pcgs)-1..1] do
    relo:=RelativeOrders(pcisom!.sourcePcgs)[
            DepthOfPcElement(pcisom!.sourcePcgs,pcgs[genum])];
    img:=actfun(orb[1],pcgsimgs[genum]);
    repword:=repwords[1];
    p:=LookupDictionary(dict,img);
    if p=fail then
      # new orbit images
      vp:=Length(orb)*(relo-1);
      for j in [1..vp] do
        img:=actfun(orb[j],pcgsimgs[genum]);
        Add(orb,img);
        AddDictionary(dict,img,Length(orb));
        Add(reps,reps[j]*pcgs[genum]);
        Add(repwords,repword);
      od;
    else
      rep:=pcgs[genum]/reps[p];
      Add(stabrad,rep);
      stabrsubsz:=stabrsubsz*relo;
      subsz:=stabrsubsz;
      ratio:=gpsz/subsz/Length(orb);
    fi;

  od;
  stabrad:=Reversed(stabrad);

  subsz:=stabrsubsz;
  if  solvsz>subsz*Length(orb) then
    Error("processing stabstack solvable ", Length(stabrad));

    s:=1;
    while solvsz<>subsz*Length(orb) do
      vp:=stabstack[s][1];
      genum:=stabstack[s][2];
      img:=actfun(orb[vp],pcgsimgs[genum]);
      rep:=reps[vp]*pcgs[genum];
      repword:=repwords[vp];
      p:=LookupDictionary(dict,img);
      st:=rec(left:=rep,right:=reps[p]);
      stabilizergen();
      s:=s+1;
    od;
    Info(InfoHomClass,5,"processed solvable ",s," from ",Length(stabstack));
  fi;

  subsz:=stabrsubsz;
  solsubsz:=subsz;

  orblock:=Length(orb);
  Info(InfoHomClass,5,"solvob=",orblock);

  # nonsolvable iteration: We act on orbits
  stage:=2;

  # ratio 1: full orbit/stab known, ratio <2 stab cannot grow any more.
  ratio:=5;
  vp:=1;
  while vp<=Length(orb) do
    for genum in [1..Length(gens)] do
      img:=actfun(orb[vp],imgs[genum]);

      repword:=Concatenation(repwords[vp],[genum]);

      p:=LookupDictionary(dict,img);
      if p=fail then
        # new orbit image
        Add(orb,img);
        AddDictionary(dict,img,Length(orb));
        Add(repwords,repword);
        for j in [1..orblock-1] do
          img:=actfun(orb[vp+j],imgs[genum]);
          Add(orb,img);
          AddDictionary(dict,img,Length(orb));
          Add(repwords,Concatenation(repwords[vp+j],[genum]));
        od;

        ratio:=gpsz/subsz/Length(orb);
        if ratio=1 then vp:=Length(orb);fi;

      elif ratio>=2 then
        # old orbit element -- stabilizer generator
        # if ratio <2 the stabilizer cannot grow any more

        st:=rec(left:=fail,vp:=vp,genumr:=genum,right:=p);
        stabilizergen();
      fi;
    od;
    vp:=vp+orblock; # jump in steps
  od;

  s:=1;
  subsz:=stabrsubsz*Size(stabfac);
  if  gpsz<>subsz*Length(orb) then
    Error("should not happen nonslv stabstack");
  fi;

  Info(InfoHomClass,4,"orblen=",Length(orb)," blocked ",orblock,
    " len=", Length(stabrad)," ",Length(stabfacgens));

  s:=rec(rep:=orb[1],len:=Length(orb),stabradgens:=stabrad,
          stabfacgens:=stabfacgens,stabfacimgs:=stabfacimg,
          stabrsub:=stabrsub,stabrsubsz:=stabrsubsz,subsz:=subsz
                );
  s.gens:=gens;
  s.fgens:=fgens;
  s.orbit:=orb;
  s.orblock:=orblock;
  s.reps:=reps;
  s.repwords:=repwords;

  return s;
end;

ModularImageMatrixGroup:=function(g,m)
local r,l,h,red;
  l:=List(GeneratorsOfGroup(g),x->List(x,r->List(r,Int)));
  if IsInt(m) then
    r:=Integers mod m;
    l:=List(l,x->x*One(r));
  else
    l:=List(GeneratorsOfGroup(g),x->List(x,r->List(r,m)));
  fi;
  h:=Group(l);
  return h;
end;

# word decomposition functions

###########################################################
#
# Compute HNF and keep word of the transforms
#
# based on library DoNFIM
#

# on generators  [ [ 1, 1 ], [ 0, 1 ] ], [ [ 1, 0 ], [ 1, 1 ] ]
SL2WORD:=function(gens,mat)
local w,q;
  #if not IsMatrix(gens[1]) then
  #  Assert(1,SL2WORD([[ [ 1, 1 ], [ 0, 1 ] ], [ [ 1, 0 ], [ 1, 1 ] ]],mat)=mat);
  #fi;
  mat:=List(mat,ShallowCopy);
  w:=One(gens[1]);
  #euclid column 1
  while not IsZero(mat[2][1]) do
    if IsZero(mat[1][1]) then
      # add 2 to 1, subtract 1 from 2
      AddRowVector(mat[1],mat[2],1);
      w:=gens[1]*w;
      AddRowVector(mat[2],mat[1],-1);
      w:=gens[2]^-1*w;
    elif AbsInt(mat[2][1])>=AbsInt(mat[1][1]) then
      q:=QuoInt(AbsInt(mat[2][1]),AbsInt(mat[1][1]));
      if SignInt(mat[2][1])=SignInt(mat[1][1]) then
        AddRowVector(mat[2],mat[1],-q);
        w:=gens[2]^-q*w;
      else
        AddRowVector(mat[2],mat[1],q);
        w:=gens[2]^q*w;
      fi;
    else
      q:=QuoInt(AbsInt(mat[1][1]),AbsInt(mat[2][1]));
      if SignInt(mat[2][1])=SignInt(mat[1][1]) then
        AddRowVector(mat[1],mat[2],-q);
        w:=gens[1]^-q*w;
      else
        AddRowVector(mat[1],mat[2],q);
        w:=gens[1]^q*w;
      fi;
    fi;
    #Print(mat,"\n");
  od;
  if mat[1][1]<0 then
    mat:=-mat;
    w:=(gens[2]^-1*gens[1]^2)^2*w;
  fi;
  w:=gens[1]^-mat[1][2]*w;
  #mat:=gens[1]^-mat[1][2]*mat;
  return w^-1;
end;


HNFWord:=function(hom,mat)
local opt, sig, n, m, A,  r, c2, rp, c1, j, k, N, L, b, a, g, c,
      t, tmp, i, q, R,tIndex,gens,w,small,trunc;

  trunc:=ValueOption("always")=true;
  mat:=List(mat,ShallowCopy);
  tIndex:=hom!.tIndex;
  gens:=MappingGeneratorsImages(hom)[1];
  w:=One(gens[1]);
  #Parse options
  opt:=[ false, true, true, false, false ];

  #Embed arg[1] in 2 larger "id" matrix
  n:=Length(mat)+2;
  m:=Length(mat[1])+2;
  k:=ListWithIdenticalEntries(m,0);

  A:=[];
  for i in [2..n-1] do
    #A[i]:=[0];
    #Append(A[i],arg[1][i-1]);
    #A[i][m]:=0;
    A[i]:=ShallowCopy(k);
    A[i]{[2..m-1]}:=mat[i-1];
  od;
  A[1]:=ShallowCopy(k);
  A[n]:=k;
  A[1][1]:=1;
  A[n][m]:=1;

  #list:=[];

  r:=0;
  c2:=1;
  rp:=[];
  while m>c2 do
    Info(InfoMatInt,2,"DoNFIM - reached column ",c2," of ",m);
    r:=r+1;
    c1:=c2;
    rp[r]:=c1;

    j:=c1+1;
    while j<=m do
      k:=r+1;
      while k<=n and A[r][c1]*A[k][j]=A[k][c1]*A[r][j] do k:=k+1; od;
      if k<=n then c2:=j; j:=m; fi;
     j:=j+1;
    od;

    c:=MATINTmgcdex(AbsInt(A[r][c1]),A[r+1][c1],A{[r+2..n]}[c1]);
    for i in [r+2..n] do
      if c[i-r-1]<>0 then
        AddRowVector(A[r+1],A[i],c[i-r-1]);
        #Add(list,["add",r,i-1,c[i-r-1]]);
        w:=gens[tIndex[r][i-1]]^c[i-r-1]*w;
        #C[r+1][i]:=c[i-r-1];
        #AddRowVector(Q[r+1],Q[i],c[i-r-1]);
      fi;
    od;

    i:=r+1;
    while A[r][c1]*A[i][c2]=A[i][c1]*A[r][c2] do i:=i+1; od;
    if i>r+1 then
      c:=MATINTmgcdex(AbsInt(A[r][c1]),A[r+1][c1]+A[i][c1],[A[i][c1]])[1]+1;;
      AddRowVector(A[r+1],A[i],c);
      if not IsZero(c) then
        #Add(list,["add",r,i-1,c]);
        w:=gens[tIndex[r][i-1]]^c*w;
      fi;

      #C[r+1][i]:=C[r+1][i]+c;
      #AddRowVector(Q[r+1],Q[i],c);
    fi;

    g:=MATINTbezout(A[r][c1],A[r][c2],A[r+1][c1],A[r+1][c2]);
    small:=[[g.coeff1,g.coeff2],[g.coeff3,g.coeff4]];
    if DeterminantMat(small)=-1 then
      small[2]:=-small[2];
    fi;
    # isbound is only relevant if matrix does not have determinant 1
    if not IsOne(small) and IsBound(tIndex[r]) then
      A{[r,r+1]}:=small*A{[r,r+1]};
      #Add(list,["2mult",r-1,r,small]);
      w:=SL2WORD([gens[tIndex[r-1][r]],gens[tIndex[r][r-1]]],small)*w;
    fi;
    #Q{[r,r+1]}:=[[g.coeff1,g.coeff2],[g.coeff3,g.coeff4]]*Q{[r,r+1]};

    for i in [r+2..n] do
      q:=QuoInt(A[i][c1],A[r][c1]);
      AddRowVector(A[i],A[r],-q);
      if not IsZero(q) then
        #Add(list,["add",i-1,r-1,-q]);
        w:=gens[tIndex[i-1][r-1]]^-q*w;

      fi;
      #AddRowVector(Q[i],Q[r],-q);
      q:=QuoInt(A[i][c2],A[r+1][c2]);
      AddRowVector(A[i],A[r+1],-q);
      if not IsZero(q) then
        #Add(list,["add",i-1,r,-q]);
        w:=gens[tIndex[i-1][r]]^-q*w;
      fi;
      #AddRowVector(Q[i],Q[r+1],-q);
    od;

  od;
  rp[r+1]:=m;
  Info(InfoMatInt,2,"DoNFIM - r,m,n=",r,m,n);

  # hermite or (smith w/ column transforms)

  for i in [r, r-1 .. 1] do
    Info(InfoMatInt,2,"DoNFIM - reducing row ",i);
    for j in [i+1 .. r+1] do
      q:=QuoInt(A[i][rp[j]]-(A[i][rp[j]] mod A[j][rp[j]]),A[j][rp[j]]);
      AddRowVector(A[i],A[j],-q);
      if not IsZero(q) then
        #Add(list,["add",i-1,j-1,-q]);
        w:=gens[tIndex[i-1][j-1]]^-q*w;
      fi;
      #AddRowVector(Q[i],Q[j],-q);
    od;
  od;

  # #row transforms finisher
  # for i in [r+2..n] do Q[i][i]:= 1; od;

  for i in [2..n-1] do
    A[i-1]:=A[i]{[2..m-1]};
  od;
  Unbind(A[n-1]);
  Unbind(A[n]);
  if trunc then return w^-1;
  elif not IsOne(A) then Error("not one!");fi;
  return w^-1;
end;

NormDriver:=function(hom,phom,mat,norm)
local n,bn,b,bs,i,sign,a,left,right,words,lwords,lgens,sel,lsel,gens,ln;
  gens:=MappingGeneratorsImages(hom);
  words:=gens[1];
  gens:=gens[2];

  # remove duplicates
  if IsBound(hom!.unduplisel) then
    sel:=hom!.unduplisel;
  else
    sel:=[];
    for i in [1..Length(gens)] do
      if not ForAny(sel,x->gens[i]=gens[x] or gens[i]=gens[x]^-1)
        and gens[i]<>One(gens[i]) then
        Add(sel,i);
      fi;
    od;
    hom!.unduplisel:=sel;
  fi;

  left:=One(words[1]);
  right:=left;

  repeat
    n:=norm(mat);
    lwords:=words;
    lgens:=gens;
    lsel:=sel;
    bn:=0;
    bs:=0;
    b:=0;
    while b=0 do

      for i in lsel do
        for sign in [1,-1] do

          a:=lgens[i]^sign*mat;
          ln:=(n-norm(a))/Length(lwords[i]);
          if ln>bn then
            bn:=ln;
            b:=sign*i;
            bs:=1;
          fi;

          a:=mat*lgens[i]^sign;
          ln:=(n-norm(a))/Length(lwords[i]);
          if ln>bn then
            bn:=ln;
            b:=sign*i;
            bs:=2;
          fi;

        od;
      od;
  #Print("DID ",bn,"\n");
      if bs=1 then
        mat:=lgens[AbsInt(b)]^SignInt(b)*mat;
        left:=lwords[AbsInt(b)]^SignInt(b)*left;
      elif bs=2 then
        mat:=mat*lgens[AbsInt(b)]^SignInt(b);
        right:=right*lwords[AbsInt(b)]^SignInt(b);
      # now the cases that it failed, hom and phom
      elif IsIdenticalObj(lgens,gens) then
        lgens:=MappingGeneratorsImages(phom);
        lwords:=lgens[1];
        lgens:=lgens[2];
        lsel:=Filtered([1..Length(lwords)],x->Length(lwords[x])>0);
      else
        b:=1; # to break while loop
      fi;
    od;

  until bn=0;
  return rec(left:=left,mat:=mat,right:=right);
end;

SlSPDecompExtraGenHom:=function(hom,lev)
local gens,words,sel,i,pw,pm,new,nem,j,k,sign;
  gens:=MappingGeneratorsImages(hom);
  words:=gens[1];
  gens:=gens[2];
  # remove duplicates
  sel:=[];
  for i in [1..Length(gens)] do
    if not ForAny(sel,x->gens[i]=gens[x] or gens[i]=gens[x]^-1) then
      Add(sel,i);
    fi;
  od;
  gens:=gens{sel};
  words:=words{sel};

  pw:=[One(Source(hom))];
  pm:=[One(Range(hom))];
  for i in [1..lev] do
    for j in [1..Length(pw)] do
      for k in [1..Length(gens)] do
        for sign in [1,-1] do
          nem:=pm[j]*gens[k]^sign;
          if not (nem in pm  or nem^-1 in pm) then
            new:=pw[j]*words[k]^sign;
            Add(pm,nem);
            Add(pw,new);
          fi;
        od;
      od;
    od;
  od;
  Info(InfoArithSub,1,"Built pool of size ",Length(pm));
  return GroupHomomorphismByImagesNC(Source(hom),Range(hom),pw,pm);
end;

WordSL:=function(hom,elm)
local phom,left,right,one,norm2dist,red,norm,n,i,slhom,a,b,factorrad;

  n:=Length(elm);
  if IsBound(hom!.phom) then
    phom:=hom!.phom;
  else
    factorrad:=ValueOption("factorrad");
    if factorrad=fail then factorrad:=4;fi;
    phom:=SlSPDecompExtraGenHom(hom,factorrad);
    hom!.phom:=phom;
  fi;

  left:=One(Source(hom));
  right:=left;

  one:=One(elm);

  norm:=m->Sum(m-one,x->x*x);
  red:=NormDriver(hom,phom,elm,norm);
  left:=red.left*left;right:=right*red.right;elm:=red.mat;

  if norm(elm)<>0 then
    Info(InfoWarning,1,"not perfect cleanout");
    red:=HNFWord(hom,elm);
  else
    red:=One(Source(hom));
  fi;

  return left^-1*red/right;
end;

SLNZFP:=function(n)
local t,geni,m,gens,f,rels,i,j,k,l,mat,mats,id,hom,inv;
  # for 2, get the nice pres
  if n=2 then
    f:=FreeGroup("S","T");
    rels:=ParseRelators(f, "S^4, (S^3*T)^3, S^2*T*S^-2*T^-1");
    t:=f/rels;
    gens:=ShallowCopy(GeneratorsOfGroup(t));
    Add(gens,t.1^2*t.2/t.1*t.2);
    mats:=[[[0,-1],[1,0]],[[1,1],[0,1]],[[1,0],[1, 1]]];
    geni:=[[,2],[3]];
  else
    geni:=List([1..n],x->[]);
    t:=function(i,j)
      return gens[geni[i][j]];
    end;
    mats:=[];
    id:=IdentityMat(n,1);
    m:=0;
    gens:=[];
    for i in [1..n] do
      for j in [1..n] do
        if j<>i then
          m:=m+1;
          geni[i][j]:=m;
          Add(gens,Concatenation("t",String(i),String(j)));
          mat:=List(id,ShallowCopy);
          mat[i][j]:=1;
          Add(mats,mat);
        fi;
      od;
    od;
    f:=FreeGroup(gens);
    gens:=GeneratorsOfGroup(f);
    rels:=[];
    for i in [1..n] do
      for j in Difference([1..n],[i]) do
        for k in Difference([1..n],[j]) do
          for l in Difference([1..n],[i,k]) do
            if i>k or j>l then
              Add(rels,Comm(t(i,j),t(k,l)));
            fi;
          od;
          if k<>i then
            Add(rels,Comm(t(i,j),t(j,k))/t(i,k));
          fi;
        od;
      od;
    od;
    Add(rels,(t(1,2)/t(2,1)*t(1,2))^4);
    t:=f/rels;
    gens:=GeneratorsOfGroup(t);
  fi;

  m:=Group(mats);
  hom:=GroupHomomorphismByImages(t,m,gens,mats);
  hom!.tIndex:=geni;
  inv:=GroupHomomorphismByFunction(m,t,function(mat)
    return WordSL(hom,mat);
  end);
  SetIsBijective(hom,true);
  SetIsBijective(inv,true);
  SetInverseGeneralMapping(hom,inv);
  SetInverseGeneralMapping(inv,hom);
  return hom;
end;


WordSP:=function(hom,elm)
local phom,left,right,one,norm2dist,red,norm,n,i,slhom,a,b,factorrad;

  factorrad:=ValueOption("factorrad");
  if factorrad=fail then factorrad:=4;fi;
  n:=Length(elm);
  #phom:=SlSPDecompExtraGenHom(hom,3);
  a:=MappingGeneratorsImages(hom);
  b:=ShallowCopy(a[2]);
  a:=ShallowCopy(a[1]);
  for i in hom!.wrds do
    Add(a,i[2]);
    Add(b,Image(hom,i[2]));
  od;
  if IsBound(hom!.phom) then
    phom:=hom!.phom;
  else
    phom:=GroupHomomorphismByImagesNC(Source(hom),Range(hom),a,b);
    phom:=SlSPDecompExtraGenHom(phom,factorrad);
    hom!.phom:=phom;
  fi;

  left:=One(Source(hom));
  right:=left;

  one:=One(elm);
  norm2dist:=m->Sum(m-one,x->x*x); #2-norm distance to identity

  norm:=m->Sum(m-one,x->x*x);
  red:=NormDriver(hom,phom,elm,norm);
  left:=red.left*left;right:=right*red.right;elm:=red.mat;

  # upper right block
  for i in [1..n/2] do
    norm:=m->Sum(m{[1..i]}{[n/2+1..n]},x->x*x);
#Display(elm);Print(norm(elm)," \n");
    if norm(elm)>0 then
      red:=NormDriver(hom,phom,elm,norm);
      left:=red.left*left;right:=right*red.right;elm:=red.mat;
    fi;
  od;

  # lower left block
  for i in [n/2+1..n] do
    norm:=m->Sum(m{[n/2+1..i]}{[1..n/2]},x->x*x)+Sum(m{[1..n/2]}{[n/2+1..n]},x->x*x);
#Display(elm);Print(norm(elm)," \n");
    if norm(elm)>0 then
      red:=NormDriver(hom,phom,elm,norm);
      left:=red.left*left;right:=right*red.right;elm:=red.mat;
    fi;
  od;

  if norm(elm)<>0 then Error("not perfect cleanout");fi;

  if not IsBound(hom!.halfslhom) then
    slhom:=SLNZFP(n/2:factorrad:=2*factorrad);
    hom!.halfslhom:=slhom;
  else
    slhom:=hom!.halfslhom;
  fi;
  a:=elm{[1..n/2]}{[1..n/2]};
  if DeterminantMat(a)=-1 then
    a:=MappingGeneratorsImages(hom)[1];
    #(Y1^2U1)^2 is -1...1 blcoks
    a:=(First(a,x->String(x)="Y1")^2*First(a,x->String(x)="U1"))^2;
    elm:=elm*Image(hom,a);
    right:=right/a;
    # fix determinant of minor
    a:=elm{[1..n/2]}{[1..n/2]};
  fi;

  red:=WordSL(slhom,a);

  #map onto sp generators:
  a:=MappingGeneratorsImages(slhom)[2];
  b:=[];
  for i in [1..Length(a)] do
    b[i]:=PositionProperty(MappingGeneratorsImages(phom)[2],x->x{[1..n/2]}{[1..n/2]}=a[i]);
  od;
  if fail in b then Error("generator map");fi;
  red:=MappedWord(red,MappingGeneratorsImages(slhom)[1],MappingGeneratorsImages(phom)[1]{b});
  return left^-1*red/right;
  Error("ZZY");




  norm:=m->Sum(m,x->Sum(x,AbsInt)); # 1
  norm:=m->Sum(m,x->x*x); #2-norm
  #norm:=m->Maximum(List(m,x->Maximum(List(x,AbsInt)))); # infty;

  #norm:=m->Sum(m{[1]}{[4..6]},x->x*x);
end;


# presentation following Birman, 1971
SPNZFP:=function(twog)
local g,symb,mats,yind,uind,zind,i,m,free,rels,j,k,r,s,t,genprod,addrel,p,
      gens,hom,inv,gp,a,b;

  g:=twog/2;
  if not IsInt(g) then
    Error("SLNZFP needs even degree");
  fi;

  genprod:=function(l)
    local i,w;
    w:=One(gens[1]);
    for i in l do
      w:=w*gens[i];
    od;
    return w;
  end;

  addrel:=function(r)
    if not IsOne(MappedWord(r,gens,mats)) then Error("wrong rel");fi;
    AddSet(rels,r);
  end;

  symb:=[];
  mats:=[];
  yind:=[];
  uind:=[];
  zind:=[];
  for i in [1..g] do
    Add(symb,Concatenation("Y",String(i)));
    Add(yind,Length(symb));
    m:=IdentityMat(2*g);
    m[i][g+i]:=-1;
    Add(mats,m);
  od;
  for i in [1..g] do
    Add(symb,Concatenation("U",String(i)));
    Add(uind,Length(symb));
    m:=IdentityMat(2*g);
    m[g+i][i]:=1;
    Add(mats,m);
  od;
  for i in [1..g-1] do
    Add(symb,Concatenation("Z",String(i)));
    Add(zind,Length(symb));
    m:=IdentityMat(2*g);
    m[i][g+i]:=-1;
    m[i][g+i+1]:=1;
    m[i+1][g+i]:=1;
    m[i+1][g+i+1]:=-1;
    Add(mats,m);
  od;

  free:=FreeGroup(symb);
  gens:=GeneratorsOfGroup(free);
  rels:=[];
  # (1.1)
  for i in [1..g] do
    for r in [i+1..g] do
      addrel(Comm(gens[yind[i]],gens[yind[r]])); # [Yi,Yr]
    od;
    for s in [1..g] do
      if i<>s then
        addrel(Comm(gens[yind[i]],gens[uind[s]])); # [Yi,Us]
      fi;
    od;
    for t in [1..g-1] do
      addrel(Comm(gens[yind[i]],gens[zind[t]])); # [Yi,Yr]
    od;
  od;

  for j in [1..g] do
    for s in [j+1..g] do
      addrel(Comm(gens[uind[j]],gens[uind[s]])); # [Uj,Us]
    od;
    for t in [1..g-1] do
      if j<>t and j<>t+1 then
        addrel(Comm(gens[uind[j]],gens[zind[t]])); # [Uj,Zt]
      fi;
    od;
  od;

  for k in [1..g-1] do
    for t in [k+1..g-1] do
      addrel(Comm(gens[zind[k]],gens[zind[t]])); # [Zk,Zt]
    od;
  od;

  # (1.2)
  for i in [1..g] do
    addrel(genprod([yind[i],uind[i],yind[i]])/genprod([uind[i],yind[i],uind[i]]));
  od;

  # (1.3)
  for j in [1..g] do
    for t in [j-1,j] do
      if t>0 and t<g then
        addrel(genprod([uind[j],zind[t],uind[j]])/genprod([zind[t],uind[j],zind[t]]));
      fi;
    od;
  od;

  if g>=3 then
    # (1.5)
    p:=[];
    for i in [1..g-1] do
      p[i]:=genprod([yind[i],uind[i],yind[i]])*genprod([yind[i],uind[i],zind[i],uind[i+1],yind[i+1]])^3*genprod([yind[i],uind[i],yind[i]])^-1;
    od;

    # (1.4)
    for i in [1..g-2] do
      addrel(p[i]*p[i+1]*gens[zind[i]]/p[i+1]/p[i]/gens[zind[i+1]]);
    od;

    # (1.10)
    addrel(genprod([yind[3],yind[2],yind[1]])
      /gens[zind[1]]*gens[uind[2]]/gens[zind[2]]/gens[uind[2]]/gens[yind[2]]
      *genprod([uind[2],zind[1],uind[2],zind[2]])/gens[yind[2]]/gens[uind[2]]
    /(p[2]*gens[zind[1]]/p[2]));

  fi;

  # (1.6)
  addrel(genprod([yind[1],uind[1],yind[1]])^4);

  # (1.7)
  addrel(genprod([yind[1],uind[1],zind[1],uind[2],yind[2]])^6);

  # (1.8)
  addrel(genprod([yind[1],uind[1],zind[1],uind[2],yind[2],yind[2],uind[2],zind[1],uind[1],yind[1]])^2);

  # (1.9)
  addrel(Comm(genprod([yind[1],uind[1],zind[1],uind[2],yind[2],yind[2],uind[2],zind[1],uind[1],yind[1]]),gens[yind[1]]));

  rels:=Filtered(rels,x->not IsOne(x));

  gp:=free/rels;
  gens:=GeneratorsOfGroup(gp);
  m:=Group(mats);
  hom:= GroupHomomorphismByImages(gp,m,GeneratorsOfGroup(gp),mats);
  inv:=GroupHomomorphismByFunction(m,gp,function(mat)
    return WordSP(hom,mat);
  end);
  SetIsBijective(hom,true);
  SetIsBijective(inv,true);
  SetInverseGeneralMapping(hom,inv);
  SetInverseGeneralMapping(inv,hom);

  mats:=[];
  # calcuate words for other generators
  # first the $t_{i,j}$:
  for i in [2..g] do
    Add(mats,[["t",i-1,i],
              genprod([yind[i],uind[i],yind[i],yind[i-1]])^-1*
                genprod([zind[i-1],uind[i],yind[i]])]);
    Add(mats,[["t",i,i-1],
              genprod([yind[i],yind[i-1],uind[i-1],yind[i-1]])/
                genprod([yind[i-1],uind[i-1],zind[i-1]])]);
  od;

  for i in [3..g] do
    # For 1,3: [ Y2*Z2^-1*U3*Y3, U2*Y2*Z1^-1*U2^-1 ]
    Add(mats,[["t",i-2,i],Comm(
              genprod([yind[i-1]])/genprod([zind[i-1]])*genprod([uind[i],yind[i]]),
              genprod([uind[i-1],yind[i-1]])/genprod([uind[i-1],zind[i-2]]))]);
    # for 3,1: [ Y2*Z1^-1*U1*Y1, U2*Y2*Z2^-1*U2^-1 ]
    Add(mats,[["t",i,i-2],Comm(
              genprod([yind[i-1]])/genprod([zind[i-2]])*genprod([uind[i-2],yind[i-2]]),
              genprod([uind[i-1],yind[i-1]])/genprod([uind[i-1],zind[i-1]]))]);
  od;

  # now other $t$ as commutators
  for i in [3..g-1] do
    for j in [1..g-i] do
      a:=First(mats,x->x[1][2]=j and x[1][3]=i+j-1);
      b:=First(mats,x->x[1][2]=i+j-1 and x[1][3]=i+j);
      Add(mats,[["t",j,j+i],Comm(a[2],b[2])]);

      a:=First(mats,x->x[1][3]=j and x[1][2]=i+j-1);
      b:=First(mats,x->x[1][3]=i+j-1 and x[1][2]=i+j);
      Add(mats,[["t",j+i,j],Comm(b[2],a[2])]);
    od;
  od;

    #Add(mats,[Concatenation("O",String(i-1)),
    #          genprod([yind[i-1],uind[i-1],yind[i-1]])^2]);
  hom!.wrds:=mats;

  mats:=[];
  t:=function(i,j)
  local m;
    m:=IdentityMat(2*g);
    m[i][j]:=1;
    return m;
  end;

  for i in [1..g] do
    for j in [i+1..g] do
      Add(mats,[Concatenation("u",String(i),String(j)),t(i,g+j)*t(j,g+i)]);
      Add(mats,[Concatenation("v",String(i),String(j)),t(g+i,j)*t(g+j,i)]);
    od;
    Add(mats,[Concatenation("t",String(i)),t(i,s+i)]);
    Add(mats,[Concatenation("T",String(i)),t(s+i,i)]);
  od;
  hom!.omats:=mats;
  return hom;
end;

oldSPNZFP:=function(n)
local t,geni,m,slmats,gens,f,rels,i,j,k,l,mat,mats,id,nh;
  nh:=n/2;
  if not IsInt(nh) then
    Error("dimension must be even");
  fi;
  t:=function(i,j)
    return slmats[geni[i][j]];
  end;
  geni:=List([1..n],x->[]);
  mats:=[];
  slmats:=[];
  id:=IdentityMat(n,1);
  m:=0;
  for i in [1..n] do
    for j in [1..n] do
      if j<>i then
        m:=m+1;
        geni[i][j]:=m;
        mat:=List(id,ShallowCopy);
        mat[i][j]:=1;
        Add(slmats,mat);
      fi;
    od;
  od;

  gens:=[];
  mats:=[];
  for i in [1..nh] do
    for j in [1..nh] do
      if j<>i then
        Add(gens,Concatenation("T",String(i),String(j)));
        Add(mats,t(i,j)/t(j+nh,i+nh));
      fi;
    od;
  od;

    for i in [1..nh] do
    for j in [1..nh] do
      if j<>i then
        Add(gens,Concatenation("U",String(i),String(j)));
        Add(mats,t(i,j+nh)*t(j,i+nh));
      fi;
    od;
  od;

  for i in [1..nh] do
    for j in [1..nh] do
      if j<>i then
        Add(gens,Concatenation("V",String(i),String(j)));
        Add(mats,t(i+nh,j)*t(j+nh,i));
      fi;
    od;
  od;

  f:=FreeGroup(gens);
  gens:=GeneratorsOfGroup(f);
  rels:=[];
  t:=f/rels;
  m:=Group(mats);
  return GroupHomomorphismByImages(t,m,GeneratorsOfGroup(t),mats);
end;

GeneratorsPCSSL:=function(n,m)
local addgens,one,tij,gens,mat,k,l;

  addgens:=function()
  local m,a;
    for m in tij do
      a:=m^mat;
      if not a in gens then
        Add(gens,a);
      fi;
    od;
  end;

  one:=IdentityMat(n,0);
  tij:=[];
  for k in [1..n] do
    for l in [1..n] do
      if k<>l then
        mat:=List(one,ShallowCopy);
        mat[k][l]:=m;
        Add(tij,mat);
      fi;
    od;
  od;
  gens:=ShallowCopy(tij); # identity conjugator

  for k in [1..n-1] do
    for l in [k+1..n] do
      mat:=Permuted(List(one,ShallowCopy),(k,l));
      addgens();
    od;
    mat:=List(one,ShallowCopy);
    mat[k][k]:=-1;
    mat[k+1][k+1]:=-1;
    mat[k+1][k]:=1;
    addgens();
  od;
  return gens;
end;

# log_10 of 1-norm
ASMatrixHeight:=function(m)
local a,i,j;
  a:=1;
  for i in m do
    for j in i do
      if j>a then
        a:=j;
      elif -j>a then
        a:=-j;
      fi;
    od;
  od;
  return 1+LogInt(a,10);
end;


ASOrbit1Gamma:=function(u)
local s;
  s:=SmithNormalFormIntegerMatTransforms([u]);
  Assert(1,u*s.coltrans*s.rowtrans[1][1]=s.normal[1]);
  return [s.normal[1][1],s.coltrans*s.rowtrans[1][1]];
end;


ASOrbitGamma:=function(u,v)
local d1,d2;
  d1:=ASOrbit1Gamma(u);
  d2:=ASOrbit1Gamma(v);
  if d1[1]=d2[1] then
    return d1[2]/d2[2];
  else
    return false;
  fi;
end;

ASAuxillary1:=function(u,m)
local b,j,k,p,pp;
  p:=Collected(Factors(m));
  pp:=List(p,x->x[1]^x[2]);
  b:=[];
  for j in [1..Length(p)] do
    k:=First([1..Length(u)],
          k->not IsZero((pp[j]/p[j][1])*u[k] mod pp[j]));
    b[j]:=ListWithIdenticalEntries(Length(u),0);
    b[j][k]:=1;
  od;
  #Display(b);
  b:=TransposedMat(b);
  b:=List(b,x->ChineseRem(pp,x));
  Assert(0,Gcd(m,u[1]+Sum([2..Length(u)],x->b[x]*u[x]))=1);
  return b;
end;

ASMultiExtendedGcd:=function(l)
local g,r,i,e;
  g:=l[1];
  r:=[1];
  for i in [2..Length(l)] do
    e:=Gcdex(g,l[i]);
    g:=e.gcd;
    r:=r*e.coeff1;
    Add(r,e.coeff2);
  od;
  return rec(gcd:=g,coeffs:=r);
end;

ASAuxillary2:=function(u,v,I,m)
local IP,n,c,g,x,mat,i,j;
  n:=Length(u);
  if u=v then return IdentityMat(n,1);fi;
  Assert(1,ForAll(I,i->u[i]=v[i]));
  IP:=Difference([1..n],I);
  Assert(1,ForAll(IP,i->IsInt((u[i]-v[i])/m)));
  c:=[];
  g:=ASMultiExtendedGcd(u{I});
  for j in IP do
    x:=(v[j]-u[j]);
    Assert(1,IsInt(x/g.gcd));
    x:=x/g.gcd*g.coeffs;
    c[j]:=[];
    c[j]{I}:=x;
    Assert(1,v[j]=u[j]+Sum(I,i->c[j][i]*u[i]));
  od;
  mat:=IdentityMat(n,1);
  for i in I do
    for j in IP do
      mat[i]:=mat[i]+c[j][i]*mat[j];
    od;
  od;
  Assert(1,u*mat=v);
  return mat;
end;

ASUnimodularPreImage:=function(A,m)
local n,d,adj,da,best,bv,i,j,B,q,g,val;
  #Add(allmats,A);
  n:=Length(A);
  repeat
    d:=DeterminantMat(A);
    if d=1 then return A;fi;

#    # kill negative determinant
#    while d<0 do
#      i:=Random([1..n]);j:=Random([1..n]);
#      B:=List(A,ShallowCopy);
#      B[i][j]:=B[i][j]+m;
#      da:=DeterminantMat(B);
#      if da<d then
#       B[i][j]:=B[i][j]-2*m;
#       da:=DeterminantMat(B);
#      fi;
#      A:=B;
#      d:=da;
#    od;

    adj:=TransposedMat(A^-1*d);
    d:=(d-1)/m; # the missing bit
    da:=AbsInt(d);

    # find the largest entry smaller than d
    best:=fail;
    bv:=da;
    for i in [1..n] do
      for j in [1..n] do
        if adj[i][j]<>0 and da mod AbsInt(adj[i][j])<bv then
          bv:=da mod AbsInt(adj[i][j]);
          best:=[i,j];
        fi;
      od;
    od;
    B:=List(A,ShallowCopy);

    if bv<da then
      q:=QuoInt(d,adj[best[1]][best[2]]);
      B[best[1]][best[2]]:=B[best[1]][best[2]]-q*m;
    else
      # use GCD's of pairs -- rows
      best:=fail;
      bv:=infinity;
      for i in [1..n] do
        for j in Combinations([1..n],2) do
          g:=Gcdex(adj[i][j[1]],adj[i][j[2]]);
          if g.gcd<>0 then
            val:=QuoInt(da,AbsInt(g.gcd))
              *Maximum(AbsInt(g.coeff1),AbsInt(g.coeff2));
            if val<>0 and val<bv then
              bv:=val;
              best:=[i,j,g];
            fi;
          fi;
        od;
      od;
      if best<>fail then
        i:=best[1]; j:=best[2]; g:=best[3];
        q:=QuoInt(d,g.gcd);
        B[i][j[1]]:=B[i][j[1]]-q*m*g.coeff1;
        B[i][j[2]]:=B[i][j[2]]-q*m*g.coeff2;
      else
        # use GCD's of pairs -- columns
        bv:=infinity;
        for i in [1..n] do
          for j in Combinations([1..n],2) do
            g:=Gcdex(adj[j[1]][i],adj[j[2]][i]);
            if g.gcd<>0 then
              val:=QuoInt(da,AbsInt(g.gcd))
                *Maximum(AbsInt(g.coeff1),AbsInt(g.coeff2));
              if val<>0 and val<bv then
                bv:=val;
                best:=[i,j,g];
              fi;
            fi;
          od;
        od;
        if best<>fail then
          i:=best[1]; j:=best[2]; g:=best[3];
          q:=QuoInt(d,g.gcd);
          B[j[1]][i]:=B[j[1]][i]-q*m*g.coeff1;
          B[j[2]][i]:=B[j[2]][i]-q*m*g.coeff2;
        else
          # fall back on SNF.
          d:=SmithNormalFormIntegerMatTransforms(B);
          q:=0;
          # ad-hoc treatment for for SNF with diagonal not 1..1,x
          while not ForAll([1..n-1],x->d.normal[x][x]=1) do
            i:=Random([1..n]);
            j:=Random([1..n]);
            B[i][j]:=B[i][j]+Random([1,-1])*m;
            d:=SmithNormalFormIntegerMatTransforms(B);
            q:=q+1;
            Info(InfoArithSub,2,"iter",q);
            if q>20 then Error("infinite loop? return;");q:=0;fi;
          od;
          q:=One(d.normal);
          if d.signdet=-1 then
            q:=List(q,ShallowCopy);
            q[n][n]:=-1;
          fi;
          return d.rowtrans^-1*q*d.coltrans^-1;

          Error("not yet done");
          return fail;
        fi;
      fi;
    fi;

    A:=B;
  until DeterminantMat(B)=1;
  return B;

end;

ASOrbitGammaM:=function(uo,v,m)
local n,a,b,t,u,c,w,r,s1,s2,s3,s,g;
  n:=Length(uo);
  a:=ASOrbit1Gamma(v);
  b:=ASOrbit1Gamma(uo);
  if a[1]<>b[1] then return false;fi; # OrbitGamma(u,v) test
  t:=a[2];
  a:=a[1];
  if ForAny([1..n],i->(uo[i]-v[i]) mod (a*m)<>0) then return false;fi;
  if uo=v then return IdentityMat(n,1);fi;
  u:=1/a*(uo*t);
  r:=1-u[1];
  Assert(1,IsInt(r/m));

  if r=0 then
    c:=u[2];
  else
    b:=[u[2]];
    for w in [3..Length(u)] do
      Add(b,r*u[w]);
    od;
    b:=ASAuxillary1(b,u[1]);
    c:=u[2]+r*Sum([3..n],i->b[i-1]*u[i]);
    Assert(1,Gcd(u[1],c)=1);
  fi;

  if n>=3 then
    w:=ShallowCopy(u);
    w[2]:=c;
    s1:=ASAuxillary2(u,w,[3..n],m);
    s2:=0*u;
    s2[1]:=u[1];
    s2[2]:=c;
    s2[3]:=r;
    s2:=ASAuxillary2(w,s2,[1,2],m);
  fi;
  if n=2 then
    Error("s=h");
  else
    s3:=IdentityMat(n,1);
    s3[1]:=s3[1]+s3[3];
    s3[2]:=s3[2]-c*s3[1];
    s3[3]:=s3[3]-r*s3[1];
    s3[1]:=s3[1]-s3[3];
    s3:=TransposedMat(s3);
    s:=s1*s2*s3;
  fi;
  g:=t*s/t;
  Assert(1,uo*g=v);
  return g;
end;

ASOnLinesModuloFunc:=function(arg)
local R,U,sub,orbs,invs,stbs,start,prepareSub,fct,en,n,addvecs;

  prepareSub:=function(p)
  local orb;
    if not IsBound(orbs[p]) then
      orb:=Orbits(sub[p],Elements(R),OnRight);
      orb:=List(orb,Set);
      orbs[p]:=orb;
      stbs[p]:=List(orb,x->Position(sub,Stabilizer(sub[p],x[1],OnRight)));
      invs[p]:=List([1..Length(orb)],x->List(orb[x],y->
      First(RightTransversal(sub[p],sub[stbs[p][x]]),z->orb[x][1]*z=y)^-1));
    fi;
  end;

  R:=arg[1];
  U:=Units(R);
  sub:=List(ConjugacyClassesSubgroups(U),Representative);
  orbs:=[];
  invs:=[];
  stbs:=[];
  start:=Position(sub,U); # trigger for whole group
  prepareSub(start);

  fct:=function(v,g)
  local p,i,a,b,n;
    v:=OnPoints(v,g);
    n:=Length(v);
    p:=PositionNonZero(v);
    a:=start;
    while Size(sub[a])>1 and p<=n do
      prepareSub(a);
      i:=0;
      b:=fail;
      while b=fail do;
        i:=i+1;
        b:=Position(orbs[a][i],v[p]);
      od;
      v:=invs[a][i][b]*v;
      a:=stbs[a][i];
      p:=p+1;
    od;
    return v;
  end;

  if Length(arg)=1 then
    return fct;
  elif IsPosInt(arg[2]) then
    n:=arg[2];
    en:=[];

    addvecs:=function(seed,stb,p)
    local i,v;
      prepareSub(stb);
      for i in [1..Length(orbs[stb])] do
        v:=ShallowCopy(seed);
        v[p]:=orbs[stb][i][1];
        if p=n then
          MakeImmutable(v);
          AddSet(en,v);
        else
          addvecs(v,stbs[stb][i],p+1);
        fi;
      od;
    end;

    addvecs(ListWithIdenticalEntries(n,Zero(R)),start,1);
    return [fct,en];
  fi;
  Error("wrong arguments");
end;

ASBestPreImg:=function(A,m,gens)
local c,d;
  if IsObjWithMemory(A) then
    c:=ResultOfStraightLineProgram(SLPOfElm(A),gens);
  else
    c:=fail;
  fi;
  A:=List(A,x->List(x,Int));
  d:=ASUnimodularPreImage(A,m);
  if d=fail then
    Error("QQQ");
  fi;
#Print("c",ASMatrixHeight(c),"\n");
#if d<>fail then
#  Print("d",ASMatrixHeight(d),"\n");
#fi;
  if  (c=fail or ASMatrixHeight(c)>ASMatrixHeight(d)) then
    #Print("unimo\n");
    return d;
  else
    #Print("word\n");
    return c;
  fi;
end;

ASStabPCS:=function(u,m)
  local n,t,can,gens,hom,i,s,sigma,a,j;
  n:=Length(u);
  t:=ASOrbit1Gamma(u);
  t:=t[2]^-1;
  can:=u/t;
  gens:=[];
  hom:=SLNZFP(n);
  hom:=MappingGeneratorsImages(hom)[2];
  for i in hom do
    # as we don't know the index numbers, test stabilization
    if can*i=can then
      AddSet(gens,i^m);
    fi;
  od;
  hom:=SLNZFP(n-1);
  hom:=MappingGeneratorsImages(hom)[2];
  sigma:=[IdentityMat(n-1,1)];
  for i in [1..n-2] do
    for j in [i+1..n-1] do
      a:=IdentityMat(n-1,1);
      a:=Permuted(a,(i,j));
      Add(sigma,a);
    od;
    a:=IdentityMat(n-1,1);
    a[i][i]:=-1;
    a[i+1][i+1]:=-1;
    a[i+1][i]:=1;
    Add(sigma,a);
  od;

  for i in hom do
    for s in sigma do
      a:=IdentityMat(n,1);
      a{[2..n]}{[2..n]}:=((i^m)^s);
      AddSet(gens,a);
    od;
  od;
  return List(gens,x->x^t);
end;

# set v=fail to get the blocks orbit
ASDoOrbitStab:=function(gens,u,v,m,mode)
local ff,n,ring,one,u1,v1,u2,v2,gens1,orb,d,t,stabgens,stabsub,o,i,img,p,
  post,poss,vo,s,gp,actfun,mm,mo,facact,radact,ml,fggens,orblen;

  orblen:=1;

  n:=Length(u);
  vo:=v;

  # first find an element that maps u to v modulo m

  ring:=Integers mod m;
  one:=One(ring);
  u1:=u*one;
  gens1:=List(gens,x->x*one);

  #gens1:=GeneratorsWithMemory(gens1);
  # do clever orbit algorithm using recognition
  gp:=Group(gens1);
  ff:=FittingFreeLiftSetup(gp);
  p:=MappingGeneratorsImages(ff.pcisom);
  o:=MappingGeneratorsImages(ff.factorhom);

  if not IsPrime(m) then
    # work in steps
    mo:=Reversed(Factors(m));
    mo:=List([1..Length(mo)],x->Product(mo{[1..x]}));
    orb:=rec(stabradgens:=p[1],stabrsubsz:=Size(Image(ff.pcisom)),
             stabfacgens:=o[1],stabfacimgs:=o[2],subsz:=Size(gp));
    post:=One(gens[1]);
    ml:=1;
#mo:=[m];
    for mm in mo do

      radact:=orb.stabradgens;
      facact:=orb.stabfacgens;
      u2:=u1;
      if mm<m then
        radact:=List(radact,x->ReduceModM(x,mm));
        facact:=List(facact,x->ReduceModM(x,mm));
        u2:=ReduceModM(u2,mm);
      fi;

      d:=Enumerator((Integers mod mm)^n);

      if mm/ml>10 then
        # projective first
        if IsPrimeInt(mm) then
          actfun:=OnLines;
        else
          actfun:=ASOnLinesModuloFunc(Integers mod mm);
        fi;
        fggens:=orb.stabfacgens;
        orb:=OrbitStabRepsMultistage(orb.stabradgens,
              radact,ff.pcisom,
          orb.stabrsubsz,TrivialSubgroup(Image(ff.pcisom)),
          orb.stabfacgens,facact,orb.stabfacimgs,
          ff.factorhom,orb.subsz,actfun,d,actfun(u2,ReduceModM(One(gp),mm)));
        orblen:=orblen*orb.len;
        Info(InfoArithSub,2,"Modulo ",mm," length projectively ",orb.len);

        if v<>fail then
          v2:=actfun(ReduceModM(v,mm),ReduceModM(One(gp),mm));
          p:=Position(orb.orbit,v2);
          if p=fail then return false;fi; # not image mod m mod scalars;

          if IsBound(orb.reps[p]) then
            # rep is given directly
            poss:=orb.reps[p];
          else
            # need to use repwords
            d:=One(gens[1]);
            for i in orb.repwords[p] do
              d:=d*fggens[i];
            od;
            p:=Position(orb.orbit,actfun(ReduceModM((v*one)/(d*one),mm),
                 ReduceModM(One(gp),mm)));
            poss:=orb.reps[p];
            poss:=poss*d;
          fi;
          poss:=ASBestPreImg(poss,m,gens);
          v:=v/poss;
          post:=poss*post;
        fi;

        radact:=orb.stabradgens;
        facact:=orb.stabfacgens;
        if mm<m then
          radact:=List(radact,x->ReduceModM(x,mm));
          facact:=List(facact,x->ReduceModM(x,mm));
        fi;

      fi;

      fggens:=orb.stabfacgens;
      orb:=OrbitStabRepsMultistage(orb.stabradgens,
            radact,ff.pcisom,
        orb.stabrsubsz,TrivialSubgroup(Image(ff.pcisom)),
        orb.stabfacgens,facact,orb.stabfacimgs,
        ff.factorhom,orb.subsz,OnRight,d,u2);
      orblen:=orblen*orb.len;
      Info(InfoArithSub,2,"Modulo ",mm," length ",orb.len);

      if v<>fail then
        p:=Position(orb.orbit,ReduceModM(v*one,mm));
        if p=fail then return false;fi; # not image mod m mod scalars;

        if IsBound(orb.reps[p]) then
          # rep is given directly
          poss:=orb.reps[p];
        else
          # need to use repwords
          d:=One(gens[1]);
          for i in orb.repwords[p] do
            d:=d*fggens[i];
          od;
          p:=Position(orb.orbit,ReduceModM((v*one)/(d*one),mm));
          poss:=orb.reps[p];
          poss:=poss*d;
        fi;
        poss:=ASBestPreImg(poss,m,gens);
        v:=v/poss;
        post:=poss*post;
      fi;

      ml:=mm;
    od;
    if v<>fail then
      # clean up the accumulated post
      post:=ASUnimodularPreImage(post mod m,m);
      v:=vo/post;
    fi;

  elif false and m>1 then

    if false then
      actfun:=ASOnLinesModuloFunc(ring,n);
      d:=actfun[2];
      actfun:=actfun[1];
    else
      d:=Enumerator(ring^n);
      actfun:=ASOnLinesModuloFunc(ring);
    fi;

    u2:=actfun(u1,One(gp));

    orb:=OrbitStabRepsMultistage(p[1],p[1],ff.pcisom,
      Size(Image(ff.pcisom)),TrivialSubgroup(Image(ff.pcisom)),o[1],o[1],o[2],
                  ff.factorhom,Size(gp),actfun,d,u2);

    orblen:=orblen*orb.len;
    Info(InfoArithSub,2,"Modulo ",m," projective length ",orb.len," in ",
         Size(d));

    if v<>fail then
      v2:=actfun(v*one,One(gp));
      p:=Position(orb.orbit,v2);
      if p=fail then return false;fi; # not image mod m mod scalars;

      if IsBound(orb.reps[p]) then
        # rep is given directly
        poss:=orb.reps[p];
        poss:=ASBestPreImg(poss,m,gens);
      else
        # need to use repwords
        d:=One(gens[1]);
        for i in orb.repwords[p] do
          d:=d*gens[i];
        od;
        p:=Position(orb.orbit,actfun((v*one)/(d*one),One(gp)));
        poss:=orb.reps[p];
        poss:=ASBestPreImg(poss,m,gens);
        poss:=poss*d;
      fi;
      v:=v/poss;
    fi;

    orb:=OrbitStabRepsMultistage(orb.stabradgens,
          orb.stabradgens,ff.pcisom,
      orb.stabrsubsz,TrivialSubgroup(Image(ff.pcisom)),
      orb.stabfacgens,orb.stabfacgens,orb.stabfacimgs,
      ff.factorhom,orb.subsz,OnRight,d,u1);

    orblen:=orblen*orb.len;
    Info(InfoArithSub,2,"Modulo ",m," length ",orb.len);
    if v<>fail then
      p:=Position(orb.orbit,v*one);
      if p=fail then return false;fi; # not image mod m;

      if IsBound(orb.reps[p]) then
        # rep is given directly
        post:=orb.reps[p];
        post:=ASBestPreImg(post,m,gens);
      else
        # need to use repwords
        d:=One(gens[1]);
        for i in orb.repwords[p] do
          d:=d*gens[i];
        od;
        p:=Position(orb.orbit,(v*one)/(d*one));
        post:=orb.reps[p];
        post:=ASBestPreImg(post,m,gens);
        post:=post*d;
      fi;

      # since Gamma_m is contained in G we can simply take the natural preimage
      Assert(1,DeterminantMat(post)=1);

      v:=v/post;
    fi;

  else

    d:=Enumerator(ring^n);
    orb:=OrbitStabRepsMultistage(p[1],p[1],ff.pcisom,
      Size(Image(ff.pcisom)),TrivialSubgroup(Image(ff.pcisom)),o[1],o[1],o[2],
                  ff.factorhom,Size(gp),OnRight,d,u1);

    orblen:=orblen*orb.len;
    Info(InfoArithSub,2,"Modulo ",m," length ",orb.len);
    if v<>fail then
      p:=Position(orb.orbit,v*one);
      if p=fail then return false;fi; # not image mod m;

      if IsBound(orb.reps[p]) then
        # rep is given directly
        post:=orb.reps[p];
        post:=ASBestPreImg(post,m,gens);
      else
        # need to use repwords
        d:=One(gens[1]);
        for i in orb.repwords[p] do
          d:=d*gens[i];
        od;
        p:=Position(orb.orbit,(v*one)/(d*one));
        post:=orb.reps[p];
        post:=ASBestPreImg(post,m,gens);
        post:=post*d;
      fi;

      # since Gamma_m is contained in G we can simply take the natural preimage
      Assert(1,DeterminantMat(post)=1);

      v:=v/post;
    fi;

  fi;

  stabgens:=Concatenation(orb.stabradgens,orb.stabfacgens);

  if v<>fail then
    d:=ASOrbitGammaM(u,v,m);
    if d<>false then
      d:=d*post;
      Assert(1,u*d=vo);
      return d;
    fi;
  fi;

  stabgens:=List(stabgens,x->ASBestPreImg(x,m,gens));
  Assert(1,ForAll(stabgens,y->DeterminantMat(y)=1));

  if mode=1 then
    # orbit representative version

    # now act on Gamma_m orbits, using the mod-m orbit test
    orb:=[u];
    d:=false; # empty cache
    t:=[One(gens[1])];
    o:=1;
    while o<=Length(orb) do
      for i in [1..Length(stabgens)] do
        img:=orb[o]*stabgens[i];
        d:=false;
        # find which block we are in, if any
        p:=0;
        while p<Length(orb) and d=false do
          p:=p+1;
          d:=ASOrbitGammaM(img,orb[p],m);
        od;
        if d=false then
          if v<>fail then
            # test whether we found the block with v.
            d:=ASOrbitGammaM(img,v,m);
            if d<>false then
              Info(InfoArithSub,2,"Used ",Length(orb)," blocks");
              d:=t[o]*stabgens[i]*d*post;
              Assert(1,u*d=vo);
              Info(InfoArithSub,2,"orblen=",Length(orb)*orblen);
              return d;
            fi;
          fi;
          Add(orb,img);
          Add(t,t[o]*stabgens[i]);
        fi;
      od;
      o:=o+1;
    od;
    orblen:=orblen*Length(orb);
    Print("orblen=",Length(orb)*orblen,"\n");
    if v=fail then return orb;fi;
    return false;
  else
    # stabilizer version

    d:=[u];
    # function for action on Gamma_m orbits, represented by ``canonical'' reps
    actfun:=function(v,a)
    local i;
      v:=v*a;
      for i in d do
        if ASOrbitGammaM(v,i,m)<>false then
          return i;
        fi;
      od;
      Add(d,v);
      return v;
    end;

    orb:=OrbitStabRepsMultistage(orb.stabradgens,
          stabgens{[1..Length(orb.stabradgens)]},ff.pcisom,
      orb.stabrsubsz,TrivialSubgroup(Image(ff.pcisom)),
        orb.stabfacgens,stabgens{[Length(orb.stabradgens)+1..Length(stabgens)]},
        orb.stabfacimgs,
                  ff.factorhom,orb.subsz,actfun,false,u);
    Print("orblen=",orblen*orb.len,"=",orblen,"*",orb.len,"\n");
    orblen:=orblen*orb.len;

    stabgens:=Concatenation(orb.stabradgens,orb.stabfacgens);
    stabgens:=List(stabgens,x->ASBestPreImg(x,m,gens));
    Assert(1,ForAll(stabgens,y->DeterminantMat(y)=1));

    # correct stabilizing generators
    for i in [1..Length(stabgens)] do
      d:=ASOrbitGammaM(u*stabgens[i],u,m);
      stabgens[i]:=stabgens[i]*d;
    od;

    d:=ASStabPCS(u,m);
    return Concatenation(stabgens,d);

  fi;

end;

# set v=fail to get the blocks orbit
ASOrbit:=function(G,u,v,m)

  if v<>fail and ASOrbitGamma(u,v)=false then
    return false;
  fi;

  return ASDoOrbitStab(GeneratorsOfGroup(G),u,v,m,1);
end;

ASStabilizerGens:=function(G,u,m)
  return ASDoOrbitStab(GeneratorsOfGroup(G),u,fail,m,2);
end;

# Part 4: Group Examples

#Long/Reid examples

b1beta:=function(G)
local x,y;
  x:=G.1;
  y:=G.2;
  #x:=x^-1*y*y*y*x*y*y*x/y*x;
  x:=y*y*x*y*y*x;
  return x;
end;

BetaT:=function(T)
local G;
  G:= Group([[-1+T^3,-T,T^2],[0,-1,2*T],[-T,0,1]],
               [[-1,0,0],[-T^2,1,-T],[T,0,-1]],
               [[0,0,1],[1,0,T^2],[0,1,0]]);
  G!.unipotent:=b1beta(G);
  return G;
end;

RhoK:=function(k)
local G,x,y,a,b;
  G:= Group([[1,-2,3],[0,k,-1-2*k],[0,1,-2]],
               [[-2-k,-1,1],[-2-k,-2,3],[-1,-1,2]],
               [[0,0,1],[1,0,-k],[0,1,-1-k]]);
  x:=G.1;
  y:=G.2;
  if k=0 then
    a:=x^2*y^-3*x*y*x^-1;b:=x^-1*y*x*y^-3*x^2;
    G!.unipotent:=a*b;
  elif k=2 then
    a:=x^3*(y*x)^3*y;
    b:=y^-1*x^-1*y*x*y^-1*x*y*x^-1*y^-1;
    G!.unipotent:=a*b/a/b;
  elif k=3 then
    a:=y*x^-2*y*x^3;
    b:=x^-3*y*x^4*y;
    G!.unipotent:=a*b;
  elif k=4 then
    a:=(x*y)^2*(y*x)^-2*x^2*y^-1*x^-2*y;
    b:=y*x^-2*y^-1*x^2*(x*y)^-2*(y*x)^2;
    G!.unipotent:=a*b;
  elif k=5 then
    a:=y*x^-3*y*x^-1*y^-1*x*y^-1*x^-1;
    b:=x^-1*y^-1*x*y^-1*x^-1*y*x^-3*y;
    G!.unipotent:=a*b;
  fi;

  return G;
end;

#KacVinberg:=Group([[2,2,-1],[0,1,0],[1,1,1]],
#            [[1,0,0],[3,0,-1],[1,1,-1]],[[1,-1,2],[2,-1,1],[0,0,1]]);

LongReidThistle:=function(t)
  return Group([[0,0,1],[1,0,0],[0,1,0]],
               [[1,2-t+t^2,3+t^2],[0,-2+2*t-t^2,-1+t-t^2],
               [0,3-3*t+t^2,(-1+t)^2]]);
end;

LongThistle:=function(k)
  return Group([[k*(3-4*k+4*k^2),-1-4*k-8*k^2 +16*k^3 -16*k^4,0,0],
                [1-k+k^2,-1-3*k+4*k^2 -4*k^3,0,0],
                [k*(1-2*k+2*k^2),-3-4*k-2*k^2 +8*k^3 -8*k^4,1,0],
                [2*(1-k+k^2),-2*(1+2*k-4*k^2 +4*k^3),0,1]],
               [[1,0,-4,0],[0,1,0,-1],[0,0,-1,-1],[0,0,1,0]]);
end;

HofmannStraatenExample:=function(d,k)
  return
  Group([[1,1,0,0],[0,1,0,0],[d,d,1,0],[0,-k,-1,1]],
        [[1,0,0,0],[0,1,0,1],[0,0,1,0],[0,0,0,1]]);
end;

HumphriesFreeSubgroupThree:=function(x)
return Group([[1,x^2+1,x],[0,1,0],[0,0,1]],[[1,0,0],[x,1,x+1],[0,0,1]],
  [[1,0,0],[0,1,0],[-x+1,x^2,1]]);
end;

# Part5: Find primes

CongruenceImageOfGroup:=function(g,prime)
local red,modfun,maz,f;
  red:=PrepareReductionInfo(
    Char0ScalarDomainMatrixList(GeneratorsOfGroup(g)));
  modfun:=prime.redfun;
  maz:=List(GeneratorsOfGroup(g),m->List(m,r->List(r,modfun)));
  if Characteristic(Flat(maz))<>fail then
    f:=Field(Set(Flat(maz)));
    if Size(f)<=256 then
      maz:=List(maz,x->ImmutableMatrix(f,x));
    fi;
  fi;
  return Group(maz);
end;

IsSmallerCongruenceImage:=function(g,prime)
local a;
  a:=CongruenceImageOfGroup(g,prime);
  return Size(a)<Size(SL(2,FieldOfMatrixGroup(a)));
end;

# utility fct to find irrelevant prime
DetermineIrrelevantPrime:=function(H,kind,bound)
local test,irr,ind,good,bad,denom,HM,f,dim,ring,redinfo,a,b,modfun,p;

  # caching
  if IsBound(H!.IrrprimeInfo) and H!.IrrprimeInfo.irr.p>bound and
    H!.IrrprimeInfo.irr<>false then
    return H!.IrrprimeInfo;
  fi;

  dim:=Length(One(H));

  kind:=CheckProperKind([H,kind],2);

  # ring
  ring:=Char0ScalarDomainMatrixList(GeneratorsOfGroup(H));
  bad:=ring[2];
  redinfo:=PrepareReductionInfo(ring);
  denom:=[];
  if bad=1 then
    bad:=[];
  else
    denom:=Union(denom,Set(Factors(bad)));
    bad:=Union(List(Set(Factors(bad)),redinfo.primesinprime));
  fi;

  # do this only over Z
  if not ForAny(Flat(GeneratorsOfGroup(H)),x->IsRat(x) and not IsInt(x))
    and ValueOption("skipring")<>true then
    # Give warnings about ring spanned by generator entries

    ind:=ZIdealBasis(redinfo.bas,[1],Flat(GeneratorsOfGroup(H)):denom:=denom);
    f:=AbsInt(DeterminantMat(ind.mat));
    if f<>1 then
      Print("\nWARNING: Matrix extries only generate ring of index ",f,"\n");
    fi;
  fi;

  # good/bad primes

  good:=[];
  f:=ValueOption("badprimes");
  if f<>fail then
    bad:=Union(bad,f);
    denom:=Union(denom,f);
  fi;

  # special treatment of 2,3 in small dimensions
  if dim<=4 then
    if redinfo.case=1 then

      irr:=1;
      if dim=3 or dim=4 then
        if not (2 in bad or 2 in denom) then irr:=4;fi;
      elif dim=2 then
        if 2 in denom then
          if 3 in denom then
            irr:=1;
          else
            irr:=9;
          fi;
        elif 3 in denom then
          irr:=4;
        else
          irr:=36;
        fi;
      fi;
      if irr>1 then

        test:=function(modulus)
          local a;
            a:=Integers mod modulus;
            #a:=List(GeneratorsOfGroup(H),x->ZmodnZMat(a,x*One(a)));
            a:=List(GeneratorsOfGroup(H),x->Matrix(a,x*One(a)));
            a:=Group(a);
            if ForAny(GeneratorsOfGroup(a),x->not IsOne(x)) then
              FittingFreeLiftSetup(a);
            fi;
            if kind=SL then
              return Size(SL(dim,Integers mod modulus))/Size(a);
            elif kind=SP then
              return Size(SP(dim,Integers mod modulus))/Size(a);
            else Error("kind");fi;
          end;

        ind:=test(irr);
        if ind>1 then
          if irr=36 then # 2/3 case
            if ind=test(4) then
              AddSet(good,2);
            elif ind=test(9) then
              AddSet(good,3);
            else
              AddSet(good,2);
              AddSet(good,3);
            fi;
          else
            AddSet(good,SmallestPrimeDivisor(irr));
          fi;
        fi;
      fi;
    else
      Print("warning -- small dim cases not implemented yet\n");
    fi;
  fi;

  if kind=SL then
    test:=function(G,number)
      return IsNaturalSL(G) and
      Size(DefaultFieldOfMatrixGroup(G))=number.fieldsize;
    end;
  else
    test:=function(G,number)
    local q,r;
      r:=RecognizeGroup(G);
      q:=DefaultFieldOfMatrixGroup(G);
      return Size(r)=Size(SP(Length(One(G)),q)) and
          Size(DefaultFieldOfMatrixGroup(G))=number.fieldsize;
    end;
  fi;

  # discriminant and dimension
  if redinfo.case>1 then
    for irr in redinfo.primesinnumber(redinfo.discriminant*dim) do
      if not irr in bad then
        modfun:=irr.redfun;
        HM:=List(GeneratorsOfGroup(H),m->List(m,r->List(r,modfun)));
        HM:=Group(HM);
        if not test(HM,irr) then Add(good,irr);
        else Add(bad,irr);fi;
      fi;
    od;
  fi;

  f:=ValueOption("densitytest");
  if f<>fail then
    irr:=false;
  else
    irr:=ValueOption("irrelevant");
  fi;


  # try to find irrelevant prime that is integer
  if irr=fail then
    a:=1;
    repeat
      repeat
        a:=NextPrimeInt(a);
        irr:=redinfo.primesinprime(a);
        # avoid preset/known primes
        irr:=Filtered(irr,x->not x in denom);
        irr:=Filtered(irr,x->not x in good);

      until Length(irr)>0 and not a in denom;
      irr:=irr[1]; # pick first

      f:=irr;
      if IsRecord(f) and IsBound(f.ideal) then f:=f.ideal;fi;
      Info(InfoArithSub,2,"Try irr=",f);

      if irr=10007 then # first prime >10000.
        if ValueOption("mayfail")=true then return fail;fi;
        # maybe its not dense
        if not IsDenseIR2(H) then
          Error("The input group is not dense");
        fi;
      fi;

      modfun:=irr.redfun;
      HM:=List(GeneratorsOfGroup(H),m->List(m,r->List(r,modfun)));
      HM:=Group(HM);
      if not test(HM,irr) then Add(good,irr);fi;
    until not irr in good and a>bound;
  fi;
  Info(InfoArithSub,1,"irrelevant prime ",irr.ideal);

  irr:=rec(irr:=irr,good:=good,bad:=bad,denom:=denom,test:=test,kind:=kind,
    red:=redinfo);

  H!.IrrprimeInfo:=irr;
  # do this only over Z
  if not ForAny(Flat(GeneratorsOfGroup(H)),x->IsRat(x) and not IsInt(x))
      and ValueOption("skipring")<>true then

    # check Trace ring

    # basis enveloping algebra
    #b:=ZEnvelopingAlgebraBasis(H,false);

    b:=[Concatenation(One(H))];
    b:=RegModZSpan(GeneratorsOfGroup(H),b,irr.irr.redfun,redinfo);
    # sum up trace for each
    a:=DimensionOfMatrixGroup(H);
    # trace positions
    b:=Set(List(b,y->Sum([1..a],x->y[x+a*(x-1)])));

    # Need to expand with factors
    a:=ShallowCopy(b);
    for f in [2..Length(redinfo.bas)] do
      Append(b,redinfo.bas[f]*a);
    od;

    ind:=ZIdealBasis(redinfo.bas,[1],b);
    if Length(ind.mat)<Length(ind.mat[1]) then
      f:=infinity;
    else
      f:=AbsInt(DeterminantMat(ind.mat));
    fi;
    if f<>1 then
      Print("\nWARNING: Traces only generate ring of index ",f,"\n\n");
      irr.traceringgens:=ind.mgens;
    fi;
  fi;

  return irr;
end;

GcdTrivialModuloImage:=function(m,redu)
local n,i,j,gcd;
  n:=Length(m);
  gcd:=[];
  for i in [1..n] do
    for j in Difference([1..n],[i]) do
      Add(gcd,m[i][j]);
    od;
    Add(gcd,m[i][i]-1);
  od;
  gcd:=Gcd(List(gcd,redu.normval));
  if IsList(gcd) and gcd[1]=fail then gcd:=gcd[2];fi; # possibly too big
  return gcd;
end;

PrimesByExponentBound:=function(g,e)
local n,mats,pr,prim,m,p,i,j;
  n:=DimensionOfMatrixGroup(g);
  mats:=GeneratorsOfGroup(g);
  mats:=Filtered(mats,x->Order(x)=infinity);
  while Length(mats)=0 do
    mats:=List([1..Length(GeneratorsOfGroup(g))],x->ASPseudoRandom(g));
    mats:=Filtered(mats,x->Order(x)=infinity);
  od;
  mats:=List(mats,x->x^e);
  prim:=fail;
  for m in mats do
    pr:=GcdTrivialModuloImage(m);
    if prim=fail then
      prim:=pr;
    else
      prim:=Gcd(prim,pr);
    fi;
  od;
  return Set(Factors(prim));
end;

NumberForElementOrder:=function(g,ord)
local n,mats,pr,prim,m,p,i,d,pow,j,k,gcd,red;
  n:=DimensionOfMatrixGroup(g);
  red:=g!.IrrprimeInfo.red;
  repeat
    m:=ASPseudoRandom(g);
  until Order(m)=infinity;

  prim:=1;
  pow:=m;
  for i in [1..ord] do # that is power 2..ord+1
    pow:=pow*m;
    d:=pow-m;
    pr:=[];
    for j in [1..Length(d)] do
      for k in [1..Length(d)] do
        Add(pr,d[j][k]);
      od;
    od;
    pr:=Gcd(List(pr,red.normval));
    if IsList(pr) and pr[1]=fail then pr:=pr[2];fi; # possibly too big
    prim:=prim*pr;
  od;

  return prim;
end;

PrimesByNontrivialCommutators:=function(g,lev)
local doit,n,i,j,p,pr,m,s,irr,red;

  irr:=DetermineIrrelevantPrime(g,0,2); # often cached
  red:=irr.red;
  irr:=irr.irr;

  s:=0;

  doit:=function(l)
  local a,b,c,switch;
    if l=0 then
      repeat
        a:=Random(GeneratorsOfGroup(g));
        b:=Random(GeneratorsOfGroup(g));
        switch:=Random([1..14]);
        if switch=1 then
          c:=a;
        elif switch=2 then
          c:=b;
        elif switch<=4 then
          c:=a*b;
        elif switch<=6 then
          c:=b*a;
        elif switch<=8 then
          c:=a/b;
        elif switch<=10 then
          c:=b/a;
        elif switch<=12 then
          c:=LeftQuotient(a,b);
        elif switch<=14 then
          c:=LeftQuotient(b,a);
        fi;
      until not IsOne(c);
      #c:=c^pow;
    else
      a:=doit(l-1);
      b:=doit(l-1);
      c:=Comm(a,b);
      switch:=true;
      while IsOne(c) do
        if switch then
          a:=doit(l-1);
        else
          b:=doit(l-1);
        fi;
        switch:=not switch;
        c:=Comm(a,b);
      od;
    fi;
    if l>s then
      Info(InfoArithSub,3,"Success Level :",l);
      s:=l;
    fi;
    return c;
  end;

  m:=doit(lev);
  return GcdTrivialModuloImage(m,red);
end;

NumberForMonomial:=function(g,k)
local rad,a,b,c,red;
  rad:=5;
  repeat
    a:=ASPseudoRandom(g:radius:=Int(rad));
    b:=ASPseudoRandom(g:radius:=Int(rad));
    c:=Comm(a^k,b^k);
    rad:=rad+1/10;
  until not IsOne(c) and Order(a)=infinity;
  return GcdTrivialModuloImage(c,
    DetermineIrrelevantPrime(g,0,2).red
    );
end;

NumberAbsReducibleSecondDerived:=function(g)
local doit,n,i,j,p,pr,m,s,irr,h,l,a;

  irr:=DetermineIrrelevantPrime(g,0,2); # often cached

  s:=0;

  doit:=function(l)
  local a,b,c,switch;
    if l=0 then
      repeat
        a:=Random(GeneratorsOfGroup(g));
        b:=Random(GeneratorsOfGroup(g));
        switch:=Random([1..14]);
        if switch=1 then
          c:=a;
        elif switch=2 then
          c:=b;
        elif switch<=4 then
          c:=a*b;
        elif switch<=6 then
          c:=b*a;
        elif switch<=8 then
          c:=a/b;
        elif switch<=10 then
          c:=b/a;
        elif switch<=12 then
          c:=LeftQuotient(a,b);
        elif switch<=14 then
          c:=LeftQuotient(b,a);
        fi;
      until not IsOne(c);
      #c:=c^pow;
    else
      a:=doit(l-1);
      b:=doit(l-1);
      c:=Comm(a,b);
      switch:=true;
      while IsOne(c) do
        if switch then
          a:=doit(l-1);
        else
          b:=doit(l-1);
        fi;
        switch:=not switch;
        c:=Comm(a,b);
      od;
    fi;
    return c;
  end;

  l:=[];
  repeat
    for i in [1..5] do
      a:=doit(2);
      if not IsOne(a) then Add(l,a);fi;
    od;
  until Length(l)>0 and irr.test(ModularImageMatrixGroup(Group(l),
    irr.irr.redfun),irr.irr);
  h:=Group(l);
  h!.IrrprimeInfo:=irr;
  return NumberNotAbsIrr(h);
end;

NumberForImprimitive:=function(g,k)
local rad,a,l,h,irr,i;
  irr:=DetermineIrrelevantPrime(g,0,3);
  rad:=1;
  l:=[];
  repeat
    for i in [1..5] do
      a:=ASPseudoRandom(g:radius:=Int(rad))^k;
      if not IsOne(a) then Add(l,a);fi;
      rad:=rad+1/3;
    od;
  until Length(l)>0 and
    irr.test(ModularImageMatrixGroup(GroupByGenerators(l),irr.irr.redfun),
    irr.irr);
  h:=GroupByGenerators(l);
  h!.IrrprimeInfo:=irr;
  return NumberNotAbsIrr(h);
end;

PrimesByTraceInverseGaloisCommutator:=function(g,co,au)
local rad,a,b,t,cnt,p,red,cou;
  red:=DetermineIrrelevantPrime(g,-1,-1).red;
  rad:=1;
  cnt:=0;
  p:=0;
  repeat
    cou:=0;
    repeat
      a:=ASPseudoRandom(g:radius:=Int(rad));
      if co then
        b:=ASPseudoRandom(g:radius:=Int(rad));
        a:=Comm(a,b);
      fi;
      t:=TraceMat(a)-ImagesRepresentative(au,TraceMat(a^-1));
      cou:=cou+1;
    until not IsZero(t) or cou>100;


    rad:=rad+1/10;
    if not IsZero(t) then
      cnt:=cnt+1;
      if IsBound(red.gcdexfun) then
        p:=red.gcdexfun(p,t)[1];
      else
        p:=Gcd(p,red.normval(t));
      fi;
#Print(Int(MOFO(t))," ",p,"<<<<\n");
#Print("NTI:",p,"\n");
    fi;
  until not IsZero(p) and cnt>50;
  return p;
end;

PrimesByTraceInverseCommutator:=
  g->PrimesByTraceInverseGaloisCommutator(g,true,IdentityMapping(DefaultFieldOfMatrixGroup(g)));

PrimesByTraceInverse:=
  g->PrimesByTraceInverseGaloisCommutator(g,false,IdentityMapping(DefaultFieldOfMatrixGroup(g)));

NumberNotAbsIrr:=function(H)
local HM,gens,b,d,irri,modfun,denomfun,pl;

  irri:=DetermineIrrelevantPrime(H,0,2); # often cached
  modfun:=irri.irr.redfun;
  denomfun:=irri.red.denominatorfun;

  gens:=GeneratorsOfGroup(H);

  # Enveloping algebra -- start with identity
  b:=[Concatenation(gens[1])];

  b:=RegModZSpan(gens,b,modfun,irri.red);

  if not ForAll(Flat(b),IsInt) then
    d:=Lcm(List(Flat(b),denomfun));
    b:=b*d;
  fi;
  d:=MyDiscriminantOfLattice(b);

  # ensure it's not absirr:
  gens:=[];
#Print("d=",d,"\n");
  if IsZero(d) then Error("Zero");fi;
  pl:=irri.red.primesinnumber(Norm(d));
  pl:=Filtered(pl,x->not x in irri.bad);
  gens:=Filtered(pl,x->x in irri.good);
  pl:=Filtered(pl,x->not x in irri.good);

  for b in pl do
#Print("TRY:",b.p,"^",LogInt(b.fieldsize,b.p),"\n");
    if not MTX.IsAbsolutelyIrreducible(
      GModuleByMats(List(GeneratorsOfGroup(H),m->List(m,
        r->List(r,modfun))),GF(irri.irr.fieldsize))) then
      Add(gens,b);
    fi;
  od;
  # go back to Z-primes
  d:=Product(Set(List(gens,x->x.p)),1);

  return d;
end;

# Group, flag to take commutators
#ZEnvelopingAlgebraBasis:=function(G,co)
#local red,bas,module,span,addmat,i,j,k,a,z,y;
#  red:=G!.IrrprimeInfo.red;
#  bas:=red.bas;
#  module:=[];
#  span:=[];
#
#  addmat:=function(omat)
#  local s,mat;
#    # flattened, Z-coeffs
#    mat:=Concatenation(omat);
#    mat:=Concatenation(List(mat,x->Coefficients(bas,x)));
#    if Length(module)=0 then
#      s:=fail;
#    else
#      s:=SolutionMat(module,mat);
#    fi;
#    if s<>fail and ForAll(s,IsInt) then
#      return false;
#    else
#      Add(module,mat);
#      module:=HermiteNormalFormIntegerMat(module);
#      Add(span,omat);
#      return true;
#    fi;
#  end;
#
#  for i in GeneratorsOfGroup(G) do
#    if co then
#      for z in GeneratorsOfGroup(G) do
#        j:=Comm(i,z);
#        addmat(j);
#        #if addmat(j) then Add(span,j);fi;
#      od;
#    else
#      addmat(i);
#      #if addmat(i) then Add(span,i);fi;
#    fi;
#  od;
#
#  for i in span do
#    for j in span do
#      for k in [1,-1] do
#        a:=i*j^k;
#        addmat(a);
#        #if addmat(a) then Add(span,a);fi;
#      od;
#    od;
#  od;
#
#  # now every trace is Z-linear combination of traces in span
#  return span;
#
#end;

DiscriminantTraceRing:=function(G)
local red,bas,module,span,addmat,i,j,k,a,z,y;
  red:=G!.IrrprimeInfo.red;
  bas:=red.bas;

  span:=[Concatenation(One(G))];
  span:=RegModZSpan(GeneratorsOfGroup(G),span,G!.IrrprimeInfo.irr.redfun,red);
  # now every trace is Z-linear combination of traces in span

  a:=DimensionOfMatrixGroup(G);
  module:=List(span,y->Sum([1..a],x->y[x+a*(x-1)])); # traces
  module:=List(module,x->Coefficients(bas,x));
  # any denominators?
  k:=Set(List(Flat(module),DenominatorRat));

  module:=HermiteNormalFormIntegerMat(module);
  module:=Filtered(module,x->not IsZero(x));
  return MyDiscriminantOfLattice(module)*Product(k);;
end;

## prime>3 must be so G is SL mod prime
#NumberImprimitiveImage:=function(G,exp,prime,tester)
#local one,gens,gm,gp,a,am;
#  one:=One(GF(prime));
#  # find exp-powers that generate
#  gens:=List([1..5],x->ASPseudoRandom(G)^exp);
#  gm:=List(gens,x->x*one);
#  gp:=Group(gm);
#  while not tester(gp) do
#    a:=ASPseudoRandom(G)^exp;
#    am:=a*one;
#    if not am in gp then
#      Add(gens,a);
#      Add(gm,am);
#      gp:=Group(gm);
#    fi;
#  od;
#
#  return NumberNotAbsIrr(gp);
#
#end;

# make test functionf from number functions
IndividualPrimeTestFunction:=function(tester)
  return function(arg)
    local n,cc;
    n:=CallFuncList(tester,arg);
    cc:=1;
    while cc<10 and n>1 and
      ForAny(PartialFactorization(n,6),x->not IsPrimeInt(x)) do
        n:=Gcd(n,CallFuncList(tester,arg));
        cc:=cc+1;
    od;
    return Set(Factors(n));
  end;
end;

PrimesForAbsIrreducible:=IndividualPrimeTestFunction(NumberNotAbsIrr);

PrimesForMonomial:=IndividualPrimeTestFunction(function(H)
  return
  NumberForMonomial(H,Exponent(SymmetricGroup(Length(One(H)))));
  end);

PrimesForSolvable:=IndividualPrimeTestFunction(PrimesByNontrivialCommutators);

PrimesForIsometry:=IndividualPrimeTestFunction(PrimesByTraceInverse);

PrimesForSimilarity:=IndividualPrimeTestFunction(PrimesByTraceInverseCommutator);

PrimesForOrder:=IndividualPrimeTestFunction(NumberForElementOrder);

#H,t, third argument is 1:SL, 2:SP
PrimesForDense:=function(arg,modfun)
local good,irr,HM,b,rad,f,tco,i,b0,H,t,test,kind,dim,cnt,j,new,bad;

  H:=arg[1];
  dim:=Length(One(H));
  t:=arg[2];
  kind:=CheckProperKind(arg,3);

  # get an irrelevant prime, to allow matrix work modulo
  irr:=DetermineIrrelevantPrime(H,kind,2);
  if irr=fail then return fail;fi;
  test:=irr.test;
  bad:=irr.bad;
  good:=ShallowCopy(irr.good);
  modfun:=irr.reductionfunction;

  rad:=4;
  f:=EpimorphismFromFreeGroup(H);
  tco:=[t];

  b:=[Concatenation(One(t))];
  cnt:=0;
  repeat
    rad:=rad+1;
    for i in [1..3] do
      AddSet(tco,t^Image(f,PseudoRandom(Source(f):radius:=Int(rad))));
    od;
    i:=b;
    Error("fixcall");
    b:=RegModZSpan(tco,b,modfun);
    if b=fail then b:=i;fi;
    cnt:=cnt+1;
  until Length(b)=Length(b[1]) or cnt>8;

  if Length(b)<Length(b[1]) then
    # deal with undense case, proper normal closure
    tco:=[t];
    for i in tco do
      for j in
        Union(GeneratorsOfGroup(H),List(GeneratorsOfGroup(H),Inverse)) do
        new:=i^j;
        b0:=b;
        b:=RegModZSpan(Concatenation(tco,[new]),b0,modfun);
        if b=fail then
          return false;
        fi;
        if Length(b)>Length(b0) then
          #Print("new!\n");
          Add(tco,new);
        fi;
      od;
    od;
    if Length(b)<Length(b[1]) then
      return false;
    fi;
  fi;

  if ValueOption("densitytest")=true then
    if IsEvenInt(dim) and kind=SL then
      # test whether it preserves a form
      b0:=Group(tco);
      if ForAll(tco,x->TraceMat(x)=TraceMat(x^-1)) and
        ForAll(List([1..20],x->ASPseudoRandom(b0)),
          x->TraceMat(x)=TraceMat(x^-1)) then
        Error("Group seems to be not dense, but not fully proven");
        return false;
      fi;
    fi;

    return true;
  fi;

  b0:=b;
  b:=Set(irr.red.partialFactorization(AbsInt(NumeratorRat(Determinant(b)))));
  cnt:=0;
  while cnt<10 and (Maximum(b)>100  or Length(b)>3) do
    cnt:=cnt+1;
    rad:=rad+3;
    Info(InfoArithSub,2,"Further elements ",cnt," ",rad);
    for i in [1..Length(tco)] do
      AddSet(tco,t^Image(f,PseudoRandom(Source(f):radius:=Int(rad))));
    od;
    b:=RegModZSpan(tco,b0,modfun);
    b:=Set(irr.red.partialFactorization(AbsInt(NumeratorRat(Determinant(b)))));
  od;
  b:=Set(Factors(Product(b)));

  b:=Union(b,Factors(Gcd(Union(t-t^0))));
  if kind=SL then
    b:=Union(b,Factors(PrimesByTraceInverse(Group(tco))));
  fi;

  b:=Set(List(b,AbsInt));
  b:=Filtered(b,x->x<>irr);
  b:=Filtered(b,x->not x in good);
  b:=Filtered(b,x->not x in bad);

  Info(InfoArithSub,1,"candidates=",b);
  for irr in b do
    HM:=List(GeneratorsOfGroup(H),x->x*Z(irr)^0);
    HM:=Group(HM);
    if not test(HM) then
      AddSet(good,irr);
    fi;
  od;

  return good;
end;

#5a Adjoint representation and Z-meataxe

ConstructAdjointRep:=function(G,kind)
local n,unflat,bas,i,j,m,V,act,form,mats,d;

  kind:=CheckProperKind([G,kind],2);

  unflat:=m->List([1..n],x->m{[1+n*(x-1)..n*x]});
  n:=Length(One(G));
  #if IsFinite(G) then return false;fi;
  if kind=SL then
    #trace 0
    bas:=[];
    for i in [1..n] do
      for j in [1..n] do
        m:=NullMat(n,n);
        m[i][j]:=1;
        if i=j then
          m[n][n]:=-1;
        fi;
        if i<n or j<n then
          Add(bas,m);
        fi;
      od;
    od;
  else
    # symmetric
    bas:=[];
    for i in [1..n] do
      for j in [i..n] do
        m:=NullMat(n,n);
        m[i][j]:=1;
        if i<>j then
          m[j][i]:=1;
        fi;
        Add(bas,m);
      od;
    od;
    form:=NullMat(n,n);
    form{[1..n/2]}{[n/2+1..n]}:=IdentityMat(n/2);
    form{[n/2+1..n]}{[1..n/2]}:=-IdentityMat(n/2);
    bas:=List(bas,x->LeftQuotient(form,x));
  fi;
  bas:=bas*One(One(G)[1][1]);
  bas:=List(bas,Flat);
  act:=function(m,g) return Flat(unflat(m)^g);end;
  mats:=List(GeneratorsOfGroup(G),x->List(bas,b->SolutionMat(bas,act(b,x))));

  # build a new basis
  #nano:=ZSpinnedBasis(One(mats[1])[1],mats,2);

  return [mats,bas];
end;


# this is basically the irreducibility test from the meataxe, with some tests and special cases
# removed. mats must be a nonempty list of Z-matrices

#Z-random element
IntmatCoRaEl:=function(matrices,ngens,newgenlist,dim)
local g1,g2,M,x;
  g1:=Random([1..ngens]);
  g2:=g1;
  while g2=g1 and ngens>1 do
     g2:=Random([1..ngens]);
  od;

  x:=matrices[g1] * matrices[g2];
  if LogInt(Maximum(List(Flat(x),AbsInt)),10)<=200 and not x in matrices then
    ngens:=ngens + 1;
    matrices[ngens]:=x;
    Add(newgenlist, [g1, g2]);
  fi;

  # Take a random linear sum of the existing generators as new generator.
  # Record the sum in coefflist
  M:=0*matrices[1];
  # force some sparseness
  for g1 in Set(List([1..Random([2..7])],x->Random([1..ngens]))) do
     #g2:=Random(Integers); # only -10..10
     g2:=Random([-10..10]);
     if IsOne(g2) then
       M:=M + matrices[g1];
     elif not IsZero(g2) then
       M:=M + g2 * matrices[g1];
     fi;
  od;
  Info(InfoArithSub,4,"Evaluated random element in algebra.");
  return M;
end;

# variant of SolutionMat, avoid retriangulization
MySolMat:=function( sem, vec )
    local i,ncols,vno, z,x, row, sol;
    vec:=ShallowCopy(vec);
    ncols := Length(vec);
    z := Zero(sem.vectors[1][1]);
    sol := ListWithIdenticalEntries(Length(sem.vectors),z);
    ConvertToVectorRepNC(sol);
    #if ncols <> Length(sem.vectors[1]) then
    #    Error("SolutionMat: matrix and vector incompatible");
    #fi;
    for i in [1..ncols] do
        vno := sem.heads[i];
        if vno <> 0 then
            x := vec[i];
            if x <> z then
                AddRowVector(vec, sem.vectors[vno], -x);
                AddRowVector(sol, sem.coeffs[vno], x);
            fi;
        fi;
    od;
    if IsZero(vec) then
        return sol;
    else
        return fail;
    fi;
end;


## as SpinnedBasis but over Z
ZSpinnedBasis:=function(v,matrices,ngens,irr)
   local   zero,ans,anst, dim, subdim, leadpos, w, i, j, k, l, m,F,newi,nans;

  if Length(v)=0 then
    return [];
  fi;
  if not IsList(v[1]) then
    v:=[v];
  fi;
  zero:=0;
  #ans:=ShallowCopy(Basis(VectorSpace(F,v)));
  ans:=List(v,ShallowCopy);
  ans:=Filtered(HermiteNormalFormIntegerMat(ans),x->not IsZero(x));

  if Length(ans)=0 then
    return ans;
  fi;
  ans:=List(ans, v -> ImmutableVector(Rationals,v));
  anst := SemiEchelonMatTransformationDestructive(List(ans,ShallowCopy));
  dim:=Length(ans[1]);

  # alternate, add small images first

  repeat
    subdim:=Length(ans);
    #leadpos:=SubGModLeadPos(ans,dim,subdim,zero);
    newi:=[];
    i:=1;
    while i <= subdim do
      for l in [1..ngens] do
        for m in [1,-1] do
          # apply generator l ^m to submodule generator i

          w:=ShallowCopy(ans[i] * matrices[l]^m);
          # simply test whether not not in Z-span
          if SolutionMat(ans*Z(irr)^0,w*Z(irr)^0)<>fail then
            #nans:=SolutionMat(ans,w);
            nans:=MySolMat(anst,w);
#if nans<>MySolMat(anst,w) then Error("??");fi;
            if nans=fail or not ForAll(nans,IsInt) then
              Add(newi,w);
            fi;
          else
            Add(newi,w);
          fi;

        od;
      od;
      i:=i+1;
    od;
    Info(InfoArithSub,4,"|newi|=",Length(newi));
    if Length(newi)>0 then
      nans:=List(newi,x->x*x); # values
      nans:=Filtered([1..Length(nans)],x->nans[x]<=3/2*Minimum(nans));
      newi:=newi{nans}; # smallest ones, possibly multiple
      nans:=Concatenation(ans,newi);
      #ans:=Filtered(HermiteNormalFormIntegerMat(nans),x->not IsZero(x));
      ans:=LLLReducedBasis(nans).basis;
      anst := SemiEchelonMatTransformationDestructive(List(ans,ShallowCopy));
    fi;
    Info(InfoArithSub,4,"2|newi|=",Length(newi),"|ans|=",Length(ans));
  until Length(newi)=0;
  return ans;



  i:=1;
  while i <= subdim do
    newi:=i+1; # next row to be treated
    for l in [1..ngens] do
      for m in [1,-1] do
        # apply generator l ^m to submodule generator i
        w:=ShallowCopy(ans[i] * matrices[l]^m);
        nans:=Concatenation(ans,[w]);
        nans:=Filtered(HermiteNormalFormIntegerMat(nans),x->not IsZero(x));
        if nans<>ans then
          if ans[1]<>nans[1] then
            newi:=1;
          else
            newi:=Minimum(newi,Maximum(Filtered([1..Length(ans)],x->ans[x]=nans[x]))+1);
          fi;
          ans:=nans;
          subdim:=Length(ans);
        fi;
      od;
    od;

    Error("done ",i," next ",newi,ans);
    i:=newi;
  od;
  return ans;


#         # try to express w in terms of existing submodule generators
#         j:=1;
#         for  j in [1..subdim] do
#            k:=w[leadpos[j]];
#            if k <> zero then
#
#Print(j,leadpos,w,"\n");
#
#              # comparative cleanout amongst rows
#              # note that this does not change pivot positions, as not both pivots can be reduced
#              # to zero.
#              bez:=w[leadpos[j]]/ans[j][leadpos[j]];
#              if IsInt(bez) then
#                # only reduce w
#                w:=w-bez*ans[j];
#              else
#                bez:=MATINTbezout(ans[j][leadpos[j]],1,w[leadpos[j]],1);
#                bez:=[[bez.coeff1,bez.coeff2],[bez.coeff3,bez.coeff4]]*[ans[j],w];
#                ans[j]:=bez[1];
#                w:=bez[2];
#                newi:=Minimum(newi,i); # need to do from this row again as vector changed
#              fi;
#
#            fi;
#         od;
#
#         j:=1;
#         while j <= dim and w[j] = zero do j:=j + 1; od;
#         if j <= dim then
#            # we have found a new nonzero generator of the submodule
#            subdim:=subdim + 1;
#            leadpos[subdim]:=j;
#
#            #w:=(w[j]^-1) * w;
#            # No scaling: MultRowVector(w,w[j]^-1);
#            Add( ans, w );
#
#            w:=List(ans,PositionNonZero);
#            if w<>Set(w) then Error("stran");fi;
#
#            # cannot yet stop, need to continue mapping all
#            #if subdim = dim then
#            #   ans:=ImmutableMatrix(F,ans);
#            #   return ans;
#            #fi;
#         fi;
#      od;
#      i:=newi;
#   od;
#
#   Sort(ans);
#   ans:=Reversed(ans); # To bring it into semi-echelonised form.
#   ans:=ImmutableMatrix(Rationals,ans);
#   return ans;
end;

AreRefinementsNontrivial:=function(part)
local l,i,ll;
  part:=List(part,SortedList);
  part:=Set(part);
  SortBy(part,Length);
  l:=Length(part[1]);
  if l=1 then
    return false;
  fi;
  i:=First([1..Length(part)],x->Length(part[x])>1);
  if i<>fail then
    part:=part{[i..Length(part)]};
    ll:=Length(part[1]);
    if ll=2 and Length(part)>1 and Length(part[2])=2 then
      return false; # two different length 2.
    fi;
  fi;

  return true;
end;

ZModuleNullityOne:=function( mats,irr )
local matrices, tmatrices, ngens, ans,  M, mat, g1, g2, maxdeg,
      newgenlist, orig_ngens, zero,okprime,ofac,
      N, NT, v, subbasis, fac, sfac, pol, orig_pol, q, dim, ndim, i,
      l, trying, deg, facno, bestfacno, F, count, R, rt0,idmat,x,p,irrp,
      pfac1, pfac2, quotRem, pfr, idemp, M2, mat2, mat3,subb1,cnt,rk,rows,cols;

  mats:=ShallowCopy(mats);
  if not mats[1]^0 in mats then
    Add(mats,mats[1]^0); # identity
  fi;
  cnt:=0;
  okprime:=[];
  ofac:=0;
  repeat
    rt0:=Runtime();
    matrices:=ShallowCopy(mats);
    dim:=Length(matrices[1]);
    ngens:=Length(matrices);
    orig_ngens:=ngens;
    F:=Integers;
    zero:=Zero(F);
    R:=PolynomialRing(Rationals);

    # Now compute random elements M of the group algebra, calculate their
    # characteristic polynomials, factorize, and apply the irreducible factors
    # to M to get matrices with nontrivial nullspaces.
    # tmatrices will be a list of the transposed generators if required.

    tmatrices:=[];
    trying:=true;
    # trying will become false when we have an answer
    maxdeg:=1;
    newgenlist:=[];
    # Do a small amount of preprocessing to increase the generator set.
    for i in [1..1] do
      g1:=Random([1..ngens]);
      g2:=g1;
      while g2=g1 and Length(matrices) > 1 do
        g2:=Random([1..ngens]);
      od;
      x:=matrices[g1] * matrices[g2];

      if LogInt(Maximum(List(Flat(x),AbsInt)),10)<=200 and not x in matrices then
        ngens:=ngens + 1;
        matrices[ngens]:=x;
        Add(newgenlist, [g1, g2]);
      fi;
    od;
    Info(InfoArithSub,3,"Done preprocessing. Time = ",Runtime()-rt0,".");
    count:=0;

    # Main loop starts - choose a random element of group algebra on each pass
    while maxdeg<dim do
      count:=count + 1;
      if count mod SMTX.RAND_ELM_LIMIT = 0 then
        Error("Have generated ",SMTX.RAND_ELM_LIMIT,
                "random elements and failed to prove\n",
                "or disprove irreducibility. Type return to keep trying.");
      fi;
      maxdeg:=Minimum(maxdeg * 2,dim);
      # On this pass, we only consider irreducible factors up to degree maxdeg.
      # Using higher degree factors is very time consuming, so we prefer to try
      # another element.
      # To choose random element, first add on a new generator as a product of
      # two randomly chosen unequal existing generators
      # Record the product in newgenlist.
      Info(InfoArithSub,3,"Choosing random element number ",count);

      # force element with reducible characteristic polynomial
      repeat
        M:=IntmatCoRaEl(matrices,ngens,newgenlist,dim);

        ngens:=Length(matrices);

        M:=ImmutableMatrix(Rationals,M);

        deg:=[];
        p:=2;
        if deg<=4 then i:=30;
        elif deg<=6 then i:=70;
        elif deg<=8 then i:=110;
        else i:=150;fi;

        while deg<>fail and i>=0 do
          p:=NextPrimeInt(p);
          pol:=CharacteristicPolynomial(M*Z(p)^0,1);
          pol:=List(Factors(pol),DegreeOfUnivariateLaurentPolynomial);
          if Length(pol)=1 then
            deg:=fail;
          elif Length(pol)=2 then
            if Length(deg)=1 and Set(pol)<>Set(deg[1]) then
              deg:=fail;
            else
              Add(deg,pol);
            fi;
          fi;
          i:=i-1;
        od;

      until deg<>fail;

      pol:=CharacteristicPolynomialMatrixNC(Rationals,M,1);

      Info(InfoArithSub,2,"Mrank",RankMat(M));
      idmat:=M^0;

      orig_pol:=pol;
      Info(InfoArithSub,4,"Evaluated characteristic polynomial. Time = ",
          Runtime()-rt0,".");
      # Now we extract the irreducible factors of pol starting with those
      # of low degree
      deg:=0;
      fac:=[];
      # The next loop is through the degrees of irreducible factors
      while DegreeOfLaurentPolynomial(pol) > 0 and deg < maxdeg and trying do
        repeat
          deg:=deg + 1;
          if deg > Int(DegreeOfLaurentPolynomial(pol) / 2) then
            fac:=[pol];
          else
            fac:=Factors(R, pol);
            fac:=Filtered(fac,i->DegreeOfLaurentPolynomial(i)=deg);
            Info(InfoArithSub,4,Length(fac)," factors of degree ",deg,
                  ", Time = ",Runtime()-rt0,".");
          fi;
        until fac <> [] or deg = maxdeg;

        if fac <> [] then
          # not used -- will not give us finite set of primes
          #if DegreeOfLaurentPolynomial(fac[1]) = dim then
          #   # In this case the char poly is irreducible, so the
          #   # module is irreducible.
          #   ans:=true;
          #   trying:=false;
          #   bestfacno:=1;
          #   v:=ListWithIdenticalEntries(dim,zero);
          #   v[1]:=One(F);
          #   ndim:=dim;
          #fi;

          # Otherwise, first see if there is a non-repeating factor.
          # If so it will be decisive, so delete the rest of the list
          l:=Length(fac);
          facno:=1;
          while facno <= l and trying do
            if facno = l  or  fac[facno] <> fac[facno + 1] then
                fac:=[fac[facno]]; l:=1;
            else
              while facno < l and fac[facno] = fac[facno + 1] do
                facno:=facno + 1;
              od;
            fi;
            facno:=facno + 1;
          od;
          # Now we can delete repetitions from the list fac
          sfac:=Set(fac);

          if DegreeOfLaurentPolynomial(fac[1]) <> dim then
            # Now go through the factors and attempt to find a submodule
            facno:=1; l:=Length(sfac);
            while facno <= l and trying do
              mat:=Value(sfac[facno], M,idmat);
#Error("found!");
              Info(InfoArithSub,4,"Evaluated matrix on factor. Time = ",
                  Runtime()-rt0,".");
              #N:=NullspaceMat(mat);
              N:=HermiteNormalFormIntegerMatTransform(mat);
              N:=NullspaceMat(N.normal)*N.rowtrans;

              v:=N[1];
              ndim:=Length(N);
#Info(InfoArithSub,1,"ndim=",ndim,", deg=",deg);

if cnt<200 and Maximum(List(v,AbsInt))>10^6 then
  Info(InfoWarning,2,"too big: ",LogInt(Maximum(List(v,AbsInt)),10));
else
              Info(InfoArithSub,3,"Evaluated nullspace. Dimension = ",
                    ndim,". Time = ",Runtime()-rt0,".");
              if ndim<>deg then
#Info(InfoArithSub,1,"ndim=",ndim,", deg=",deg);
              else

                subbasis:=ZSpinnedBasis(v, matrices, orig_ngens,irr);
                Info(InfoArithSub,3,"spun up vector. Dimension = ",
                      Length(subbasis),". Time = ",Runtime()-rt0,".");
                if Length(subbasis) < dim then
                  Error("submodule!");
                  # Proper submodule found
                  trying:=false;
                  ans:=false;
                  #SMTX.SetSubbasis(module, subbasis);
                fi;

                subb1:=subbasis;
                trying:=false;
                # if we transpose and find no proper submodule, then the
                # module is definitely irreducible.
                mat:=TransposedMat(mat);
                if Length(tmatrices)=0 then
                  for i in [1..orig_ngens] do
                    Add(tmatrices, TransposedMat(matrices[i]));
                  od;
                fi;
                #NT:=NullspaceMat(mat);
                NT:=HermiteNormalFormIntegerMatTransform(mat);
                NT:=NullspaceMat(NT.normal)*NT.rowtrans;

                subbasis:=ZSpinnedBasis(NT[1],tmatrices,orig_ngens,irr);

                Info(InfoArithSub,3,"Spun up vector. Dimension = ",
                    Length(subbasis),". Time = ",Runtime()-rt0, ".");
                if Length(subbasis) < dim then
                  Error("subdual!");
                  # subbasis is a basis for a submodule of the transposed
                  # module, and the orthogonal complement of this is a
                  # submodule of the original module. So we find a vector
                  # v in that, and then spin it. Of course we won't
                  # necessarily get the full orthogonal complement
                  # that way, but we'll certainly get a proper submodule.
                  v:=SMTX.OrthogonalVector(subbasis);
                  #SMTX.SetSubbasis(module, SMTX.SpinnedBasis(v,matrices,F,orig_ngens));
                  ans:=false;
                else
                  if RankMat(mat)<dim-1 and
                    DegreeOfUnivariateLaurentPolynomial(sfac[facno])<>dim-RankMat(mat) then
                    Error("criterion not satsfied, should iterate, not yet done");
                  fi;


                  # test for which primes the nullspace could be larger:
                  # first find a minor of maximal rank:
                  rk:=Length(mat)-Length(N);

                  v:=0;
                  okprime:=[];
                  fac:=fail;
                  while v<=10 and (fac=fail or fac>10^20) do
                    rk:=RankMat(mat);
                    irrp:=irr;
                    while RankMat(mat*Z(irrp)^0)<rk do
                      irrp:=NextPrimeInt(irrp);
                    od;
                    # pick independent rows
                    rows:=[1..Length(mat)];
                    while(Length(rows))>rk do
                      i:=Random(rows);
                      if RankMat(mat{Difference(rows,[i])}*Z(irrp)^0)=rk then
                        rows:=Difference(rows,[i]);
                      fi;
                    od;

                    cols:=List(TriangulizedMat(mat{rows}),PositionNonZero);
                    i:=AbsInt(DeterminantMat(mat{rows}{cols}));
                    #i:=Set(Factors(AbsInt(DeterminantMat(mat{rows}{cols}))));
                    #if fac=fail then fac:=i;else fac:=Intersection(fac,i);fi;

                    if fac=fail then
                      fac:=i;
                    else
                      fac:=Gcd(fac,i);
                    fi;
                    v:=v+1;
                  od;
                  fac:=Gcd(fac,ofac);
                  ofac:=fac;
                  #fac:=Set(Factors(fac));
                  fac:=Set(PartialFactorization(fac));
Info(InfoArithSub,1,"fac=",fac);

                  for i in Difference(Filtered(fac,x->x<1000),okprime) do
                    if RankMat(mat*Z(i)^0)=rk then RemoveSet(fac,i);else Add(okprime,i);fi;
                  od;

                  # assure factors are prime and
                  # assume they are all small or we've tried a few
                  if ForAll(fac,IsPrimeInt) and
                    (ForAll(fac,x->x<65536) or cnt>100) then
                    for i in Difference(Filtered(fac,x->x<65536),okprime) do
                      if RankMat(mat*Z(i)^0)=rk then RemoveSet(fac,i);else Add(okprime,i);fi;
                    od;

                    # modulo these primes it does not span fully
                    return Lcm(Product(fac),(Lcm(DeterminantMat(subbasis),
                                                    DeterminantMat(subb1))));
                  fi;

                fi;
              fi;

fi;

              # leave out Ivanyos/Lux for the moment

              facno:=facno + 1;
            od; # going through irreducible factors of fixed degree.

            # If trying is false at this stage, then we don't have
            # an answer yet, so we have to go onto factors of the next degree.
            # Now divide p by the factors used if necessary
            if trying and deg < maxdeg then
              for q in fac do
                  pol:=Quotient(R, pol, q);
              od;
            fi;
          fi;           #DegreeOfLaurentPolynomial(fac[1]) <> dim
        fi;             #fac <> []
      od; # loop through degrees of irreducible factors
    od;  # main loop
    cnt:=cnt+1;
  until cnt>1000;
  return fail;
end;

# kind is SL or SP
# option `hard` forces the adjoint test through the lattice spanned
NumberAdjointReducible:=function(G,kind)
local mats,bas,d,red,irr;

  irr:=DetermineIrrelevantPrime(G,kind,3); # often cached
  red:=irr.red;
  irr:=irr.irr;
  mats:=ConstructAdjointRep(G,kind)[1];

  # # reducibility test
  if ValueOption("hard")<>true and DefaultFieldOfMatrixGroup(G)=Rationals then
    Info(InfoArithSub,1,"Trying MeatAxe");
    d:=ZModuleNullityOne(mats,irr);
    if d<>fail then return d; fi;
    Info(InfoArithSub,1,"MeatAxe failed, using Lattice");
  fi;

  # fallback to lattice setup, but is more expensive

  # Enveloping algebra, starting with identity
  bas:=[Concatenation(mats[1]^0)];
  bas:=RegModZSpan(mats,bas,irr.redfun,red);

  d:=MyDiscriminantOfLattice(bas);
  return d;
end;

AdjointReduciblePrimes:=function(G,kind)
  # may return superset
  return Set(Factors(NumberAdjointReducible(G,kind)));
end;

ASDoDelta:=function(H,classize,delcache,ring,layerlimit)
local gens,Q,r,lastgp;
  Q:=Size(ring);
  gens:=First(delcache,x->x[1]=Q);
  if gens<>fail then return [gens[2],fail];fi;

  gens:=List(GeneratorsOfGroup(H),x->x*One(ring));
  if IsPrimeInt(Q) then
    gens:=List(gens,x->ImmutableMatrix(ring,x));
  else
    gens:=List(gens,x->Matrix(ring,x));
  fi;

  if ForAll(gens,IsOne) then
    Q:=Group(()); # trivial group
  else
    Q:=Group(gens);
    if ValueOption("basic")=true then
      Size(Q);
    elif IsPrimeInt(Size(ring)) then
      r:=RecognizeGroup(Q); # here recognition alone will give the order as we work modulo prime
      SetSize(Q,Size(r));
    else
      FittingFreeLiftSetup(Q:layerlimit:=layerlimit); # also gives order
    fi;
  fi;
  lastgp:=Q;
  Info(InfoArithSub,3,"For ",Collected(Factors(Size(ring))),":",
    classize(ring)," ",Size(Q),":",classize(ring)/Size(Q));
  Q:=classize(ring)/Size(Q);
  if ForAny(delcache,x->x[1] mod Size(ring)=0 and x[2]<Q) then Error("huch");fi;
  AddSet(delcache,[Size(ring),Q]);
  return [Q,lastgp];
end;

ShortProduct:=function(g,len)
local a,i;
  a:=One(g);
  for i in [1..len] do
    a:=a*Random(GeneratorsOfGroup(g))^Random([-1,1]);
  od;
  return a;
end;

# this function does surjectivity tests so that no bad primes are returned.
PrimesNonSurjective:=function(arg)
local f,b,i,all,primes,d,cnt,fct,basch,n,r,v,sn,j,a,homo,homoe,dold,ii,
      rad,new,irr,HM,p,cnt1,reduced,good,bad,denom,
      gens,kinds,ngens,H,kind,modfun,redinfo,tco,
      test,enhance,expbound,solvlen,ordbound,ordbound_noadj,delcache,delta,
      count,hh,reduzier,modimg,transv,det,deto,forcea;

  delcache:=[];
  delta:=function(ring)
    return ASDoDelta(H,r->Size(SL(2,r)),delcache,ring,3)[1];
  end;

  H:=arg[1];
  kind:=CheckProperKind(arg,2);

  n:=Length(One(H));

  # get an irrelevant prime, to allow matrix work modulo
  # also immediately test small primes to be rid of them
  irr:=DetermineIrrelevantPrime(H,kind,3);
  test:=irr.test;
  good:=Set(ShallowCopy(irr.good));
  bad:=Set(ShallowCopy(irr.bad));
  denom:=ShallowCopy(irr.denom);
  redinfo:=irr.red;


  # Bounds for classes C6 and C9
  # finite bounds for SL also will work for SP.

  # Dimension2
  # 2^{1+2}.S3: exp 24, maxord 8
  # 2^{1+2}.3: exp 12, maxord 6
  # 2`A5: exp 60, maxord 10

  # Dimension 3
  # 3^3.Q8.3: exp 36, maxord 18
  # d x L2(7): exp: 84, maxord: 21
  # 3.A6: exp: 60, maxord: 15

  # Dimension 4
  # 4\circ 2^5.S6 exp: 120, max 24
  # d\circ 2`L2(7) (contained in A7)
  # A7: exp 420, maxord 7
  # d\circ 2`A_7: exp: 840, maxord 28
  # d\circ 2`U_4(2): exp: 360, maxord:=36

  # Dimension 5
  # 5^{1+2}:SP2(5): exp 60, maxord 30
  # d x L2(11): exp: 330, maxord: 55
  # M11: exp: 1320, maxord: 11
  # d x U4(2): exp: 180, maxord: 60

  # Dimension 6
  # 2x3`A_6.2_3
  # 6`A_6
  # 6 o 2`L_2(11) exp 660, order 66
  # 6`A_7    exp: 840, order 42
  # 6`L_3(4)`2_`  exp: 840, Order 42
  # 2`M_{12}: exp: 1320, order: 22
  # 6_1`U_4(3)`2_2   exp: 2520, order: 60

  # Dimension 7
  # 7^3.SP2(7): exp: 168 maxord 56
  # d x U3(3): exp: 168, maxord: 84

  # Dimension 8

  # 8\circ 2^{1+6}`SP_6(2)
  # 8\circ 4`L3(4).2`

  # Dimension 11, d=(q-1,11), p.418
  # 11^3:SP_2(11): 660, maxord: 132
  # L_2(23): 3036, maxord: 23
  # d x L2(23): 3036, maxord: 253
  # d x U_5(2): 3960, maxord: 198
  # M_24  exp: 212520, maxord: 23

  ordbound_noadj:=[,10,21,36,60,  ,84,,,,253];
  ordbound:=      [,10,21,36,60,66,56,120,90,120,198,156];
  expbound:=[,120,1260,2520,3960,2520,168,5040,360,9240,637560,360360];

  if kind=SL then
    if n>12 then Error("so far only dimension <=12 done");fi;
  else
    Error("So far only SL done");
  fi;

  enhance:=function(str,cnt,fct)
  local i,HM,primes,found,cc;
    primes:=fail;
    i:=1;

    # Norm of Numbers resulting, Gcd-ed
    while i<=cnt and (primes=fail or Length(primes)<2 or ForAny(primes,x->x>20)) do
      HM:=irr.red.normval(fct(0));
      if n=2 then
        for cc in [1..10] do
          HM:=Gcd(HM,irr.red.normval(fct(0)));
        od;
      fi;
      if primes<>fail then
        HM:=Gcd(HM,irr.red.normval(Product(primes)));
      else
        # is factoring an issue? Repeat if so.
        cc:=1;
        while cc<10 and HM>1 and
          ForAny(PartialFactorization(HM,6),x->not IsPrimeInt(x)) do
#Print("recall ",i," ",cnt,"\n");
          HM:=Gcd(HM,irr.red.normval(fct(0)));
          cc:=cc+1;
        od;
      fi;

      if HM=1 then primes:=[];
      elif primes=fail then primes:=Set(Factors(HM));
      else primes:=Intersection(primes,Factors(HM));fi;
      if cnt>3 and Length(primes)>0 then
	cnt:=Maximum(cnt,Minimum(50000,5*RootInt(Maximum(primes),3)));
      elif cnt=1 and ForAny(primes,x->x>200) then
        cnt:=2;
      fi;
      Info(InfoArithSub,5,"Enhance ",str," ",i,primes);
      i:=i+1;
    od;

    # Now primes is a list of Z-primes, preferrably not too big

    # factor
    primes:=Unique(Concatenation(List(primes,irr.red.primesinprime)));

    found:=ShallowCopy(primes);

    primes:=Filtered(primes,x->not x in bad); # not known bad ones
    cc:=Filtered(primes,x->x in good); # already known good
    primes:=Filtered(primes,x->not x in good); # not already known good ones

#if str[1]='F' then Error(primes);fi;

    for i in primes do # explicitly test whether they're good
      modfun:=i.redfun;
      HM:=List(GeneratorsOfGroup(H),m->List(m,r->List(r,modfun)));
      HM:=Group(HM);
      if not test(HM,i) then
        Add(good,i);
      else
if i=2 then Error("huh1");fi;
        Add(bad,i);
      fi;
    od;
    Info(InfoArithSub,1,str," - candidates: ",
      List(Filtered(found,x->x in bad),x->x.ideal),
      "\nknown:",
      List(cc,x->x.ideal),
      "\nnew:",
      List(Filtered(primes,x->x in good),x->x.ideal)
      );
  end;

  # is there a transvection ?
  transv:=ValueOption("transvection");
  b:=GeneratorsOfGroup(H);
  if transv=fail then
    transv:=First(b,IsTransvection);
    if transv=fail then
      i:=1;
      while i<=Length(b) and transv=fail do
        j:=1;
        while j<=Length(b) and transv=fail do
          if IsTransvection(b[i]*b[j]) then
            transv:=b[i]*b[j];
          elif IsTransvection(b[i]/b[j]) then
            transv:=b[i]/b[j];
          elif IsTransvection(b[i]^-1*b[j]) then
            transv:=b[i]^-1*b[j];
          fi;
          j:=j+1;
        od;
        i:=i+1;
      od;
    fi;
    if transv=fail then
      i:=0;
      while transv=fail and i<20 do
        transv:=ASPseudoRandom(H:radius:=3*i);
        if not IsTransvection(transv) then transv:=fail;fi;
        i:=i+1;
      od;
    fi;

  fi;

  forcea:=ValueOption("forceadj");

  if kind=SL then

    if transv<>fail and forcea<>true then
      Print("Have Transvection!\n");

      # transvection does not vanish -- Gcd of entries of t-t^0;
      tco:=transv-transv^0;
      tco:=Gcd(List(Flat(tco),Norm));
      enhance("TransvectionEigenspace ",1,x->tco);

      # form normal closure of transvection, hope it is absirr
      rad:=4;
      tco:=[transv];

      j:=0;
      # start with 1 and transvection
      b:=[Concatenation(One(transv)),
          Concatenation(transv)];
      det:=infinity;
      repeat
        deto:=det;
        j:=j+1;
        cnt:=0;
        repeat
          rad:=rad+1;
          # form a few more transvection and span
          for i in [1..3] do
            new:=transv^ASPseudoRandom(H:radius:=Int(rad));
            Add(tco,new);
            Add(b,Concatenation(new));
          od;
          i:=b;
          b:=RegModZSpan(tco,b,irr.irr.redfun,irr.red);
          if b=fail then b:=i;fi;
          cnt:=cnt+1;
        until (Length(b)>=Length(b[1]) and RankMat(b)=Length(b[1])) or cnt>10 ;
        rad:=rad+3;
        det:=DeterminantMat(b);
        i:=PartialFactorization(Norm(DeterminantMat(b)));
        #Print("Max=",Collected(i),"\n");
      until j>10 or (j>1 and (det=deto or det=1));

      # now we know it spans in characteristic 0. Lets add gratuitously
      # transvections, to get a good basis
      for i in [1..2*Length(b)] do
        Add(tco,transv^ASPseudoRandom(H:radius:=Int(rad)));
      od;
      b:=Concatenation(b,List(tco,Concatenation));
      b:=MyHNF(b,irr.red); # reduction
      b:=TransposedMat(b);
      i:=MyDiscriminantOfLattice(b);

      enhance("TransvectionSpan ",1,x->i);

    else
      enhance("Absolute irreducibility",1,x->NumberNotAbsIrr(H));

      if IsBound(ordbound_noadj[n]) then
        enhance("element Order",10,x->NumberForElementOrder(H,ordbound_noadj[n]));
      else
        enhance("element Order",10,x->NumberForElementOrder(H,ordbound[n]));
      fi;


      if n>2 then
        if redinfo.case=1 
          or ValueOption("noform")=true then
          enhance("Similarity",10,x->PrimesByTraceInverseCommutator(H));
        else
          # general form, including Galois involution?
          d:=Char0ScalarDomainMatrixList(redinfo.bas)[1]; # the field
          for a in Filtered(Elements(GaloisGroup(d)),x->Order(x)<=2) do
            enhance(Concatenation("Form (",String(Order(a)),")"),
              30,x->PrimesByTraceInverseGaloisCommutator(H,true,a));
          od;
        fi;
      fi;


      if (n>4 and not IsPrime(n)) or forcea=true then
        # all nonprime degrees except 4, or if forced
        if forcea=true then Print("# forced adjoint method\n");fi;
        enhance("Adjoint",1,x->NumberAdjointReducible(H,SL));
      elif IsPrime(n) then
        enhance("Monomial",
          10,x->NumberForMonomial(H,Exponent(SymmetricGroup(n))));

        # bounds from Dixon paper: ceil(8.55*log(n+1)/log(10)+0.36)
        solvlen:=[0,4,5,6,7,8,8,9,9,9,10,10,10,11,11,11,11,12,12,12,12,12,13];
        # and general bound 6 for prime
        for i in Intersection(Primes,
                  Filtered([1..Length(solvlen)],x->solvlen[x]>6)) do
          solvlen[i]:=6;
        od;

        # catches also C3 in prime degree
        enhance("Solvable",3,x->PrimesByNontrivialCommutators(H,solvlen[n]));
      else
        # n=4
        enhance("Imprimitive",3,
          x->NumberForImprimitive(H,Exponent(SymmetricGroup(n))));
        enhance("Absolutely Reducible G''",10,x->NumberAbsReducibleSecondDerived(H));
      fi;

      if redinfo.case<>1 then # extension, test subfields
        # Construct a derived subgroup, that modulo good primes still surjects
        # on SL.

        reduzier:=List([irr.irr],x->redinfo.makereductionfunc(x));
        count:=4;
        repeat
          repeat 
            count:=count+1;
            hh:=List([1..4*count],x->ShortProduct(H,Int(count/2)));
            hh:=List([1..count],x->Comm(Random(hh),Random(hh)));
            hh:=Filtered(hh,x->not IsOne(x));
          until Length(hh)>0;
          modimg:=
          List(reduzier,x->Group(List(hh,m->List(m,r->List(r,y->x(y))))));
        until ForAll(modimg,x->IsNaturalSL(x));
        hh:=Group(hh);
        DetermineIrrelevantPrime(hh,kind,2);

        # careful: String "Subfield" is tested for.
        # test the commutator group, not H
        enhance("Subfield",1,x->DiscriminantTraceRing(hh));

      fi;

      if redinfo.case=1 then
      # special treatment SL dim 2
      if n=2 then
        if not (5 in good or 5 in denom ) then
          a:=Product(Filtered(good,x->x>5));
          if a>1 and delta(Integers mod a)<delta(Integers mod (5*a)) then
            AddSet(good,5);
          fi;
        fi;
        a:=Product(Filtered(good,x->x>3));
        if a>2 and not (2 in good or 2 in denom) then
          if (3 in denom and delta(Integers mod (a))<delta(Integers mod (2*a)))
          or (not 3 in denom and delta(Integers mod (3*a))<delta(Integers mod (6*a))) then
            AddSet(good,2);
          fi;
        fi;
        if a>1 and not (3 in good or 3 in denom) then
          if (2 in denom and delta(Integers mod (a))<delta(Integers mod (3*a)))
            or (not 2 in denom and delta(Integers mod (2*a))<delta(Integers mod
          (6*a))) then
            AddSet(good,3);
          fi;
        fi;

      fi;
      else
        Print("smalldim special not yet done\n");
      fi;

    fi;

  else
    Error("non-SL case not done");
  fi;

  return good;
end;

MaxPCSPrimes :=function(arg)
local H,primes,kind,class,i,n,m,ind,idx,ids,ring,gens,Q,first,r,good,used,
      classize,delta,parts,a,lastgp,result,delcache,layerlimit,needsq;

  delcache:=[];
  delta:=function(ring)
  local a;
    a:=ASDoDelta(H,classize,delcache,ring,layerlimit);
    if a[2]<>fail then lastgp:=a[2];fi;
    return a[1];
  end;

  H:=arg[1];
  kind:=CheckProperKind(arg,3);
  if not IsBound(arg[2]) or arg[2]=fail then

    primes:=PrimesNonSurjective(H);
  else
    primes:=arg[2];
  fi;
  if not IsBound(H!.IrrprimeInfo) then
    DetermineIrrelevantPrime(H,kind,2);
  fi;

  needsq:=[2];

  n:=Length(One(H));
  if n=2 then
    Info(InfoWarning,1,"Warning:\n    ",
    "The congruence subgroup property does not hold in dimension 2");
    Add(needsq,3); # in dim 2 also 3 is a special case
  fi;

  classize:=ring->Size(class(n,ring));
  if kind=SL then
    class:=SL;
    layerlimit:=n^2-1;
    if n=2 then layerlimit:=2*layerlimit;fi;
  else
    layerlimit:=(n+1)*n/2;
    class:=SP;
    if n=4 then
      classize:=ring->Size(ring)^10
        *Product(Set(Factors(Size(ring))),p->(1-p^-2)*(1-p^-4));
    else
      # formula from
      # https://mathoverflow.net/questions/87904/is-there-a-formula-for-the-size-of-symplectic-group-defined-over-a-ring-z-pk-z
      classize:=ring->
        Product(Collected(Factors(Size(ring))),x->
          x[1]^((2*x[2]-1)*n^2/4+(x[2]-1)*n/2)
            *Product([1..n/2],i->(x[1]^(2*i)-1)));
    fi;
  fi;

  #MuP-part
  good:=[];
  parts:=[];
  ids:=[];
  for i in primes do
    idx:=1;
    a:=0;
    repeat
      ind:=idx;
      a:=a+1;
      Info(InfoArithSub,1,"Try ",i,"^",a);
      ring:=Integers mod i^a;
      idx:=delta(ring);
      if idx>ind then result:=lastgp;fi;
if idx>ind and ValueOption("level")<>fail and not ValueOption("level") mod
(i^a)=0 then
  Error("nodiv!");
fi;
    until idx=ind and (a>1 or not i in needsq); # for p=2 (3 in dim 2)
                                                # also test a=2
    if idx>1 then
      # prime is of interest
      AddSet(good,i);
      parts[i]:=a-1;
    fi;
    ids[i]:=idx;
  od;

  if Length(good)=0 then
    return [1,1];
    Error("no prime OK");
  elif Length(good)=1 then
    m:=good[1]^parts[good[1]];
    ind:=ids[good[1]];
  else

    # multiple primes -- lcm
    m:=Product(good,i->i^parts[i]);

    # now first extend by all primes once. If the delta is always the same (larger prime-power
    # will yield prime-power index factor as we intersect in kernel), it must be the same as index
    # for m and we're done
    Info(InfoArithSub,1,"Try ",m," ",good[1]);
    ind:=delta(Integers mod (m*good[1]));
    result:=lastgp;
    idx:=ind;
    i:=2;
    while i<=Length(good) and idx=ind do
      Info(InfoArithSub,1,"Try ",m," ",good[i]);
      idx:=delta(Integers mod (m*good[i]));
      i:=i+1;
    od;
    if idx<>ind then
      # indices differed, so we need to go through systematically
      # this will happen rarely
      Info(InfoArithSub,1,"Try ",m);
      ind:=delta(Integers mod m);
      result:=lastgp;
      while Length(good)>0 do
        i:=Minimum(good);
        idx:=delta(Integers mod (m*i));
        Info(InfoArithSub,1,"Try ",m," ",i," -> ",idx);
        if idx>ind then result:=lastgp;fi;
        if idx>ind then
          result:=lastgp;
          ind:=idx;
          m:=m*i;
        else
          good:=Difference(good,[i]);
        fi;
      od;
    fi;


  fi;

  # primes not caught -- this is basically 2, 3 or 5 in small dim
  a:=Difference(primes,good);
  if n<=3 then AddSet(a,2);fi;
  if n<=2 then AddSet(a,3);AddSet(a,5);fi;
  a:=Difference(a,H!.IrrprimeInfo.bad);
  for i in a do
    Info(InfoArithSub,1,"Try extra ",i);
    if (n<4 and i=2) or (n=2 and i=3) then
      idx:=delta(Integers mod (i^2*m));
      if idx>ind then
        ind:=idx;
        if delta(Integers mod (i*m))=idx then
          m:=m*i;
        else
          m:=m*i^2;
        fi;
      fi;
    else
      idx:=delta(Integers mod (i*m));
      if idx>ind then
        ind:=idx;
        m:=m*i;
      fi;
    fi;

  od;


  Info(InfoArithSub,1,"Level = ",m," = ");
  if InfoLevel(InfoArithSub)>0 then PrintFactorsInt(m);Print("\n"); fi;
  Info(InfoArithSub,1,"Index = ",ind," = ");
  if InfoLevel(InfoArithSub)>0 then PrintFactorsInt(ind);Print("\n"); fi;
  if ValueOption("quotient")<>fail then
    return [m,ind,result];
  else
    return [m,ind];
  fi;

end;

LevelMaxPCS := MaxPCSPrimes ;

# Part 6: Utility functions that eventually should go into GAP

InstallMethod( IsNaturalSL, "multiple irreducible reps, recognition size", true,
  [ IsFFEMatrixGroup and IsFinite ], 0, function( grp )
local gen, d, f,mo;
  f:=FieldOfMatrixGroup( grp );
  Info(InfoArithSub,4,"SL test over field of size ",Size(f));
  d:=DimensionOfMatrixGroup( grp );
  gen:=GeneratorsOfGroup( grp );
  if not ForAll(gen, x-> DeterminantMat(x) = One(f)) then
    #Error("erra");
    return false;fi;
  # size known -- easy
  if HasSize(grp) then return Size(grp) = Size(SL(d, Size(f)));fi;

  # natural module
  mo:=GModuleByMats(gen,f);
  if not MTX.IsAbsolutelyIrreducible(mo) then
    #Error("errb");
    return false; fi;

  # 2-symmetric
  if Characteristic(f)>2 then
    mo:=GModuleByMats(List(gen,x->SymmetricPower(x,2)),f);
    if not MTX.IsAbsolutelyIrreducible(mo) then
    #Error("errc");
      return false; fi;
  fi;

  # 2-antisymmetric
  if Characteristic(f)>2 then
    mo:=GModuleByMats(List(gen,x->ExteriorPower(x,2)),f);
    if not MTX.IsAbsolutelyIrreducible(mo) then
    #Error("errd");
      return false; fi;
  fi;

  # 3-symmetric
  if Characteristic(f)>3 then
    mo:=GModuleByMats(List(gen,x->SymmetricPower(x,3)),f);
    if not MTX.IsAbsolutelyIrreducible(mo) then
    #Error("erre");
      return false; fi;
  fi;

  mo:=RecognizeGroup(grp);
  if Size(mo) = Size(SL(d, Size(f))) then
    SetSize(grp,Size(mo));
    return true;
  # try to catch small cases like centre, the outer automs, and permutation,
  # square just to be super safe
  # this will be mostly used to catch subfield cases
  elif Size(mo)<Size(SL(d,Size(f)))/(Factorial(d)*18*Size(f))^2 then
    return false;
  fi;

  # check projective orbit
  mo:=Orbit(grp,One(grp)[2],OnLines:usesortdictionary);
  if Length(mo)<(Size(f)^d-1)/(Size(f)-1) then
    return false;
  fi;


  # force proper size w/o recog issues
  return Size(grp:cheap) = Size(SL(d, Size(f)));

end );

InstallOtherMethod( CopySubMatrix, "for two matrices made from plists and four lists",
  [ IsPlistRep and IsMatrix, IsPlistRep and IsMatrix and IsMutable,
    IsList, IsList, IsList, IsList ],
  function( m, n, srcrows, dstrows, srccols, dstcols )
    local i;
    # This eventually should go into the kernel without creating
    # a intermediate objects:
    for i in [1..Length(srcrows)] do
        n[dstrows[i]]{dstcols} :=
                  m[srcrows[i]]{srccols};
    od;
  end );

InstallOtherMethod( CopySubVector, "for two plist vectors and two lists",
  [ IsPlistRep, IsPlistRep and IsMutable, IsList, IsList ],
  function( a,b,pa,pb )
    # The following should eventually go into the kernel:
    b{pb}:=a{pa};
  end );

InstallOtherMethod( ZeroVector, "fallback: for an integer and a plist",
  [ IsInt, IsPlistRep ],-10,
  function( l, t )
    local v;
    v:=ListWithIdenticalEntries(l,Zero(t[1]));
    #if not(IsMutable(v)) then SetFilterObj(v,IsMutable); fi;
    return v;
  end );

InstallOtherMethod( Randomize, "fallback for a mutable plist vector",
  [ IsPlistRep and IsMutable ],-10,
function( v )
local bd,i;
  bd:=DefaultRing(v);
  for i in [1..Length(v)] do
    v[i]:=Random(bd);
  od;
  return v;
end);

InstallMethod( Randomize, "for a mutable 8bit vector",
  [ Is8BitVectorRep and IsMutable ],
  function( v )
    local f,i;
    f:=GF(Q_VEC8BIT(v));
    for i in [1..Length(v)] do v[i]:=Random(f); od;
    return v;
  end );

InstallMethod( MutableCopyMat, "for an 8bit matrix",
  [ Is8BitMatrixRep ],
  function( m )
    local mm;
    mm:=List(m,ShallowCopy);
    ConvertToMatrixRep(mm,Q_VEC8BIT(m[1]));
    return mm;
  end );
InstallMethod( MatElm, "for an 8bit matrix and two integers",
  [ Is8BitMatrixRep, IsPosInt, IsPosInt ],
  function( m, r, c ) return m[r][c]; end );
InstallMethod( SetMatElm, "for an 8bit matrix, two integers, and a ffe",
  [ Is8BitMatrixRep, IsPosInt, IsPosInt, IsFFE ],
  function( m, r, c, e ) m[r][c]:=e; end );
InstallMethod( Matrix, "for a list of vecs, an integer, and an 8bit mat",
  [IsList, IsInt, Is8BitMatrixRep],
  function(l,rl,m)
    local q,i,li;
    if not(IsList(l[1])) then
        li:=[];
        for i in [1..QuoInt(Length(l),rl)] do
            li[i]:=l{[(i-1)*rl+1..i*rl]};
        od;
    else
        li:= ShallowCopy(l);
    fi;
    q:=Q_VEC8BIT(m[1]);
    # FIXME: Does not work for matrices m with no rows
    ConvertToMatrixRep(li,q);
    return li;
  end );

# fix method from genss

InstallMethod( FindBasePointCandidates,
  "for a matrix group over a FF, using birthday paradox method",
  [ IsGroup and IsMatrixGroup and IsFinite, IsRecord, IsInt, IsObject ], 21,
  function( grp, opt, mode, parentS )
    local F, q, d, randels, immorblimit, orblimit, data, op, v, l, c, e, ht,
          val, x, w, cand, minest, minpos, round, i, j, gens;
    F:=DefaultFieldOfMatrixGroup(grp);
    q:=Size(F);
    d:=DimensionOfMatrixGroup(grp);
    randels:=opt.NrRandElsBirthdayParadox;
    immorblimit:=opt.OrbitLimitImmediatelyTake;
    orblimit:=opt.OrbitLimitBirthdayParadox;

    Info( InfoGenSS, 3, "Finding base points (birthday paradox, limit=",
                        orblimit,", randels=",randels,")..." );
    data:=opt.FindBasePointCandidatesData; # this we get from earlier methods
    if q = 2 then
        op:=OnPoints;
    else
        op:=OnLines;
    fi;
    gens:=GeneratorsOfGroup(grp);
    if IsObjWithMemory(gens[1]) then
        gens:=StripMemory(gens);
    fi;
    for round in [1..opt.TryBirthdayParadox] do
        v:=Set(GENSS_FindVectorsWithShortOrbit(grp,opt,parentS));
        if round = 1 then
            Append(v,data.vecs);   # take previously tried ones as well
        fi;
        v:=Filtered(v,vv->ForAny(gens,x-> vv <> op(vv,x)));
        l:=Length(v);
        if l = 0 then
            v:=OneMutable(gens[1]);
            # at least one basis vector needs to be moved
            v:=Filtered(v,vv->ForAny(gens,x-> vv <> op(vv,x)));
            l:=Length(v);
            if l=0 then
              v:=ShallowCopy(gens[1][1]);
              repeat
                v:=Randomize(v);
              until ForAny(gens,x-> v <> op(v,x));
              v:=[v];
              l:=1;
            fi;
        fi;
        c:=0*[1..l];    # the number of coincidences
        e:=ListWithIdenticalEntries(l,infinity);   # the current estimates
        ht:=HTCreate(v[1]*PrimitiveRoot(F),
                       rec(hashlen:=NextPrimeInt(l * randels * 4)));
        for i in [1..l] do
            val:=HTValue(ht,v[i]);
            if val = fail then
                HTAdd(ht,v[i],[i]);
            else
                AddSet(val,i);
            fi;
        od;
        for i in [1..randels] do
            if parentS = false then
                x:=GENSS_RandomElementFromAbove(opt,0);
            else
                x:=GENSS_RandomElementFromAbove(parentS,parentS!.layer);
            fi;
            Add(data.randpool,x);
            for j in [1..l] do
                if IsObjWithMemory(x) then
                    w:=op(v[j],x!.el);
                else
                    w:=op(v[j],x);
                fi;
                val:=HTValue(ht,w);
                if val <> fail then   # we know this point!
                    if j in val then    # a coincidence!
                        c[j]:=c[j] + 1;
                        e[j]:=QuoInt(i^2,2*c[j]);
                        if (c[j] >= 3 and e[j] <= immorblimit) or
                           (c[j] >= 15 and e[j] <= orblimit) then
                             Info( InfoGenSS, 2, "Found orbit with estimated ",
                                   "length ",e[j]," (coinc=",c[j],")" );
                             cand:=rec(points:=[v[j]], ops:=[op],
                                         used:=0);
                             for i in [1..l] do
                                 if i <> j and c[i] >= 10 and
                                    e[i] <= orblimit then
                                     Add(cand.points,v[i]);
                                     Add(cand.ops,op);
                                 fi;
                             od;
                             if Length(cand.points) > 1 then
                                 Info( InfoGenSS, 2, "Adding ",
                                       Length(cand.points)-1, " more vectors",
                                       " to candidates.");
                             fi;
                             return cand;
                        fi;
                    else
                        AddSet(val,j);
                    fi;
                else
                    HTAdd(ht,w,[j]);
                fi;
            od;
        od;
        minest:=Minimum(e);
        minpos:=Position(e,minest);
        Info( InfoGenSS,2,"Birthday #", round, ": no small enough estimate. ",
              "MinEst=",minest," Coinc=",c[j] );
        randels:=randels * 2;
        orblimit:=orblimit * 4;
    od;
    TryNextMethod();
  end );












# OLD NT workarounds


# single generator in quadratic PID -- somewhat hack
QuadSingleIdealGen:=function(id,red)
local nid,sum,i,j,sgn,t,fa,common,bas;
  bas:=red.bas;
  # first try LLL
  j:=List(id,x->Coefficients(bas,x));
  j:=LLLReducedBasis(j).basis;
  for i in j do
    t:=i*bas;
    if AllIntcoeffs(Coefficients(bas,id[1]/t))
          and AllIntcoeffs(Coefficients(bas,id[2]/t)) then
#Print("found:",i,"\n");
      return t;
    fi;
  od;

  # short Vectors
  fa:=10;
  fa:=Minimum(List(j,x->x*x));
  j:=List(id,x->Reversed(Coefficients(bas,x)));
  j:=Filtered(HermiteNormalFormIntegerMat(j),x->not IsZero(x));
  j:=List(j,Reversed);

  repeat
    fa:=fa*10;
    sgn:=ShortestVectors(j*TransposedMat(j),fa).vectors;
    for i in sgn do
      t:=i*j*bas;
      if AllIntcoeffs(Coefficients(bas,id[1]/t))
            and AllIntcoeffs(Coefficients(bas,id[2]/t)) then
        return t;
      fi;
    od;
  until Length(sgn)>10^4;

  # now take primes we get from the norm
  nid:=List(j,x->x*bas);
  fa:= Gcd(List(nid,x->Norm(Field(x),x)));
  fa:=Filtered(Set(PartialFactorization(fa)),x->x<=10^100 and IsPrimeInt(x));
  common:=[];
  for i in fa do
    for j in red.primesinnumber(i) do
      while ForAll(nid,x->AllIntcoeffs(Coefficients(bas,x/j))) do
        Add(common,j);
        nid:=List(nid,x->x/j);
      od;
    od;
  od;

  if Length(common)>0 then
    fa:=Product(common); # already known common factors
    sgn:=Gcd(List(nid,x->Norm(Field(x),x)));
    j:=QuadSingleIdealGen(Concatenation([sgn],nid),red);
    if IsList(j) and j[1]=fail then return [fail,j[2]*fa];fi;
    return j*fa;
  else
    return [fail,Gcd(List(nid,x->Norm(Field(x),x)))];
  fi;

  Error("UUU");

  for sum in [1..Maximum(id[1],10000)] do
    for i in [0..sum] do
      for sgn in [1,-1] do
        j:=sum-i;
        t:=sgn*i*id[1]+j*id[2];
        if ForAll(id,x->AllIntcoeffs(Coefficients(bas,x/t))) then
#Print("found",[i,j],"\n");
          return t;
        fi;
      od;
    od;
  od;
  Error("not found");
end;

QD:=x->Quadratic(x).display;

# general setup for reduction mod p. API should extend to rings.
IdealQuotientNumorder:=function(bas,gens)
local a,l,i,c,e,s,j,b,k,sel;
  # put 1 in last position, so HNF will preserve it for itself
  a:=BasisVectors(bas);
  if ForAny(bas,IsInt) then
    b:=Concatenation(Filtered(a,x->not IsInt(x)),Filtered(a,IsInt));
    bas:=Basis(UnderlyingLeftModule(bas),b);
  fi;

  a:=ShallowCopy(gens);
  l:=List(gens,x->Coefficients(bas,x));
  l:=Filtered(HermiteNormalFormIntegerMat(l),x->not IsZero(x));
  # ideal closure
  for i in a do
    for j in bas do
      e:=i*j;
      c:=Coefficients(bas,e);
      s:=SolutionMat(l,c);
      if s=fail or not ForAll(s,IsInt) then
        Add(a,e);
        Add(l,c);
        l:=Filtered(HermiteNormalFormIntegerMat(l),x->not IsZero(x));
      fi;
    od;
  od;
  s:=SmithNormalFormIntegerMatTransforms(l);
  c:=DiagonalOfMat(s.normal);
  if Length(c)<Length(bas) or Product(c)=0 then
    Error("not finite quotient");
  fi;
  sel:=Filtered([1..Length(c)],x->c[x]>1);
  e:=s.coltrans^-1*bas; # Elements that satisfy diagonal relations
  e:=Basis(UnderlyingLeftModule(bas),e);

  # is it just an ring Integers modulo ?
  if Length(sel)=1 then
    sel:=sel[1];
    a:=Integers mod c[sel];
    k:=One(a);
    c:=MappingByFunction(UnderlyingLeftModule(bas),a,
         function(x)
           return Coefficients(e,x)[sel]*k;
          end,
          Int);
    return c;
  fi;

  l:=EmptySCTable(Length(sel),0);
  for i in [1..Length(sel)] do
    for j in [1..Length(sel)] do
       a:=e[sel[i]]*e[sel[j]];
       a:=Coefficients(e,a){sel};
       for k in [1..Length(a)] do
         a[k]:=a[k] mod c[sel[k]];
       od;
       # translate coefficient form
       if not IsZero(a) then
         a:=Concatenation(List(Filtered([1..Length(a)],x->not IsZero(a[x])),
           x->[a[x],x]));
         SetEntrySCTable(l,i,j,a);
       fi;
    od;
  od;
  a:=[];
  k:=1;
  for i in [1..Length(sel)] do
    if IsInt(e[sel[i]]) then Add(a,String(e[sel[i]]));
    else Add(a,[CharInt(96+k)]);k:=k+1;fi;
  od;
  a:=RingByStructureConstants(c{sel},l,a);
  SetIsAssociative(a,true);

  if Length(Set(c{sel}))=1 and IsPrimeInt(c[Length(c)]) then
    # do we have a field?
    if Size(Units(a))=Size(a)-1 then
      s:=c[sel[1]]; # prime
      l:=GF(Size(a));

      # try based on 1 element
      k:=e[1];
      c:=List([0..Length(bas)-1],x->k^x);
      if RankMat(List(c,x->Coefficients(bas,x)))<Length(bas) then
        Error("not yet full rank");
      else
        k:=MinimalPolynomial(Rationals,e[1]);
        k:=PolynomialModP(k,s);
        if not IsIrreducible(k) then
          Error("poly is reducible");
        else
          a:=GF(Size(a));
          k:=RootsOfUPol(a,k)[1];
          k:=List([0..Length(bas)-1],x->k^x);
          c:=Basis(UnderlyingLeftModule(bas),c);
          j:=Basis(a,k);
          return MappingByFunction(UnderlyingLeftModule(bas),a,
            function(x)
              return Coefficients(c,x)*k;
            end,
            function(x)
              return List(Coefficients(j,x),Int)*c;
            end);
        fi;
      fi;
    fi;
  fi;

  l:=FamilyObj(One(a));
  c:=MappingByFunction(UnderlyingLeftModule(bas),a,
    function(x)
      return Objectify( l!.defaultTypeDenseCoeffVectorRep,
            [ Immutable(
            SCRingReducedModuli(l!.moduli,Coefficients(e,x){sel})) ] );
    end,
    function(x)
    local v;
      v:=List(e,x->0);
      v{sel}:=x![1];
      return e*v;
    end);
  return c;
end;

GroupReductionMod:=function(mhom,num)
local G,red,bas,map,mats,new,orb,o2,hom;
  G:=Range(mhom);
  red:=G!.IrrprimeInfo.red;
  if GeneratorsOfGroup(G)<>MappingGeneratorsImages(mhom)[2] then
    G:=GroupByGenerators(MappingGeneratorsImages(mhom)[2]);
  fi;
  bas:=red.bas;
  map:=IdealQuotientNumorder(bas,num);
  mats:=List(GeneratorsOfGroup(G),m->List(m,r->List(r,map)));
  new:=GroupByGenerators(mats);
  orb:=Set(Immutable(Orbit(new,One(new)[1],OnRight)));
  Print("Domain:",Length(orb),"\n");

  if not One(new)[2] in orb then
    o2:=Orbit(new,One(new)[2],OnRight);
    orb:=Union(orb,Immutable(o2));
    Print("NewDomain:",Length(orb),"\n");
  fi;
  hom:=ActionHomomorphism(new,orb,OnRight,"surjective");
  new:=Image(hom,new);
if Length(GeneratorsOfGroup(new))<>Length(mats) then Error("EH");fi;
  hom:=SmallerDegreePermutationRepresentation(new);
  new:=Image(hom,new);
  Print("DegA:",NrMovedPoints(new),"\n");
  hom:=SmallerDegreePermutationRepresentation(new);
  new:=Image(hom,new);
  Print("DegB:",NrMovedPoints(new),"\n");
  hom:=MinimalFaithfulPermutationRepresentation(new);
  new:=Image(hom,new);
  Print("DegC:",NrMovedPoints(new),"\n");
  return GroupHomomorphismByImages(Source(mhom),new,
    MappingGeneratorsImages(mhom)[1],GeneratorsOfGroup(new));
end;

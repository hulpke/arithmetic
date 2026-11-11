#############################################################################
##
##  slnatural.g      Constructive recognition of SL(n,q), q odd,
##                   in its natural representation
##
##  A GAP transcription of the strategy of the Leedham-Green--O'Brien
##  algorithm as implemented in Magma's CompositionTree code
##  (classical/recognition/natural/odd/sl/{sl.m,gen.m}).
##  done by Claude.
##
##  Input : G <= GL(n,q), q odd, n >= 2, with SL(n,q) <= G.
##  Output: the Leedham-Green--O'Brien standard generators [a,b,t,delta]
##          of SL(n,q) (as returned by Magma's
##          ClassicalStandardGenerators("SL",n,q)), conjugated into G,
##          together with an SLP for them in the given generators of G and
##          the change of basis CB with  CB * std[i] * CB^-1 = LGO[i].
##          Plus constructive membership: SLP of any g in SL(n,q) in the
##          standard generators (Gaussian elimination with transvections,
##          as in Costi's rewriting).
##
##  Strategy (recursive, on a subspace W of dimension k, with a group H
##  acting on W as a group containing SL(k) and trivially on a fixed
##  complement):
##   1. find an involution z (power of a random element) whose eigenspaces
##      W1 (+1) and W2 (-1) have dimensions f, k-f, ideally in [k/3,2k/3];
##   2. Bray's trick: centraliser C of z (block diagonal);
##   3. "kill factor": powers of elements of C that are trivial on W2,
##      plus C-conjugates, generate a group acting as SL(f) on W1 and
##      trivially elsewhere; same for W2;
##   4. recurse on both blocks (base cases: SL(1) trivial, SL(2) by the
##      Conder--Leedham-Green method, or brute force for q <= 11);
##   5. glue: build the involution I' = -1 on e_1 and e_{f+1} (first basis
##      vectors of the two blocks), take its centraliser, kill the other
##      factor, recognise the SL(2) on <e_1,e_{f+1}>; this yields the
##      transvections between the blocks, hence all transvections of
##      SL(k), and the standard generators of SL(k) are written down by
##      row reduction.
##
##  Step 5 differs from Magma (which uses the involution
##  diag(-1,-1,1,..,1,-1,-1), an SL(4) and a CompositionTree / Ryba call to
##  find a block-swapping element and then multiplies n-cycles together);
##  the version here needs only the SL(2) base case.
##
##  Everything returned is checked exactly (Las Vegas): elements carry
##  their own SLPs (GAP objects with memory), and every standard
##  generator is compared with the target matrix.
##
#############################################################################

if not IsBound(InfoSLNat) then DeclareInfoClass("InfoSLNat"); fi;

SLNat := rec();

#############################################################################
##  Leedham-Green--O'Brien standard generators of SL(n,q)
##  (Magma: SLChosenElements in classical/recognition/standard.m)
##  row-vector convention, as in Magma and GAP:
##   a : e1 -> e2, e2 -> -e1
##   b : e1 -> en, ei -> -e(i-1)   (for n = 2, b = a)
##   t : e1 -> e1 + e2
##   delta = diag(w, w^-1, 1, ..., 1),  w = Z(q)
#############################################################################
SLNat.LGOStandardGenerators := function(n, q)
  local F, w, a, b, t, delta, i;
  F := GF(q); w := Z(q);
  a := MutableCopyMat(IdentityMat(n, F));
  a[1][1] := Zero(F); a[1][2] := One(F); a[2][1] := -One(F); a[2][2] := Zero(F);
  b := MutableCopyMat(NullMat(n, n, F));
  for i in [2..n] do b[i][i-1] := -One(F); od;
  b[1][n] := One(F);
  t := MutableCopyMat(IdentityMat(n, F)); t[1][2] := One(F);
  delta := MutableCopyMat(IdentityMat(n, F));
  delta[1][1] := w; delta[2][2] := w^-1;
  return List([a, b, t, delta], Immutable);
end;

#############################################################################
##  basic utilities
#############################################################################

# action of g on span(B{rows}) in that basis (block must be g-invariant)
SLNat.BlockAct := function(B, Binv, rows, g)
  return B{rows} * StripMemory(g) * Binv{[1..Length(B)]}{rows};
end;

SLNat.IsScalar := function(X)
  return X = X[1][1] * One(X);
end;

# product replacement ("rattle") random elements, works with memory objects
SLNat.PRInit := function(gens)
  local st, i;
  st := rec(seeds := []);
  while Length(st.seeds) < Maximum(10, Length(gens) + 2) do
    Append(st.seeds, gens);
  od;
  st.seeds := st.seeds{[1..Maximum(10, Length(gens) + 2)]};
  st.acc := gens[1]^0;
  for i in [1..50] do SLNat.PRNext(st); od;
  return st;
end;

SLNat.PRNext := function(st)
  local n, i, j;
  n := Length(st.seeds);
  i := Random([1..n]);
  j := Random([1..n-1]); if j >= i then j := j + 1; fi;
  if Random([1, 2]) = 1 then
    st.seeds[i] := st.seeds[i] * st.seeds[j];
  else
    st.seeds[i] := st.seeds[j]^-1 * st.seeds[i];
  fi;
  st.acc := st.acc * st.seeds[i];
  return st.acc;
end;

# if X - 1 is a multiple of a single matrix unit E_ij (i <> j),
# return [i, j, value], else fail
SLNat.TransInfo := function(X)
  local k, i, j, pos, D;
  k := Length(X);
  D := X - One(X);
  pos := [];
  for i in [1..k] do
    for j in [1..k] do
      if not IsZero(D[i][j]) then Add(pos, [i, j]); fi;
    od;
  od;
  if Length(pos) <> 1 or pos[1][1] = pos[1][2] then return fail; fi;
  return [pos[1][1], pos[1][2], D[pos[1][1]][pos[1][2]]];
end;

# indices of a maximal GF(p)-independent subset of the field elements vals
SLNat.IndependentIndices := function(F, vals)
  local stdB, idx, vecs, i, v;
  stdB := Basis(F);
  idx := []; vecs := [];
  for i in [1..Length(vals)] do
    v := Coefficients(stdB, vals[i]);
    if RankMat(Concatenation(vecs, [v])) > Length(vecs) then
      Add(vecs, v); Add(idx, i);
    fi;
  od;
  return idx;
end;

# integer coefficients of lambda in the GF(p)-basis bas
SLNat.FpCoeffs := function(bas, lambda)
  return List(Coefficients(bas, lambda), IntFFE);
end;

#############################################################################
##  Gaussian elimination with transvections.
##  T(i,j,lambda) must return an element acting as 1 + lambda*E_ij on W;
##  returns an element acting as M (M in SL(k)).
#############################################################################
SLNat.Eliminate := function(T, M, k, F, id)
  local ops, doop, c, r, one, res, op;
  M := MutableCopyMat(M);
  one := One(F);
  ops := [];
  doop := function(i, j, lam)          # row i := row i + lam * row j
    if IsZero(lam) then return; fi;
    M[i] := M[i] + lam * M[j];
    Add(ops, [i, j, lam]);
  end;
  for c in [1..k-1] do
    if IsZero(M[c][c]) then
      r := First([c+1..k], r -> not IsZero(M[r][c]));
      doop(c, r, one);
    fi;
    if M[c][c] <> one then
      if ForAll([c+1..k], r -> IsZero(M[r][c])) then doop(c+1, c, one); fi;
      r := First([c+1..k], r -> not IsZero(M[r][c]));
      doop(c, r, (one - M[c][c]) / M[r][c]);
    fi;
    for r in [1..k] do
      if r <> c and not IsZero(M[r][c]) then doop(r, c, -M[r][c]); fi;
    od;
  od;
  for r in [1..k-1] do
    if not IsZero(M[r][k]) then doop(r, k, -M[r][k]); fi;
  od;
  if not IsOne(M) then Error("Eliminate: matrix not in SL"); fi;
  # E_N ... E_1 M = 1  ==>  M = E_1^-1 ... E_N^-1
  res := id;
  for op in ops do res := res * T(op[1], op[2], -op[3]); od;
  return res;
end;

#############################################################################
##  Toolkit from standard generators.
##  std = [a,b,t,delta] (memory elements) acting as the LGO generators on
##  span(B{[1..k]}) in that basis, trivially on span(B{[k+1..n]}).
##  Provides T(i,j,lambda) (transvections) and Word(M) (any M in SL(k)).
#############################################################################
SLNat.ToolkitFromStd := function(std, B, k, F)
  local tk, Binv, act, a, b, t, d, e, x, vals, r12, idx, dict, key, X, inf,
        m, Rows, Cols, RowB, ColB, j, up, down, T, cacheT1j, id, bm;

  Binv := B^-1;
  act := g -> SLNat.BlockAct(B, Binv, [1..k], g);
  id := std[1]^0;
  tk := rec(B := B, Binv := Binv, k := k, F := F, std := std, id := id);
  if k = 1 then
    tk.T := function(i, j, lambda) Error("no transvections in SL(1)"); end;
    tk.Word := function(M) return id; end;
    return tk;
  fi;
  a := std[1]; b := std[2]; t := std[3]; d := std[4];
  e := DegreeOverPrimeField(F);

  # E_12 for a GF(p)-basis of F: delta^-m t delta^m = E_12(w^-2m)
  r12 := []; vals := [];
  x := t; m := 0;
  repeat
    Add(r12, x); Add(vals, SLNat.TransInfo(act(x))[3]);
    x := x^d; m := m + 1;
    idx := SLNat.IndependentIndices(F, vals);
  until Length(idx) = e or m > 4 * e + 4;
  if Length(idx) < e then Error("ToolkitFromStd: no field basis"); fi;
  r12 := List(idx, i -> [r12[i], vals[i]]);

  # adjacent transvections E_{i,i+1}, E_{i+1,i} as b-conjugates of t, t^(a^-1)
  dict := rec();
  key := function(i, j) return Concatenation(String(i), "_", String(j)); end;
  for X in [t, t^(a^-1)] do
    x := X;
    for m in [1..k] do
      inf := SLNat.TransInfo(act(x));
      if inf = fail then Error("ToolkitFromStd: unexpected element"); fi;
      dict.(key(inf[1], inf[2])) := [x, inf[3]];
      x := x^(b^-1);
    od;
  od;
  up := function(i, j) return dict.(key(i, j)); end;

  # first row: Rows[j] = list of [E_1j(v), v], v running through a basis
  Rows := []; Cols := [];
  Rows[2] := r12;
  Cols[2] := List(r12, p -> [p[1]^(a^-1), SLNat.TransInfo(act(p[1]^(a^-1)))[3]]);
  for j in [3..k] do
    # [E_1,j-1(x), E_j-1,j(s)] = E_1j(x s)
    Rows[j] := List(Rows[j-1], p -> [Comm(p[1], up(j-1, j)[1]),
                                     p[2] * up(j-1, j)[2]]);
    # [E_j,j-1(s), E_j-1,1(x)] = E_j1(s x)
    Cols[j] := List(Cols[j-1], p -> [Comm(up(j, j-1)[1], p[1]),
                                     up(j, j-1)[2] * p[2]]);
  od;
  RowB := []; ColB := [];
  for j in [2..k] do
    RowB[j] := Basis(F, List(Rows[j], p -> p[2]));
    ColB[j] := Basis(F, List(Cols[j], p -> p[2]));
  od;

  cacheT1j := [];
  T := function(i, j, lambda)
    local c, res, l;
    if IsZero(lambda) then return id; fi;
    if i = 1 then
      c := SLNat.FpCoeffs(RowB[j], lambda);
      res := id;
      for l in [1..e] do
        if c[l] <> 0 then res := res * Rows[j][l][1]^c[l]; fi;
      od;
      return res;
    elif j = 1 then
      c := SLNat.FpCoeffs(ColB[i], lambda);
      res := id;
      for l in [1..e] do
        if c[l] <> 0 then res := res * Cols[i][l][1]^c[l]; fi;
      od;
      return res;
    else
      # [E_i1(lambda), E_1j(1)] = E_ij(lambda)
      if not IsBound(cacheT1j[j]) then cacheT1j[j] := T(1, j, One(F)); fi;
      return Comm(T(i, 1, lambda), cacheT1j[j]);
    fi;
  end;
  tk.T := T;
  tk.Word := M -> SLNat.Eliminate(T, M, k, F, id);
  return tk;
end;

#############################################################################
##  Bray's trick and involution centralisers
#############################################################################

# elements of the centraliser of the involution z (act gives the matrix on W)
SLNat.BrayElements := function(st, z, act)
  local h, c, o, m;
  repeat h := SLNat.PRNext(st); until not IsOne(act(h)^2);
  c := Comm(z, h);
  o := Order(act(c));
  if IsOddInt(o) then
    return [h * c^((o - 1) / 2)];
  else
    m := o / 2;
    return [c^m, Comm(z, h^-1)^m];
  fi;
end;

# generators for C_H(z); stop when each listed block (row index lists of
# the basis B, in which z is diagonal) is absolutely irreducible
SLNat.InvolutionCentraliser := function(st, z, act, B, Binv, blocks, F,
                                        mingens)
  local gens, Z, tries, y, Y, ok;
  gens := [z]; Z := act(z); tries := 0;
  repeat
    tries := tries + 1;
    for y in SLNat.BrayElements(st, z, act) do
      Y := act(y);
      if Y * Z = Z * Y and not IsOne(Y) then Add(gens, y); fi;
    od;
    ok := Length(gens) >= mingens and
          ForAll(blocks, bl -> Length(bl) < 2 or
            MTX.IsAbsolutelyIrreducible(GModuleByMats(
              List(gens, g -> SLNat.BlockAct(B, Binv, bl, g)), F)));
  until ok or tries > 4 * mingens + 20;
  if not ok then
    Info(InfoSLNat, 2, "centraliser construction failed");
    return fail;
  fi;
  return gens;
end;

# from random elements of a block diagonal group (process Cst) construct
# generators of a group acting as SL on span(B{keep}) and trivially on
# span(B{kill}) (Magma: GoodCentraliser)
SLNat.KillFactor := function(Cst, keep, kill, B, Binv, F, mingens)
  local q, m, tries, c, o, x, X, good, gens, y, ok;
  q := Size(F); m := Length(keep);
  tries := 0;
  repeat
    tries := tries + 1;
    c := SLNat.PRNext(Cst);
    if Length(kill) > 0 then
      o := Order(SLNat.BlockAct(B, Binv, kill, c));
    else
      o := 1;
    fi;
    x := c^o;
    X := SLNat.BlockAct(B, Binv, keep, x);
    good := not SLNat.IsScalar(X);
    # GL(2,3) has a normal Q8
    if good and q = 3 and m = 2 then
      o := Order(X);
      good := o <> 2^LogInt(o, 2);
    fi;
  until good or tries > 200;
  if not good then return fail; fi;
  gens := [x]; tries := 0;
  repeat
    tries := tries + 1;
    y := x^SLNat.PRNext(Cst);
    if not SLNat.BlockAct(B, Binv, keep, y) in
           List(gens, g -> SLNat.BlockAct(B, Binv, keep, g)) then
      Add(gens, y);
    fi;
    ok := Length(gens) >= mingens and
      MTX.IsAbsolutelyIrreducible(GModuleByMats(
        List(gens, g -> SLNat.BlockAct(B, Binv, keep, g)), F));
  until ok or tries > 10 * mingens + 20;
  if not ok then return fail; fi;
  return gens;
end;

#############################################################################
##  Base case SL(2,q): gens act on span(B{[1,2]}) as a group containing
##  SL(2,q), trivially on span(B{[3..n]}).  Returns a toolkit or fail.
#############################################################################

# small q: breadth first search in the group generated
SLNat.SL2BruteForce := function(gens, B, F)
  local Binv, act, q, w, targets, found, dict, queue, pos, x, g, y, Y, i,
        LGO, std, n;
  Binv := B^-1; n := Length(B);
  act := g -> Immutable(SLNat.BlockAct(B, Binv, [1, 2], g));
  q := Size(F);
  LGO := SLNat.LGOStandardGenerators(2, q);
  targets := [LGO[1], LGO[3], LGO[4]];      # a, t, delta (b = a)
  found := [fail, fail, fail];
  x := gens[1]^0;
  y:=act(x);
  while Size(FieldOfMatrixList([y]))<>q do
    y:=y+Random(GF(q));
    y:=y*Random(GF(q)); # force matrix over correct field --hack
  od;
  dict := NewDictionary(y,false);
  AddDictionary(dict, act(x));
  queue := [x]; pos := 1;
  while pos <= Length(queue) and fail in found do
    x := queue[pos]; pos := pos + 1;
    for g in gens do
      y := x * g; Y := act(y);
      if not KnowsDictionary(dict, Y) then
        AddDictionary(dict, Y);
        Add(queue, y);
        for i in [1..3] do
          if found[i] = fail and Y = targets[i] then found[i] := y; fi;
        od;
      fi;
    od;
  od;
  if fail in found then return fail; fi;
  std := [found[1], found[1], found[2], found[3]];
  return SLNat.ToolkitFromStd(std, B, 2, F);
end;

SLNat.SolveSL2 := function(gens, B, F)
  local q, w, n, Binv, act, st, tries, x, X, ev, mu, v1, v2, s, m, delta,
        I2, getRoot, u1, u2, P, Pinv, inP, vals, els, idx, bas, c, tt,
        e21, a, Bn, std, LGO, l, one;

  q := Size(F); w := Z(q); n := Length(B); one := One(F);
  if q <= 11 then return SLNat.SL2BruteForce(gens, B, F); fi;

  Binv := B^-1;
  act := g -> SLNat.BlockAct(B, Binv, [1, 2], g);
  st := SLNat.PRInit(gens);
  I2 := IdentityMat(2, F);

  # (1) x in SL(2) with eigenvalues mu, mu^-1, mu primitive
  tries := 0;
  repeat
    tries := tries + 1;
    x := Comm(SLNat.PRNext(st), SLNat.PRNext(st));
    X := act(x);
    ev := Eigenvalues(F, X);
    if Length(ev) = 2 and Order(ev[1]) = q - 1 then break; fi;
  until tries > 1000;
  if tries > 1000 then return fail; fi;
  mu := ev[1];
  v1 := NullspaceMat(X - mu * I2)[1];
  v2 := NullspaceMat(X - mu^-1 * I2)[1];
  # delta = x^m acts as w on v1, w^-1 on v2
  s := LogFFE(mu, w);
  m := (1 / s) mod (q - 1);
  delta := x^m;

  # (2) Conder--Leedham-Green: an element C fixing the line <v>,
  # then [x, C] is a root element in the stabiliser of <v>
  getRoot := function(v)
    local tries, r, R, w1, w2, c12, y, Y, d12, rho, j, C, u, U, vC;
    for tries in [1..200] do
      r := SLNat.PRNext(st); R := act(r);
      w1 := v1 * R; w2 := v2 * R;       # eigenvectors of x^r
      c12 := SolutionMat([w1, w2], v);
      if c12 <> fail and not IsZero(c12[1]) and not IsZero(c12[2]) then
        y := SLNat.PRNext(st); Y := act(y);
        d12 := SolutionMat([w1, w2], v * Y^-1);
        if not IsZero(d12[1]) and not IsZero(d12[2]) then
          rho := (d12[1] * c12[2]) / (d12[2] * c12[1]);
          j := LogFFE(rho, mu^2);
          if j <> fail then
            C := (x^r)^j * y;
            vC := v * act(C);
            if RankMat([v, vC]) = 1 then
              u := Comm(x, C);
              U := act(u);
              if not IsOne(U) then return u; fi;
            fi;
          fi;
        fi;
      fi;
    od;
    return fail;
  end;
  u1 := getRoot(v1);     # fixes v1: v2 -> v2 + g v1  (E_21 in basis v1,v2)
  u2 := getRoot(v2);     # fixes v2: v1 -> v1 + g v2  (E_12 in basis v1,v2)
  if u1 = fail or u2 = fail then return fail; fi;

  P := [v1, v2]; Pinv := P^-1;
  inP := g -> P * act(g) * Pinv;

  # t = E_12(1) in basis (v1,v2): conjugates u2^(delta^l) = E_12(g w^-2l)
  vals := []; els := [];
  for l in [0..4 * DegreeOverPrimeField(F) + 4] do
    Add(els, u2^(delta^l));
    Add(vals, SLNat.TransInfo(inP(els[l + 1]))[3]);
  od;
  idx := SLNat.IndependentIndices(F, vals);
  if Length(idx) < DegreeOverPrimeField(F) then return fail; fi;
  bas := Basis(F, vals{idx});
  c := SLNat.FpCoeffs(bas, one);
  tt := Product([1..Length(idx)], i -> els[idx[i]]^c[i]);

  # E_21(-1) likewise from u1
  vals := []; els := [];
  for l in [0..4 * DegreeOverPrimeField(F) + 4] do
    Add(els, u1^(delta^l));
    Add(vals, SLNat.TransInfo(inP(els[l + 1]))[3]);
  od;
  idx := SLNat.IndependentIndices(F, vals);
  if Length(idx) < DegreeOverPrimeField(F) then return fail; fi;
  bas := Basis(F, vals{idx});
  c := SLNat.FpCoeffs(bas, -one);
  e21 := Product([1..Length(idx)], i -> els[idx[i]]^c[i]);

  a := tt * e21 * tt;              # [[0,1],[-1,0]]
  std := [a, a, tt, delta];
  Bn := Concatenation(P * B{[1, 2]}, B{[3..n]});
  LGO := SLNat.LGOStandardGenerators(2, q);
  if List(std, g -> SLNat.BlockAct(Bn, Bn^-1, [1, 2], g)) <> LGO then
    Info(InfoSLNat, 1, "SolveSL2: verification failed");
    return fail;
  fi;
  return SLNat.ToolkitFromStd(std, Bn, 2, F);
end;

#############################################################################
##  Splitting involution
#############################################################################
SLNat.FindSplitInvolution := function(st, act, k, F)
  local tries, g, X, o, z, Z, Ep, Em, f, I;
  I := IdentityMat(k, F);
  for tries in [1..300] do
    g := SLNat.PRNext(st);
    X := act(g);
    o := Order(X);
    if IsEvenInt(o) then
      z := g^(o / 2); Z := X^(o / 2);
      Ep := NullspaceMat(Z - I); Em := NullspaceMat(Z + I);
      f := Length(Ep);
      if f >= 1 and f <= k - 1 and
         ((3 * f >= k and 3 * f <= 2 * k) or tries > 60) then
        return [z, Ep, Em];
      fi;
    fi;
  od;
  return fail;
end;

#############################################################################
##  Glue: tk1 (SL(f) on W1) and tk2 (SL(k-f) on W2) -> toolkit for SL(k)
##  st   : random process for H (acting as SL(k) on W1+W2)
##  Cst  : random process for the centraliser of z = diag(1_f, -1_{k-f})
##  comp : rows spanning the complement on which everything is trivial
#############################################################################
SLNat.Glue := function(st, Cst, tk1, tk2, f, k, comp, F)
  local q, w, qm, Bc, Bcinv, n, act, els, vecs, tries, c, M, d1, d2, sol,
        cp, D1, D2, l1, l2, Ip, IP, Cgens, others, Cpst, g2, B2, B2inv,
        sl2, S, Sinv, Ecross, Edown, cacheA, cacheB, T, LGO, std, i, id;

  q := Size(F); w := Z(q); qm := q - 1;
  Bc := Concatenation(tk1.B{[1..f]}, tk2.B{[1..k-f]}, comp);
  Bcinv := Bc^-1; n := Length(Bc);
  act := g -> SLNat.BlockAct(Bc, Bcinv, [1..k], g);
  id := tk1.id;

  # (1) element of C acting with determinants (-1,-1) on (W1,W2)
  els := []; vecs := []; sol := fail; tries := 0;
  repeat
    tries := tries + 1;
    c := SLNat.PRNext(Cst); M := act(c);
    d1 := DeterminantMat(M{[1..f]}{[1..f]});
    d2 := DeterminantMat(M{[f+1..k]}{[f+1..k]});
    Add(els, c); Add(vecs, [LogFFE(d1, w), LogFFE(d2, w)]);
    sol := SolutionIntMat(Concatenation(vecs, [[qm, 0], [0, qm]]),
                          [qm / 2, qm / 2]);
  until sol <> fail or tries > 100;
  if sol = fail then return fail; fi;
  cp := id;
  for i in [1..Length(els)] do
    if sol[i] <> 0 then cp := cp * els[i]^sol[i]; fi;
  od;

  # (2) I' = -1 on e_1 and e_{f+1}, +1 elsewhere
  M := act(cp);
  D1 := MutableCopyMat(IdentityMat(f, F)); D1[1][1] := -One(F);
  D2 := MutableCopyMat(IdentityMat(k - f, F)); D2[1][1] := -One(F);
  l1 := tk1.Word(M{[1..f]}{[1..f]}^-1 * D1);
  l2 := tk2.Word(M{[f+1..k]}{[f+1..k]}^-1 * D2);
  Ip := cp * l1 * l2;
  IP := MutableCopyMat(IdentityMat(k, F));
  IP[1][1] := -One(F); IP[f+1][f+1] := -One(F);
  if act(Ip) <> IP then Error("Glue: construction of I' failed"); fi;

  # (3) its centraliser; kill the (k-2)-dimensional factor
  others := Difference([1..k], [1, f + 1]);
  Cgens := SLNat.InvolutionCentraliser(st, Ip, act, Bc, Bcinv,
                                       [[1, f + 1]], F, 10);
  if Cgens = fail then return fail; fi;
  Cpst := SLNat.PRInit(Cgens);
  g2 := SLNat.KillFactor(Cpst, [1, f + 1], others, Bc, Bcinv, F, 6);
  if g2 = fail then return fail; fi;

  # (4) recognise the SL(2) on <e_1, e_{f+1}>
  B2 := Concatenation(Bc{[1, f + 1]}, Bc{others}, comp);
  sl2 := SLNat.SolveSL2(g2, B2, F);
  if sl2 = fail then return fail; fi;
  B2inv := B2^-1;
  S := (sl2.B{[1, 2]} * B2inv){[1, 2]}{[1, 2]};   # v's in basis (e1,e_f+1)
  Sinv := S^-1;
  Ecross := lam -> sl2.Word(S * [[One(F), lam], [Zero(F), One(F)]] * Sinv);
  Edown  := lam -> sl2.Word(S * [[One(F), Zero(F)], [lam, One(F)]] * Sinv);

  # (5) all transvections of SL(k) in the basis Bc
  cacheA := []; cacheB := [];
  T := function(i, j, lam)
    if IsZero(lam) then return id; fi;
    if i <= f and j <= f then return tk1.T(i, j, lam);
    elif i > f and j > f then return tk2.T(i - f, j - f, lam);
    elif i <= f then                       # i in W1, j in W2
      if i = 1 and j = f + 1 then return Ecross(lam);
      elif i = 1 then
        return Comm(Ecross(lam), tk2.T(1, j - f, One(F)));
      else
        if not IsBound(cacheA[j]) then cacheA[j] := T(1, j, One(F)); fi;
        return Comm(tk1.T(i, 1, lam), cacheA[j]);
      fi;
    else                                   # i in W2, j in W1
      if i = f + 1 and j = 1 then return Edown(lam);
      elif i = f + 1 then
        return Comm(Edown(lam), tk1.T(1, j, One(F)));
      else
        if not IsBound(cacheB[j]) then cacheB[j] := T(f + 1, j, One(F)); fi;
        return Comm(tk2.T(i - f, 1, lam), cacheB[j]);
      fi;
    fi;
  end;

  # (6) standard generators of SL(k) by row reduction
  LGO := SLNat.LGOStandardGenerators(k, q);
  std := List(LGO, X -> SLNat.Eliminate(T, X, k, F, id));
  if List(std, act) <> LGO then
    Error("Glue: standard generators wrong");
  fi;
  return SLNat.ToolkitFromStd(std, Bc, k, F);
end;

#############################################################################
##  Main recursion.  gens act on span(B{[1..k]}) as a group containing
##  SL(k) and trivially on span(B{[k+1..n]}).
#############################################################################
SLNat.Solve := function(gens, B, k, F)
  local n, attempt, Binv, act, st, inv, z, W, Ep, Em, f, Bn, Bninv,
        blk1, blk2, C, Cst, g1, g2, tk1, tk2, B2, tk, comp;
  n := Length(B);
  if k = 1 then return SLNat.ToolkitFromStd([gens[1]^0], B, 1, F); fi;
  if k = 2 then return SLNat.SolveSL2(gens, B, F); fi;
  comp := B{[k+1..n]};
  for attempt in [1..3] do
    Info(InfoSLNat, 2, "Solve: dimension ", k, ", attempt ", attempt);
    Binv := B^-1;
    act := g -> SLNat.BlockAct(B, Binv, [1..k], g);
    st := SLNat.PRInit(gens);
    inv := SLNat.FindSplitInvolution(st, act, k, F);
    if inv <> fail then
      z := inv[1];
      W := B{[1..k]};
      Ep := inv[2] * W; Em := inv[3] * W;
      f := Length(Ep);
      Info(InfoSLNat, 2, "split ", k, " = ", f, " + ", k - f);
      Bn := Concatenation(Ep, Em, comp); Bninv := Bn^-1;
      blk1 := [1..f]; blk2 := [f+1..k];
      C := SLNat.InvolutionCentraliser(st, z, act, Bn, Bninv,
                                       [blk1, blk2], F, 10);
      if C <> fail then
        Cst := SLNat.PRInit(C);
        # block 1 (on Ep)
        if f >= 2 then
          g1 := SLNat.KillFactor(Cst, blk1, blk2, Bn, Bninv, F, 6);
        else
          g1 := [z^0];
        fi;
        # block 2 (on Em)
        B2 := Concatenation(Em, Ep, comp);
        if k - f >= 2 then
          g2 := SLNat.KillFactor(Cst, blk2, blk1, Bn, Bninv, F, 6);
        else
          g2 := [z^0];
        fi;
        if g1 <> fail and g2 <> fail then
          tk1 := SLNat.Solve(g1, Bn, f, F);
          tk2 := SLNat.Solve(g2, B2, k - f, F);
          if tk1 <> fail and tk2 <> fail then
            tk := SLNat.Glue(st, Cst, tk1, tk2, f, k, comp, F);
            if tk <> fail then return tk; fi;
          fi;
        fi;
      fi;
    fi;
  od;
  return fail;
end;

#############################################################################
##  User functions
#############################################################################

##  RecogniseSLNatural(G)
##  G <= GL(n,q), q odd, n >= 2, containing SL(n,q) (not checked; use
##  e.g. RecogniseClassical from the recog package to name G first).
##  Returns a record with
##    stdgens : the standard generators (elements of G)
##    slp     : SLP from GeneratorsOfGroup(G) to stdgens
##    cb      : cb * stdgens[i] * cb^-1 = LGOStandardGenerators(n,q)[i]
##  and data for SLNaturalElementToSLP.
SLNat.RecogniseSLNatural := function(G)
  local F, n, q, gens, mgens, attempt, tk, std, slp, cb, LGO, mstd, rtk;
  F := DefaultFieldOfMatrixGroup(G);
  n := DimensionOfMatrixGroup(G); q := Size(F);
  if IsEvenInt(q) then Error("only odd characteristic is implemented"); fi;
  if n < 2 then Error("dimension must be at least 2"); fi;
  gens := GeneratorsOfGroup(G);
  mgens := GeneratorsWithMemory(gens);
  tk := fail; attempt := 0;
  while tk = fail and attempt < 3 do
    attempt := attempt + 1;
    tk := SLNat.Solve(mgens, IdentityMat(n, F), n, F);
  od;
  if tk = fail then return fail; fi;
  std := tk.std;
  slp := SLPOfElms(std);
  cb := tk.B;
  # checks: matrices and SLPs
  LGO := SLNat.LGOStandardGenerators(n, q);
  std := List(std, StripMemory);
  if List(std, g -> cb * g * cb^-1) <> LGO then
    Error("RecogniseSLNatural: wrong standard generators");
  fi;
  if ResultOfStraightLineProgram(slp, gens) <> std then
    Error("RecogniseSLNatural: wrong SLP");
  fi;
  # rewriting machinery in terms of the standard generators
  mstd := GeneratorsWithMemory(std);
  rtk := SLNat.ToolkitFromStd(mstd, cb, n, F);
  return rec(n := n, q := q, F := F, gens := gens, stdgens := std,
             slp := slp, cb := cb, rtk := rtk);
end;

##  SLNaturalElementToSLP(ri, g)
##  SLP for g in SL(n,q) in the standard generators ri.stdgens
##  (compose with ri.slp via CompositionOfStraightLinePrograms to get an
##  SLP in the original generators); fail if det(g) <> 1.
SLNat.ElementToSLP := function(ri, g)
  local M, x;
  if not IsOne(DeterminantMat(g)) then return fail; fi;
  M := ri.cb * g * ri.cb^-1;
  x := ri.rtk.Word(M);
  return SLPOfElm(x);
end;

RecogniseSLNatural := SLNat.RecogniseSLNatural;
SLNaturalElementToSLP := SLNat.ElementToSLP;
LGOStandardGeneratorsSL := SLNat.LGOStandardGenerators;

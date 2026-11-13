#############################################################################
##
##  Fake projective plane groups: the maximal arithmetic subgroups
##  \bar\Gamma of PU(2,1) from Tables 1 and 2 of
##    D. Cartwright, T. Steger, Enumeration of the 50 fake projective planes,
##    C. R. Acad. Sci. Paris, Ser. I 348 (2010) 11-13,
##  given by a finite presentation together with matrices for the generators.
##
##  Source data: the files of Cartwright and Steger at
##    https://www.maths.usyd.edu.au/u/donaldc/fakeprojectiveplanes/
##  (bargammapresentations.txt for the presentations; the files
##   <case>/gp..generators_reducesyntax.txt for the matrices; register names
##   as in registerofgps.txt). The presentations and REDUCE matrix
##  definitions were transcribed and re-evaluated exactly; nothing was
##  recomputed from scratch.
##
##  After  Read("fakeplanes.g");  the list  FakeProjectivePlaneGroups
##  contains 28 records, one for each row of Tables 1 and 2, with components
##
##    name          string identifying the row of Table 1 / Table 2:
##                  "<ell>, p=<p>, T1={...}"   (Table 1, k = Q)
##                  "C<i>, p=<p>, T1={...}"     (Table 2)
##    csName        the name used in Cartwright-Steger's files
##    k, ell, p, T1 the data of the row (as strings / integer)
##    N             the index N from the tables
##    numberOfFakePlanes   the number of fake planes Pi in the class
##    presentation  a finitely presented group G isomorphic to \bar\Gamma
##    matrix        list of 3x3 matrices over `field', one for each generator
##                  of `presentation' (same order). g -> matrix is a
##                  homomorphism into PGL(3,field): every relator evaluates
##                  to a SCALAR matrix (the group lives in PU(2,1)).
##    field         the number field (a FieldExtension of the rationals)
##                  containing the entries (it contains ell)
##    form          hermitian matrix F with  conj(M)^T * F * M = F  for all
##                  matrices M in `matrix'
##    conj          the field automorphism used in the line above (it acts
##                  as complex conjugation on ell/k)
##    fakePlanes    list of records rec(name, generators, index, abInv)
##                  describing the torsion-free subgroups Pi of index N
##                  (fundamental groups of the fake planes), generators
##                  as words in the generators of `presentation', index
##                  = N, abInv = AbelianInvariants of Pi (GAP format).
##
##  For the three rows with T1={2I} (Iwahori case, N=1) the group is the
##  index 3 (resp. 9) subgroup of the \bar\Gamma of the row with T1={}
##  given by Cartwright-Steger; its presentation (on those subgroup
##  generators) was computed in GAP by Reidemeister-Schreier, and its
##  matrices are the corresponding products of the parent's matrices.
##
##  Example:
##    gap> r := FakeProjectivePlaneGroups[8];; r.name;
##    "Q(sqrt(-7)), p=2, T1={7}"
##    gap> G := r.presentation;; M := r.matrix;;
##    gap> ForAll(RelatorsOfFpGroup(G), w ->
##    >      IsDiagonalMat(MappedWord(w, FreeGeneratorsOfFpGroup(G), M)));
##    true
##    gap> Pi := Subgroup(G, r.fakePlanes[1].generators);; Index(G, Pi);
##    21
##
#############################################################################

FakeProjectivePlaneGroups := [];


#############################################################################
##  k = Q,  ell = Q(sqrt(-1)),  p = 5
##  Field generators: i^2 = -1; Z^3 = 3*Z^2+2
##  (conj: i -> -i, Z -> Z)
CallFuncList(function()
local x, F, t, tbar, conj, form, f, G, mats, H, subgens, one, i, Z, a, b, c;
x := Indeterminate(Rationals, "x");
F := FieldExtension(Rationals, x^6+9*x^4-12*x^2+4);
one := One(F);
t := RootOfDefiningPolynomial(F);   # t = i*Z
i := (-3/4*t^5-29/4*t^3+9/2*t)*one;
Z := (1/2*t^4+9/2*t^2-3)*one;
tbar := (-t)*one;   # image of t under conj
conj := e -> ValuePol(ExtRepOfObj(e), tbar);
form := [ [ 5, 0, 0 ],
          [ 0, 0, 1 ],
          [ 0, 1, 0 ] ]*one;

# Q(sqrt(-1)), p=5, T1={}   [(a=1,p=5,\emptyset)]
f := FreeGroup("a", "b", "c");
a := f.1;
b := f.2;
c := f.3;
G := f / [
  b^3,
  c^-1*b^-1*a*b^-1*a*b^-1*c^-1,
  b*a*c*b*a^-1*b^-1*c^-1*b^-1*c^-1*b^-1*c^-1*a^-1*b^-1*c^-1*b^-1*a^-1*c,
  c^-1*a^-1*b*c^-1*b^-1*a*c^-1*a*b*c*b*a*c*b*a^-1*b^-1*c*b*a^-1,
  a^-1*c*b^-1*a*b*a*b*a*c*b*a^-1*c*b*a^-1*b^-1*a*c*b*a^-1,
  b^-1*a^-1*c*a^-1*b*c*b^-1*a*c*b*a^-1*c^-1*b^-1*c^-1*a^-1*b^-1*c^-1*b^-1*a^-1,
  c*a^-1*b*c*b^-1*a*c*b*a^-2*b^-1*a^-1*b^-1*a^-1*b^-1*a*c^-1*b^-1*a,
  c^-1*a^-1*b*c*b*a^-1*b^-1*a*c^-1*b^-1*a*b*c^-1*b^-1*c^-1*a^-1*b^-1*c*b*a^-1,
  c*b*c*b*a*b^-1*c^-1*a^-1*b*a*b^-1*c*a*b^-1*c^-1*a*b^-1*c^-1*b*a,
  b*a*b*c*b*a*c*a*b^-1*a^-1*b^-1*a^-1*b^-1*a^-1*b*c^-1*a*c*b^-1*a,
  c*b^-1*a*b*a*b*c*b^-1*a*b*a*b*a^2*b^-1*c^-1*b*a*c*b*a^-1,
  c*b*a*c^-1*b^-1*a*c*a^-1*b*c^-1*b^-1*a*b*a^-1*b^-1*a*c*b*a^-1*b^-1*c^-1*a^-1,
  b*a*b*a*c*b^-1*c*a^-1*b*c*b^-1*a*c^-1*b^-1*a^2*c*b*a^-1*c*b^-1*a,
  c^-1*b^-1*c^-1*a^-1*b*a*b*a*b*a*c^-1*a^-1*b^-1*c^-1*a*b^-1*c^-1*a^-1*b^-1*c*b*a^-1,
  a^-1*b^-1*a^-1*b^-1*a^-1*b^-1*a*c*b*a^-1*b^-1*c^-1*a^-1*c*b^-1*a*b*a*b*a^2*b^-1*c^-1,
  c*b*a^-2*b^-1*a^-1*b^-1*a^-2*b*c*a^-1*b^-1*c^-1*b^-1*a^-1*b^-1*a^-1*c*b^-1*a*b*a,
  a^-1*c*b^-1*a*b*a*b*a*c^-2*b*c^-1*a*b^-1*c^-1*a^-1*b^-1*c*b*a^-1*c^-1*a^-1*b^-1*c^-1
];
mats := [
  # a  (AA in the source file)
  [ [ (-7*i*Z^2+3*Z^2+19*i*Z+3*Z-4*i-24)/18, (i*Z^2-4*i*Z-3*Z+i+9)/18, (i*Z^2-i*Z-2*i)/9 ],
    [ (-5*i*Z^2-15*Z^2+5*i*Z+45*Z+10*i)/18, (11*i*Z^2+3*Z^2-35*i*Z-9*Z-4*i-12)/18, (-i*Z^2+4*i*Z-i+3)/9 ],
    [ (5*i*Z^2-20*i*Z+15*Z+5*i+15)/18, (-5*i*Z^2+15*Z^2+5*i*Z-45*Z+10*i)/18, (-2*i*Z^2-3*Z^2+8*i*Z+3*Z-5*i)/9 ] ]*one,
  # b  (BB in the source file)
  [ [ (-2*i*Z^2+Z^2+11*i*Z+2*Z-5*i-5)/18, (-i*Z^2+2*Z^2-2*i*Z-5*Z+11*i-1)/18, (-7*i*Z^2-4*Z^2+16*i*Z+7*Z+11*i+17)/90 ],
    [ (-i*Z^2+8*Z^2+4*i*Z-17*Z+5*i+5)/18, (2*i*Z^2-Z^2-8*i*Z+4*Z+2*i-1)/9, (i*Z^2+Z^2-i*Z-4*Z+i+1)/9 ],
    [ (-5*i*Z^2-20*Z^2+20*i*Z+65*Z+25*i-5)/18, (4*i*Z^2-2*Z^2-10*i*Z+5*Z+i+7)/9, (-2*i*Z^2+Z^2+5*i*Z-10*Z+i+7)/18 ] ]*one,
  # c  (CC in the source file)
  [ [ (-3*i*Z^2-2*Z^2-Z+3*i+13)/18, (6*i*Z^2+5*Z^2-21*i*Z-14*Z+15*i-7)/18, (Z^2-3*i*Z-4*Z+3*i-5)/18 ],
    [ (5*Z^2+15*i*Z-20*Z-15*i-25)/18, (-3*i*Z^2+7*Z^2+15*i*Z-19*Z-12*i+4)/18, (-2*Z^2+3*i*Z+2*Z+3*i+1)/9 ],
    [ (-30*i*Z^2-5*Z^2+75*i*Z+50*Z+75*i-65)/18, (-5*Z^2+20*Z-20)/9, (6*i*Z^2-5*Z^2-15*i*Z+20*Z-9*i+1)/18 ] ]*one
];
Add(FakeProjectivePlaneGroups, rec(
  name := "Q(sqrt(-1)), p=5, T1={}",
  fieldGens:=[[i,Z],["I","Z"]],
  csName := "(a=1,p=5,\\emptyset)",
  k := "Q", ell := "Q(sqrt(-1))", p := 5, T1 := "{}",
  N := 3, numberOfFakePlanes := 1,
  presentation := G, matrix := mats, field := F, form := form, conj := conj,
  fakePlanes := [
    rec(name := "(a=1,p=5,\\emptyset,D_3)",
        generators := List([a, b*c*b^-1, b^-1*c*b], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 3, abInv := [ 2, 4, 31 ]) ] ));

# Q(sqrt(-1)), p=5, T1={2I}   [(a=1,p=5,\{2I\})]
# the subgroup of the group above generated by c*b^-1, b*a*b, b^-1*a*b^-1
subgens := List([c*b^-1, b*a*b, b^-1*a*b^-1], w -> MappedWord(w, GeneratorsOfGroup(f), mats));
H := CallFuncList(function()
  local fs, s1, s2, s3;
  fs := FreeGroup("s1", "s2", "s3");
  s1 := fs.1;
  s2 := fs.2;
  s3 := fs.3;
  return fs / [
    s2^-1*s1*s2^-1*s3^-3*s1*s2^-2*s3^-2*s1*s2^-2*s3*s1*s2^-2,
    s2^2*s1^-1*s3*s1*s2*s1^-1*s3^-1*s1*s3*s1*s2^-3*s1*s2^-2*s3^-1,
    s3^-3*s2^3*s1^-1*s3^-1*s1^-1*s3^-1*s1*s3^-2*s1*s2*s1^-1*s3^-1*s1,
    s2*s1^-1*s3^-1*s1*s3*s1^-1*s3^2*s1*s2^-1*s1^-1*s3^-1*s1*s2^-2*s3^-1*s2^2,
    s2^-1*s3*s1*s2^-3*s3*s1*s2*s1^-1*s3^-1*s2^-1*s3^-1*s1*s3^-2*s1*s3^-1*s2^2*s1^-1*s3^3,
    s2^-1*s3^-3*s2^3*s1^-2*s3*s1*s2^-3*s3^3*s2*s1^-1*s2^2*s1^-1*s3^-1*s1,
    s3^-1*s1*s3^-3*s1*s2*s1^-1*s3^-1*s1*s3*s1^-1*s3*s2^-1*s1*s2^-1*s3^-3*s2^3*s1^-1*s3^-1*s1*s3^-1,
    s3^3*s1^-1*s3*s1*s2^-1*s3^-1*s1*s3^-1*s1^-1*s3*s1*s2^-1*s1^-1*s3^-1*s2^3*s1^-1*s3^-1*s2^-1*s3^-1*s2^2*s1^-1,
    s1*s2^-1*s3^-3*s1*s2^-2*s3*s1^-1*s3*s1^-1*s3^-1*s1*s3^-1*s1^-1*s3*s1*s2^-1*s3^-3*s1*s2^-2*s3,
    s1^-1*s3*s1*s3*s1^-2*s3*s1*s2^-1*s1^-1*s3^-1*s2^3*s1^-1*s3^-1*s1^-1*s2*s1^-1*s3^-1*s1*s2*s1^-1*s3^-1*s1*s3,
    s1^-1*s3^-3*s2^3*s1^-1*s3^-1*s2^-1*s1^-1*s3*s1^-1*s2^-1*s3^-1*s1*s3^-1*s1^-1*s3^-1*s1*s3^-1*s1^-1*s3*s1*s2^-1*s1^-1*s3^2,
    s3^3*s2^2*s1^-1*s3^-1*s2^2*s1^-1*s3^3*s1^-1*s3^2*s1^-1*s2^2*s1^-1*s3^3*s2^-2*s3^2*s2^2*s1^-1,
    s1^-1*s3*s1^3*s2^-3*s1*s2^-2*s3^-2*s2^2*s1^-1*s3*s1*s2^-1*s3*s1*s2^-1*s1^-1*s3^-1*s1*s2*s1^-1*s3^-1*s1*s3,
    s1*s3^-1*s1^-1*s3^-1*s1*s3^-1*s1^-1*s3*s1*s2^-1*s1^-1*s3*s1^2*s3^-1*s1*s2*s3*s1*s2^-3*s3^4*s1*s2^-1*s3^-3*s1*s2^-2,
    s1^-1*s3*s1*s2^-1*s1^-1*s3*s1^-1*s3^-3*s2^3*s1^-1*s3^-1*s2^-1*s1^-1*s3*s1^-1*s3*s1*s2^-3*s3^4*s1*s2^-3*s1*s2^-1,
    s3^-3*s1*s2^-2*s3^-2*s2^2*s3^-1*s2^2*s1^-1*s3^3*s2^-1*s3^-2*s2^2*s1^-1*s3*s1*s2*s1^-1*s3^-1*s2*s1^-1*s3^-1*s1*s3^-3*s1*s2^-2*s3*s2,
    s2^-1*s3^-1*s1*s3^-1*s1^-1*s2*s1^-1*s3^-1*s1*s2^-1*s3^-3*s2^3*s1^-1*s3^-1*s1^3*s2^-3*s3^3*s2*s1^-1*s3*s1*s2*s1^-1*s3^-4*s2^3*s1^-1*s3^-1,
    s3*s1*s2^-2*s3*s1*s2^-3*s3*s1*s2*s1^-1*s3^-1*s1*s3^-1*s1*s2*s3*s1*s2^-3*s3^4*s1*s2^-1*s3^-1*s2^2*s1^-1*s3^3*s1^-1*s3*s1*s2^-1*s1*s3^-1*s1*s2*s3*s1*s2^-3*s3^3,
    s3^2*s1^-1*s3*s1*s2^-1*s3^-1*s2^2*s1^-1*s3^3*s1^-1*s3*s1*s2^-2*s1*s2^2*s1^-1*s3^-1*s2^2*s1^-1*s3^3*s1^-1*s3^2*s1^-2*s3^-1*s1*s3^-1*s1^-1*s3*s1*s2^-1*s1^-1*s3*s1*s2^-2*s1*s2^-2*s3^-2*s2^2*s1^-1,
    s1^-1*s3*s1*s2*s1^-1*s3^-1*s1*s2^-1*s3^-1*s2^2*s1^-1*s3^3*s1^-1*s3*s1*s2^-1*s1*s2^-3*s1*s2^-2*s3^-2*s1*s2^-1*s1^-1*s3^-1*s1*s2^-1*s3^-3*s2^3*s1^-1*s3^-1*s1^2*s3^-1*s1*s2*s3*s1*s2^-3*s3^4*s1*s2^-1,
    s2^2*s1^-1*s3^3*s1^-1*s3*s1*s2^-1*s3^-1*s1*s2*s1^-1*s3^-1*s1*s3^-3*s1*s2^-2*s3*s2^-1*s3^-1*s2^2*s1^-1*s3^-1*s2^3*s1^-1*s3^-1*s1^-1*s2^2*s1^-1*s3^-1*s1*s3^-3*s1*s2^-2*s3*s2*s1^-1*s3^-1*s1*s3^-2*s1*s2^-2*s3^2*s2*s3^-1 ];
end, []);
Add(FakeProjectivePlaneGroups, rec(
  name := "Q(sqrt(-1)), p=5, T1={2I}",
  fieldGens:=[[i,Z],["I","Z"]],
  csName := "(a=1,p=5,\\{2I\\})",
  k := "Q", ell := "Q(sqrt(-1))", p := 5, T1 := "{2I}",
  N := 1, numberOfFakePlanes := 1,
  presentation := H, matrix := subgens, field := F, form := form, conj := conj,
  fakePlanes := [ rec(name := "(a=1,p=5,\\{2I\\})", generators := GeneratorsOfGroup(H), index := 1, abInv := [ 2, 3, 4, 4 ]) ] ));

# Q(sqrt(-1)), p=5, T1={2}   [(a=1,p=5,\{2\})]
f := FreeGroup("a", "b", "c");
a := f.1;
b := f.2;
c := f.3;
G := f / [
  (a^-1*b)^3,
  (c*b^-1*c)^3,
  (a^-1*b^-1*a*b^-1)^3,
  a^-1*c^-1*b*a*b*c^-1*b*c*b^-1*c*b*c^-2,
  a^-1*c^-1*b*a*b*a^-2*b*a^-2*b^-1*c*b^-2,
  b^-1*a^-1*c^-1*b*c^-1*b*c^-1*a*b^-2*a^2*b*a^-1*c,
  c^2*b^-1*c*a^2*b^-1*a^2*b^-1*a*c^-1*b*a^2*b^-1*a,
  c^-2*b*c^-1*a*b*a^-1*b^2*a^-1*b^-1*a^-1*c^-1*b*a^2*b^-1*a,
  c^-1*b*a*b*a*b^-1*c^2*b^-1*c^-1*b*c^-1*a*b*a*b*a^-1*c^-1*a^-1,
  c^-1*b*c^-1*b*c^-1*b^-1*a^-1*c^-1*b*c^-1*a*b^-2*a*c^-1*b*a^2*b^-1,
  a^-1*c*b*c^-1*a*b^-1*a^-3*b^-1*a^-1*b^-1*c*b*a^-2*b^-1*c*b^-1,
  c*b^-1*c*a*b^-1*a^-2*b^2*a^-1*b^-1*a^-1*c^-1*b^-1*a^-1*c^-1*b*a*b*a^-1,
  b^-1*a^-1*c^-1*b*a^2*b^-1*c*b^-1*c*b^-1*c*a*c*b^-1*c*a*b^-1*a^-1*b^-1,
  c^-1*b*c^-2*a*b^-1*a^-1*c^-1*b*a*b*a^-1*b*c*b^-1*c*a*b^-1*a^-1*b^-1*a^-1,
  c*b*c^-1*a*b^-1*a^-3*c^-1*b*c*b^-1*c^2*a*b*a^-1*b^2*a^-2,
  b^-1*a^-1*b*a^-2*b^-1*c*b^-1*a^-1*b*c^-1*b*c^-2*a^2*b*a^-1*c*b^-1*c^-1,
  b^-1*c*a*b*a^-1*c^-1*b*c*b^-1*c*b^-2*a*b^-1*a^-1*b^-1*c*b^-1*a^-1*c^2*b^-1*c,
  b^-1*a^-1*c^-1*b*a^-1*b^2*a^-1*c*b^-1*c*a*b*a*c^-2*b*c^-1*b^-1*a*b^-1*a^-1*b^-1,
  a^2*b*a^-1*c*b^-1*c^-1*b*a*b*a^-1*b^2*a^-2*c*b^-1*c*a*b^-1*a^-2*b,
  c*b^-1*c*b^-1*c*a*c^-1*b*c^-1*b^-1*c*a*c^-1*a*b^-1*a^-1*b^-1*a^-1*c^-1*b*c^-2*a
];
mats := [
  # a  (AD in the source file)
  [ [ (-2*i*Z^2+3*Z^2+5*i*Z-6*Z+7*i+3)/18, (i*Z^2-15*Z^2+11*i*Z+45*Z-32*i+6)/36, (-i*Z^2+4*i*Z-i+3)/9 ],
    [ (5*i*Z^2-20*i*Z+15*Z+5*i+15)/18, (2*i*Z^2-5*i*Z+2*i+3)/9, (-4*i*Z^2+i*Z+3*Z+2*i)/18 ],
    [ (35*i*Z^2+75*Z^2-65*i*Z-255*Z-130*i+60)/36, (5*i*Z^2-20*i*Z-15*Z+5*i+45)/18, (-2*i*Z^2-3*Z^2+5*i*Z+6*Z+7*i+9)/18 ] ]*one,
  # b  (BD in the source file)
  [ [ (5*Z^2+3*i*Z-14*Z-21*i-7)/18, (3*i*Z^2+5*Z^2-9*i*Z-17*Z+6*i-4)/36, (9*i*Z^2-2*Z^2-12*i*Z+11*Z-9*i+7)/90 ],
    [ (-3*i*Z^2-11*Z^2-3*i*Z+29*Z+18*i+16)/18, (3*i*Z^2-4*Z^2-6*i*Z+13*Z-21*i-7)/18, (-2*Z^2+3*i*Z+5*Z-2)/18 ],
    [ (-15*i*Z^2-5*Z^2+15*i*Z+35*Z+60*i-50)/36, (-6*i*Z^2+13*Z^2+15*i*Z-40*Z+9*i+13)/18, (-3*i*Z^2-Z^2+3*i*Z+Z-12*i-4)/18 ] ]*one,
  # c  (CD in the source file)
  [ [ (-7*i*Z^2+3*Z^2+19*i*Z+3*Z-4*i-24)/18, (i*Z^2-4*i*Z-3*Z+i+9)/18, (i*Z^2-i*Z-2*i)/9 ],
    [ (-5*i*Z^2-15*Z^2+5*i*Z+45*Z+10*i)/18, (11*i*Z^2+3*Z^2-35*i*Z-9*Z-4*i-12)/18, (-i*Z^2+4*i*Z-i+3)/9 ],
    [ (5*i*Z^2-20*i*Z+15*Z+5*i+15)/18, (-5*i*Z^2+15*Z^2+5*i*Z-45*Z+10*i)/18, (-2*i*Z^2-3*Z^2+8*i*Z+3*Z-5*i)/9 ] ]*one
];
Add(FakeProjectivePlaneGroups, rec(
  name := "Q(sqrt(-1)), p=5, T1={2}",
  fieldGens:=[[i,Z],["I","Z"]],
  csName := "(a=1,p=5,\\{2\\})",
  k := "Q", ell := "Q(sqrt(-1))", p := 5, T1 := "{2}",
  N := 3, numberOfFakePlanes := 1,
  presentation := G, matrix := mats, field := F, form := form, conj := conj,
  fakePlanes := [
    rec(name := "(a=1,p=5,\\{2\\},D_3)",
        generators := List([a, c, b*a*b^-1], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 3, abInv := [ 4, 31 ]) ] ));
end, []);

#############################################################################
##  k = Q,  ell = Q(sqrt(-2)),  p = 3
##  Field generators: s^2 = -2; Z^3 = -Z^2-2*Z+2
##  (conj: s -> -s, Z -> Z)
CallFuncList(function()
local x, F, t, tbar, conj, form, f, G, mats, H, subgens, one, s, Z, a, b, c;
x := Indeterminate(Rationals, "x");
F := FieldExtension(Rationals, x^6-4*x^4-28*x^2+128);
one := One(F);
t := RootOfDefiningPolynomial(F);   # t = s*Z+s
s := (1/16*t^5-5/4*t)*one;
Z := (-1/8*t^4-1/4*t^2+3)*one;
tbar := (-t)*one;   # image of t under conj
conj := e -> ValuePol(ExtRepOfObj(e), tbar);
form := [ [ 3, 0, 0 ],
          [ 0, 0, 1 ],
          [ 0, 1, 0 ] ]*one;

# Q(sqrt(-2)), p=3, T1={}   [(a=2,p=3,\emptyset)]
f := FreeGroup("a", "b", "c");
a := f.1;
b := f.2;
c := f.3;
G := f / [
  b^3,
  (b*c*a^-1*c*a)^3,
  a^-1*b^-1*a^-1*c*b*c*a*b*c*a^-1*c*b^-1,
  a^-1*b^-1*a^-1*c*a^-1*b*c*a^-1*b^-1*a^-2*b,
  c^-1*a^-1*b^-1*c^-1*a^-1*b^-1*c^-1*b^-1*a*b*c*a^-1*b^-1,
  b*c*a^-1*b^-1*c^-2*b^-1*c^-1*a*c^-1*b^-1*a*c^-1*b^-1*a^-1,
  a*b*a*b*c*a^-1*c*b^-1*c*a^-1*c*b*c*b*a^2*c^-1,
  a^2*c^-1*a*c^-1*b^-1*a*b*c^2*a^-2*b^-1*a*b*c*a^-1*c,
  a*c^-1*a*c^-1*b^-1*a*b*c*b^-1*a^-1*c*a^-2*b^-1*c*a^-2*b^-1*c^-1,
  b*a^2*c^-1*a*b*a*b^-1*c^-1*a*c^-1*b^-1*a^-1*c*a^-1*c*b^-1*c*b*a,
  a^-1*b^-1*c^-1*b^-1*a^2*b*c*a^-2*b^-1*a^-1*b^-1*a^-1*c*b^-1*c*a^-1*c*b*c
];
mats := [
  # a  (AA in the source file)
  [ [ (2*s*Z^2-Z^2+s*Z-7*Z-s)/10, (-3*s*Z^2+2*Z^2-3*s*Z+8*Z-4*s-2)/20, (s*Z^2+2*Z^2+s*Z-2*s+2)/10 ],
    [ (-3*s*Z^2-3*s*Z-9*s)/5, (-2*s*Z^2+3*Z^2-5*s*Z+5*Z-7*s+8)/10, (s*Z^2-2*Z^2+3*s*Z-2*Z+2*s-6)/10 ],
    [ (3*s*Z^2+6*Z^2-9*s*Z-12*Z-18)/20, (3*s*Z^2-6*Z^2+3*s*Z-6*s-6)/10, (-Z^2+2*s*Z+Z-s+1)/5 ] ]*one,
  # b  (BB in the source file)
  [ [ (-5*s*Z^2+2*Z^2-9*s*Z-8*s+2)/20, (3*s*Z^2-3*s*Z-2*Z+2*s+6)/20, (-5*s*Z^2-4*Z^2-7*s*Z-2*Z-14*s+2)/60 ],
    [ (5*s*Z^2-2*Z^2+5*s*Z+4*Z+6)/20, (s*Z^2-4*Z^2+3*s*Z+6*Z+2*s-2)/20, (-s*Z^2+3*Z^2+5*Z-s+8)/10 ],
    [ (-3*s*Z^2-18*Z^2+9*s*Z-24*Z-6)/20, (3*Z^2+s*Z-Z-3*s+6)/10, (2*s*Z^2+Z^2+3*s*Z-3*Z+3*s)/10 ] ]*one,
  # c  (CC in the source file)
  [ [ (s*Z^2+s*Z-2*Z)/2, 0, 0 ],
    [ 0, (-s*Z^2+Z^2-2*s*Z+Z-3*s+2)/2, 0 ],
    [ 0, 0, (-Z^2+s*Z+Z-s)/2 ] ]*one
];
Add(FakeProjectivePlaneGroups, rec(
  name := "Q(sqrt(-2)), p=3, T1={}",
  fieldGens:=[[s,Z],["r2","Z"]],
  csName := "(a=2,p=3,\\emptyset)",
  k := "Q", ell := "Q(sqrt(-2))", p := 3, T1 := "{}",
  N := 3, numberOfFakePlanes := 1,
  presentation := G, matrix := mats, field := F, form := form, conj := conj,
  fakePlanes := [
    rec(name := "(a=2,p=3,\\emptyset,D_3)",
        generators := List([a, c, b*a*b^-1], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 3, abInv := [ 2, 2, 13 ]) ] ));

# Q(sqrt(-2)), p=3, T1={2I}   [(a=2,p=3,\{2I\})]
# the subgroup of the group above generated by a, c, b*a*b, c^b
subgens := List([a, c, b*a*b, c^b], w -> MappedWord(w, GeneratorsOfGroup(f), mats));
H := CallFuncList(function()
  local fs, s1, s2, s3, s4;
  fs := FreeGroup("s1", "s2", "s3", "s4");
  s1 := fs.1;
  s2 := fs.2;
  s3 := fs.3;
  s4 := fs.4;
  return fs / [
    s2*s3*s4*s1*s2^-1*s3^-1*s4*s1,
    s2*s3*s4*s1^2*s3*s2^-1*s3^-1*s4*s3^-1*s1^-2,
    s1*s2^-1*s3^-1*s4*s3^-1*s2^-1*s3*s4*s1^2*s3*s1,
    s4*s1*s3*s4*s1^2*s2^-1*s3^-1*s1^-1*s2*s1^-2,
    s2*s3*s4^-1*s3*s1*s3^2*s2*s3*s4*s1*s2*s3*s2,
    s2*s3*s4^-1*s3*s1*s2^-1*s3^-1*s1^-1*s4^-1*s2^-1*s1*s2^-1*s3^-1*s1^-1,
    s4*s2*s3^-1*s1^-1*s2*s3*s4^-1*s2^-1*s1*s2^-1*s3^-1*s1^-1*s2*s1^-1*s2*s3,
    s1^2*s3*s4^-1*s2^-2*s3^-1*s4*s1*s4*s2*s3^-1*s1^-1*s2*s3*s4^-1,
    s4*s3^-1*s2^-1*s1*s3*s2^-1*s4^-1*s3^-2*s2^-1*s4*s1^-1*s4^-1*s3*s2*s1*s3*s1^-1,
    s2^-2*s3^-1*s4*s1*s3*s2*s1^-1*s2*s3^-1*s2^-1*s4^2*s1*s3*s4*s1*s2*s1^2,
    s3^-1*s4*s3^-1*s2^-2*s3^-1*s4*s1*s3*s2*s1^-1*s2*s1^2*s2^-1*s1*s3^2*s2*s1^-1,
    s3*s2*s1^-1*s4^-2*s2*s3^2*s2*s1^-1*s4^-2*s1^2*s3*s4^-1*s3*s4^-1*s2*s3,
    s2^-1*s3^-1*s2^-1*s1*s2^-1*s4^-1*s2^-1*s1^-1*s4^-1*s3^-1*s2^-1*s3^-2*s2^-1*s3^-1*s2^-1*s1*s2^-1*s3^-1*s4^2*s1,
    s3^-1*s1^-1*s2*s1^-2*s3^-1*s2^-1*s3*s2*s1^-1*s2*s3^-1*s1^-1*s2*s3*s1*s3*s4*s1*s2*s4*s1,
    s3^-1*s1^-1*s2*s4*s3^-1*s1^-2*s2^-1*s1^-1*s4^-1*s3^-1*s1^-1*s4^-2*s3^-1*s2^-1*s3^-2*s1^-1*s2*s1^-2,
    s3^-1*s1^2*s3*s4^-1*s3*s1^2*s3*s4^-1*s3*s2*s1*s2^-1*s1^-1*s4^-1*s3^-1*s2^-1*s3^-1*s2^-1*s1^-1*s4^-1*s3^-1*s1^-1,
    s4^-1*s1^-1*s4^-1*s3*s2^2*s3*s4^-1*s1^2*s2^-2*s3^-1*s4*s2^-1*s3^-1*s4*s2^-1*s3^-1*s4*s3^-1*s1^-1*s2^-1*s1*s3^2*s2*s1^-1 ];
end, []);
Add(FakeProjectivePlaneGroups, rec(
  name := "Q(sqrt(-2)), p=3, T1={2I}",
  fieldGens:=[[s,Z],["r2","Z"]],
  csName := "(a=2,p=3,\\{2I\\})",
  k := "Q", ell := "Q(sqrt(-2))", p := 3, T1 := "{2I}",
  N := 1, numberOfFakePlanes := 1,
  presentation := H, matrix := subgens, field := F, form := form, conj := conj,
  fakePlanes := [ rec(name := "(a=2,p=3,\\{2I\\})", generators := GeneratorsOfGroup(H), index := 1, abInv := [ 2, 2, 2, 2, 3 ]) ] ));

# Q(sqrt(-2)), p=3, T1={2}   [(a=2,p=3,\{2\})]
f := FreeGroup("a", "b", "c");
a := f.1;
b := f.2;
c := f.3;
G := f / [
  (b*a)^3,
  (c^-1*b^-1*c^-1*a)^3,
  (a*b*c*a^-1*c*a)^3,
  c*a^-2*b^-1*c^-1*b*c*a^-1*b*c^-1*b^-1*a^-1,
  b*c*a^-1*c*a*b*c*a^-1*c*b^-1*c^-1*b^-1*a^-1*c,
  a*c^-1*b^-1*c*b^2*c*b*c*a*c^-1*b^-2*c^-1,
  a^-1*b^-1*c^-1*b^-1*c^-1*b^-2*c^-1*a^2*b*c*b*a*c*b^2*c,
  b^-1*a*c^-1*b^-2*c^-1*b^-1*c^-1*a*c^-1*a*b*a*c^-1*b^-1*c^-1*b^-2,
  b*a^-2*b^-1*c^-1*b^-1*c^-1*b^-2*c*a^-2*c*b^2*c*b*c,
  b^-2*c^-1*b*c*a^-2*c*b^-1*a*c^-1*b^-2*c^-1*b^-2*a*c^-1,
  b^3*c*b*c*b*a^3*b*c*a^-1*c*b^-1*a*c^-1*b^-2*c^-1,
  a^-1*b^-1*c^-1*b^-1*c^-1*b^-1*c*b*c*b*a*c*b*c*b^2*c*a^-1*b*c^-1,
  b^-1*c*b*c*b*c^-1*a^-1*c*b*c^-1*a*c^-1*b^-1*a*c^-1*b*c^-1*a*c^-1*b^-1*a^-1*b^-1*a*c^-1
];
mats := [
  # a  (AD in the source file)
  [ [ (2*s*Z^2-Z^2+s*Z-7*Z-s)/10, (-3*s*Z^2+2*Z^2-3*s*Z+8*Z-4*s-2)/20, (s*Z^2+2*Z^2+s*Z-2*s+2)/10 ],
    [ (-3*s*Z^2-3*s*Z-9*s)/5, (-2*s*Z^2+3*Z^2-5*s*Z+5*Z-7*s+8)/10, (s*Z^2-2*Z^2+3*s*Z-2*Z+2*s-6)/10 ],
    [ (3*s*Z^2+6*Z^2-9*s*Z-12*Z-18)/20, (3*s*Z^2-6*Z^2+3*s*Z-6*s-6)/10, (-Z^2+2*s*Z+Z-s+1)/5 ] ]*one,
  # b  (BD in the source file)
  [ [ (3*Z^2-s*Z+Z+3*s)/10, (Z^2-s*Z-5*Z+3*s+6)/20, (4*s*Z^2-Z^2+5*s*Z+Z+9*s+6)/30 ],
    [ (-s*Z^2+4*Z^2-s*Z-2*Z+2*s+10)/10, (-2*s*Z^2-Z^2-s*Z+Z+s-4)/10, (-s*Z^2-2*s*Z+2*Z+4)/10 ],
    [ (6*s*Z^2-3*Z^2+15*s*Z+3*Z+21*s+18)/20, (-3*s*Z^2-3*Z^2-4*s*Z+Z-s+4)/10, (s*Z^2-Z^2+s*Z-Z+3*s-3)/5 ] ]*one,
  # c  (CD in the source file)
  [ [ (s*Z^2+s*Z-2*Z)/2, 0, 0 ],
    [ 0, (-s*Z^2+Z^2-2*s*Z+Z-3*s+2)/2, 0 ],
    [ 0, 0, (-Z^2+s*Z+Z-s)/2 ] ]*one
];
Add(FakeProjectivePlaneGroups, rec(
  name := "Q(sqrt(-2)), p=3, T1={2}",
  fieldGens:=[[s,Z],["r2","Z"]],
  csName := "(a=2,p=3,\\{2\\})",
  k := "Q", ell := "Q(sqrt(-2))", p := 3, T1 := "{2}",
  N := 3, numberOfFakePlanes := 1,
  presentation := G, matrix := mats, field := F, form := form, conj := conj,
  fakePlanes := [
    rec(name := "(a=2,p=3,\\{2\\},D_3)",
        generators := List([a, c, b*a*b^-1, b*c*b^-1], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 3, abInv := [ 2, 2, 13 ]) ] ));
end, []);

#############################################################################
##  k = Q,  ell = Q(sqrt(-7)),  p = 2
##  Field generators: zeta^6 = -(zeta^5+zeta^4+zeta^3+zeta^2+zeta+1)
##  (conj: zeta -> zeta^6)
CallFuncList(function()
local x, F, t, tbar, conj, form, f, G, mats, H, subgens, one, zeta, a, b, c, d, z;
x := Indeterminate(Rationals, "x");
F := FieldExtension(Rationals, x^6+x^5+x^4+x^3+x^2+x+1);
one := One(F);
t := RootOfDefiningPolynomial(F);   # t = zeta
zeta := (t)*one;
tbar := (-t^5-t^4-t^3-t^2-t-1)*one;   # image of t under conj
conj := e -> ValuePol(ExtRepOfObj(e), tbar);
form := [ [ -zeta^5-zeta^4-zeta^3-zeta^2-1, 0, 0 ],
          [ 0, zeta^5+zeta^2, 0 ],
          [ 0, 0, zeta^4+zeta^3 ] ]*one;

# Q(sqrt(-7)), p=2, T1={}   [(a=7,p=2,\emptyset)]
f := FreeGroup("z", "b");
z := f.1;
b := f.2;
G := f / [
  z^7,
  (b^-2*z^1)^3,
  (b^2*z^-2*b^2*z^2)^3,
  (b^2*z^-2*b^2*z^4)^3,
  b^3*z^-2*b^-1*z^2*b^-2*z,
  b^3*z*b^3*z^3*b*z^2*b^-1*z^-1,
  b^3*z^2*b^2*z^-2*b^-1*z^-1*b^-3*z*b^-1*z^-1
];
mats := [
  # z  (ZZ in the source file)
  [ [ zeta, 0, 0 ],
    [ 0, zeta^2, 0 ],
    [ 0, 0, zeta^4 ] ]*one,
  # b  (BB in the source file)
  [ [ (-3*zeta^5-2*zeta^4+3*zeta^3+5*zeta^2+4*zeta)/7, (-2*zeta^5+8*zeta^4+2*zeta^3-6*zeta^2+5*zeta+7)/7, (-6*zeta^5+3*zeta^4+6*zeta^3+3*zeta^2+zeta+7)/7 ],
    [ (-8*zeta^5-4*zeta^4-9*zeta^3-2*zeta^2+3*zeta-1)/7, (-3*zeta^5+2*zeta^4-6*zeta^3+zeta^2-5*zeta-3)/7, (-2*zeta^5-8*zeta^4-4*zeta^3+3*zeta^2+6*zeta+5)/7 ],
    [ (-8*zeta^5+14*zeta^4-11*zeta^3+8*zeta^2-13*zeta+3)/14, (9*zeta^5+7*zeta^4+zeta^3+12*zeta^2+5*zeta+8)/7, (6*zeta^5+7*zeta^4+3*zeta^3+zeta^2+8*zeta+3)/7 ] ]*one
];
Add(FakeProjectivePlaneGroups, rec(
  name := "Q(sqrt(-7)), p=2, T1={}",
  #fieldGens:=[[zeta],["E(7)"]],
  fieldGens:=[[zeta+zeta^2-zeta^3+zeta^4-zeta^5-zeta^6,zeta+zeta^6],
    ["ER(-7)","EC(7)"]],
  csName := "(a=7,p=2,\\emptyset)",
  k := "Q", ell := "Q(sqrt(-7))", p := 2, T1 := "{}",
  N := 21, numberOfFakePlanes := 3,
  presentation := G, matrix := mats, field := F, form := form, conj := conj,
  fakePlanes := [
    rec(name := "(a=7,p=2,\\emptyset,D_3 2_7)",
        generators := List([b^3, (z*b*z^-1)^3, b*z*b^2*z^-2, z*b*z^3*b^-1], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 21, abInv := [ 2, 2, 2, 2 ]),
    rec(name := "(a=7,p=2,\\emptyset,7_{21})",
        generators := List([b, z*b^2*z, z^-2*b^2*z^3], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 21, abInv := [ 2, 2, 3, 7 ]),
    rec(name := "(a=7,p=2,\\emptyset,D_3 X_7)",
        generators := List([b^3, z*b^3*z, b*z^2*b^-1*z], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 21, abInv := [ 2, 7 ]) ] ));

# Q(sqrt(-7)), p=2, T1={7}   [(a=7,p=2,\{7\})]
f := FreeGroup("b", "z");
b := f.1;
z := f.2;
G := f / [
  z^7,
  b^3,
  (b^-1*z^1*b^-1*z^2)^3,
  (b*z^6*b*z^5*b^-1*z^1)^3,
  b*z^2*b^-1*z^6*b*z^6*b*z^2*b^-1*z^6*b*z^6*b*z^4
];
mats := [
  # b  (BB in the source file)
  [ [ (-4*zeta^5-8*zeta^4-5*zeta^3-2*zeta^2+zeta-3)/7, (-6*zeta^5-5*zeta^4+3*zeta^3-3*zeta^2-9*zeta-1)/7, (-2*zeta^5+3*zeta^4+zeta^3-8*zeta^2-3*zeta+2)/7 ],
    [ (zeta^5-5*zeta^4+3*zeta^3+4*zeta^2+5*zeta+6)/7, (5*zeta^5+3*zeta^4+zeta^3+6*zeta^2-3*zeta+2)/7, (-3*zeta^5-6*zeta^4-9*zeta^3-12*zeta^2-8*zeta-4)/7 ],
    [ (17*zeta^5-zeta^4+9*zeta^3+12*zeta^2+zeta+18)/14, (-3*zeta^5+zeta^4-2*zeta^3+2*zeta^2-8*zeta+3)/7, (-zeta^5+5*zeta^4+4*zeta^3-4*zeta^2+2*zeta+1)/7 ] ]*one,
  # z  (ZZ in the source file)
  [ [ zeta, 0, 0 ],
    [ 0, zeta^2, 0 ],
    [ 0, 0, zeta^4 ] ]*one
];
Add(FakeProjectivePlaneGroups, rec(
  name := "Q(sqrt(-7)), p=2, T1={7}",
  fieldGens:=[[zeta+zeta^2-zeta^3+zeta^4-zeta^5-zeta^6,zeta+zeta^6],
    ["ER(-7)","EC(7)"]],
  csName := "(a=7,p=2,\\{7\\})",
  k := "Q", ell := "Q(sqrt(-7))", p := 2, T1 := "{7}",
  N := 21, numberOfFakePlanes := 4,
  presentation := G, matrix := mats, field := F, form := form, conj := conj,
  fakePlanes := [
    rec(name := "(a=7,p=2,\\{7\\},D_3 2_7)",
        generators := List([z^2*b*z^-1*b^-1, b^-1*z^-1*b*z^-3, z^-1*b^-1*z^2*b, z^-2*b*z*b^-1], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 21, abInv := [ 2, 2, 2 ]),
    rec(name := "(a=7,p=2,\\{7\\},D_3 7_7)",
        generators := List([b^-1*z*b*z^-2, z^-2*b*z^2*b^-1, b*z^-1*b*z^2*b], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 21, abInv := [ 2, 7 ]),
    rec(name := "(a=7,p=2,\\{7\\},D_3 7'_7)",
        generators := List([z^2*b*z^2*b^-1, b^-1*z^-1*b*z^2, z^-2*b*z^-2*b^-1], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 21, abInv := [ 2, 2, 7 ]),
    rec(name := "(a=7,p=2,\\{7\\},7_{21})",
        generators := List([z*b^-1, b^-1*z*b*z*b, b^-1*z^3], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 21, abInv := [ 2, 2, 2, 3 ]) ] ));

# Q(sqrt(-7)), p=2, T1={3}   [(a=7,p=2,\{3\})]
f := FreeGroup("a", "b", "c");
a := f.1;
b := f.2;
c := f.3;
G := f / [
  a*b*c^-1*b*c^-1*a^2*b,
  c^-2*b*c^-1*a*b*a*b*a*b^-1*c*b,
  b^-1*a^-2*c*a^-1*b^-1*a^-1*c^-1*b*a^-1*b*a,
  (b^-2*a^-2)^3,
  b*c^-1*b*a*b*a*c^-1*b*a^-1*c*b^-1*c^-1,
  c*b^-1*c^2*a^2*b^2*a*c^-1*b*a^-1*b*a,
  b*a^-1*c*b^-1*a*b^-1*c*b*c*a^-1*b*a*c^-1*b*a^-1*b,
  a^-1*c*b^-1*c^2*b^-1*a*b^-1*c*a^-1*b^-1*c*b^-1*c^2*b*c^-1*b,
  a*c^-2*b*c^-1*a*b^-1*c*a^-1*c*b^-1*a*b^-1*c*b*a^2*b,
  b*a^-1*b^-1*a^-1*b^-1*c^-1*b^-1*a^-1*b^-1*a^-1*b^-1*c*b^-1*a^2*b*c^-1*b*a^-1*c^-1,
  c^-2*b*c^-1*a*b^-1*c*b^-2*a*c^-1*a^2*b*a^-1*c*a^-1*b^-1*a^-1*b^-1,
  (c^-1*b*c^-1*b*a*b^-1*a^-2)^3
];
mats := [
  # a  (AA in the source file)
  [ [ (4*zeta^5-4*zeta^4-10*zeta^3-14*zeta^2-9*zeta-2)/21, (20*zeta^5+25*zeta^4+15*zeta^3+4*zeta^2+27*zeta+14)/21, (-4*zeta^5+3*zeta^4-7*zeta^3-6*zeta^2-zeta-6)/21 ],
    [ (7*zeta^5-zeta^4+4*zeta^3+8*zeta^2+4*zeta-1)/21, (10*zeta^5-4*zeta^4+14*zeta^3+zeta^2+6*zeta+8)/21, (-15*zeta^5-11*zeta^4+5*zeta^3+12*zeta^2+10*zeta-1)/21 ],
    [ (-23*zeta^5-7*zeta^4-29*zeta^3-12*zeta^2-19*zeta-22)/21, (-4*zeta^5+4*zeta^4+3*zeta^3-5*zeta-5)/21, (-14*zeta^5-13*zeta^4-4*zeta^3-8*zeta^2-18*zeta-6)/21 ] ]*one,
  # b  (BB in the source file)
  [ [ (-2*zeta^5-zeta^4-zeta^3+zeta^2+1)/3, (-4*zeta^5-2*zeta^4-2*zeta^2-3*zeta-1)/3, (-zeta^5-zeta^3-3*zeta^2-zeta)/3 ],
    [ (zeta^5-zeta^4+zeta^3+2*zeta^2+zeta+2)/3, (zeta^5+2*zeta^4-zeta^3+zeta^2+2)/3, (-2*zeta^4-4*zeta^3-3*zeta^2-2*zeta-1)/3 ],
    [ (8*zeta^5+4*zeta^4+5*zeta^3+6*zeta^2+zeta+7)/6, (-zeta^5+zeta^4-2*zeta+1)/3, (zeta^5+2*zeta^4+2*zeta^3+zeta^2+3*zeta+3)/3 ] ]*one,
  # c  (CC in the source file)
  [ [ (-zeta^5+4*zeta^4+8*zeta^3+4*zeta^2+6*zeta)/7, (9*zeta^5+zeta^4-3*zeta^3+4*zeta^2+8*zeta-5)/7, (zeta^5-7*zeta^4-3*zeta^3+6*zeta^2+6*zeta-3)/7 ],
    [ (-3*zeta^5+5*zeta^4-4*zeta^3-2*zeta^2-10*zeta-7)/7, (-8*zeta^5-4*zeta^4-9*zeta^3-2*zeta^2-4*zeta-8)/7, (3*zeta^5+7*zeta^4+12*zeta^3+11*zeta^2+4*zeta-2)/7 ],
    [ (-9*zeta^5-6*zeta^4-5*zeta^3-13*zeta^2-2*zeta-14)/7, (4*zeta^5+2*zeta^4+zeta^3-6*zeta^2+9*zeta-3)/7, (9*zeta^5+7*zeta^4+zeta^3+5*zeta^2+5*zeta+1)/7 ] ]*one
];
Add(FakeProjectivePlaneGroups, rec(
  name := "Q(sqrt(-7)), p=2, T1={3}",
  fieldGens:=[[zeta+zeta^2-zeta^3+zeta^4-zeta^5-zeta^6,zeta+zeta^6],
    ["ER(-7)","EC(7)"]],
  csName := "(a=7,p=2,\\{3\\})",
  k := "Q", ell := "Q(sqrt(-7))", p := 2, T1 := "{3}",
  N := 3, numberOfFakePlanes := 2,
  presentation := G, matrix := mats, field := F, form := form, conj := conj,
  fakePlanes := [
    rec(name := "(a=7,p=2,\\{3\\},D_3)",
        generators := List([a, b*c*b^-1, b^-1*a*b], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 3, abInv := [ 2, 4, 7 ]),
    rec(name := "(a=7,p=2,\\{3\\},3_3)",
        generators := List([a^3, a*b*a^-1, a^-1*c*a^-1], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 3, abInv := [ 2, 2, 3, 4 ]) ] ));

# Q(sqrt(-7)), p=2, T1={3,7}   [(a=7,p=2,\{3,7\})]
f := FreeGroup("a", "b");
a := f.1;
b := f.2;
G := f / [
  (a^-1*b*a*b^3)^3,
  (b*a^-1*b^-1*a^-1*b^2*a*b^-2*a^-2*b*a)^3,
  a^-1*b^2*a^-1*b*a^-1*b^-1*a^-2*b*a*b*a*b*a*b^-2,
  a*b*a^-1*b^-1*a^2*b^2*a^-1*b^-1*a*b^-1*a^-1*b^-1*a^2*b*a,
  b^-2*a^-2*b*a^-1*b^-1*a^-1*b^-2*a*b^2*a^-1*b*a^-1*b^-1*a^-1*b^-1,
  b^-1*a^-1*b^2*a^-1*b*a*b*a^-2*b^-1*a^-1*b^-2*a*b^2*a^-1*b^-1*a^-1*b^2*a^-1,
  a*b^2*a^-1*b^-1*a^-1*b^2*a^-1*b*a^-1*b*a^-1*b^-3*a^-2*b*a*b*a^-1*b^-1,
  a^-1*b^-1*a^2*b^2*a^-1*b^-2*a^2*b*a^-1*b^-1*a^2*b^3*a*b^-1*a^2*b^2,
  a^-1*b^-3*a^-1*b^-2*a*b^2*a^-1*b^-1*a^-3*b^-3*a^-2*b*a*b^-1*a^-2*b,
  b^-1*a*b^-1*a^-1*b^-1*a^2*b^2*a^-1*b^-2*a^2*b^2*a^-1*b^-1*a^-1*b^2*a*b*a*b^-1*a,
  a*b*a^-1*b^-1*a^2*b^3*a^-2*b^2*a*b*a*b^-1*a*b^-1*a*b^-2*a^-2*b^-1*a^-2*b^-1*a^-1*b^2*a^-1*b,
  a*b^2*a^-1*b*a^-1*b*a^-1*b^-1*a^-1*b^-2*a^2*b^-1*a^-1*b^-1*a^2*b^-1*a^2*b^2*a^-1*b*a^-1*b*a^-1*b^-1*a^-1*b^-5*a^-2*b*a^2
];
mats := [
  # a  (AA in the source file)
  [ [ (12*zeta^5+3*zeta^4-6*zeta^3-8*zeta^2-10*zeta+2)/21, (18*zeta^5+8*zeta^4-9*zeta^3+9*zeta^2+20*zeta-11)/21, (-22*zeta^5-9*zeta^4-3*zeta^3-4*zeta^2-5*zeta+8)/21 ],
    [ (-10*zeta^5-6*zeta^4-23*zeta^3+2*zeta^2-zeta+3)/21, (6*zeta^5-2*zeta^4+18*zeta^3-4*zeta^2+9*zeta+8)/21, (9*zeta^5+18*zeta^4+27*zeta^3+29*zeta^2+17*zeta-2)/21 ],
    [ (-22*zeta^5-9*zeta^4-10*zeta^3-25*zeta^2-5*zeta-34)/21, (23*zeta^5+25*zeta^4+13*zeta^3+22*zeta^2+17*zeta+26)/21, (-18*zeta^5-22*zeta^4-12*zeta^3-9*zeta^2-20*zeta-10)/21 ] ]*one,
  # b  (BB in the source file)
  [ [ (zeta^5-4*zeta^4-4*zeta^3-3*zeta^2+zeta-1)/3, (-4*zeta^5-4*zeta^4-2*zeta^2-5*zeta+1)/3, (6*zeta^5+9*zeta^4+5*zeta^3+4*zeta^2+7*zeta+4)/3 ],
    [ (-zeta^5+2*zeta^4+6*zeta^3+3*zeta^2+5*zeta-1)/3, (4*zeta^5+zeta^4+5*zeta^3+5*zeta^2+3)/3, (-2*zeta^4-4*zeta^3-5*zeta^2-4*zeta+1)/3 ],
    [ (10*zeta^5+4*zeta^4+7*zeta^3+8*zeta^2+5*zeta+15)/6, (-6*zeta^5-3*zeta^4-7*zeta^3-zeta^2-4*zeta-7)/3, (-5*zeta^5-zeta^3-5*zeta^2-4*zeta-2)/3 ] ]*one
];
Add(FakeProjectivePlaneGroups, rec(
  name := "Q(sqrt(-7)), p=2, T1={3,7}",
  fieldGens:=[[zeta+zeta^2-zeta^3+zeta^4-zeta^5-zeta^6,zeta+zeta^6],
    ["ER(-7)","EC(7)"]],
  csName := "(a=7,p=2,\\{3,7\\})",
  k := "Q", ell := "Q(sqrt(-7))", p := 2, T1 := "{3,7}",
  N := 3, numberOfFakePlanes := 2,
  presentation := G, matrix := mats, field := F, form := form, conj := conj,
  fakePlanes := [
    rec(name := "(a=7,p=2,\\{3,7\\},D_3)",
        generators := List([a, b^3, b^-1*a*b], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 3, abInv := [ 4, 7 ]),
    rec(name := "(a=7,p=2,\\{3,7\\},3_3)",
        generators := List([a, b*a*b, b^-1*a*b^-1], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 3, abInv := [ 2, 3, 4 ]) ] ));

# Q(sqrt(-7)), p=2, T1={5}   [(a=7,p=2,\{5\})]
f := FreeGroup("a", "b");
a := f.1;
b := f.2;
G := f / [
  b^-1*a^-3*b^2*a*b^3*a^-2*b^2*a*b^3*a^2*b*a^-1*b^2*a*b*a*b*a^-2*b^2*a*b^3*a*b^-1,
  b*a*b*a^-1*b^2*a*b*a*b*a^-2*b^2*a*b^2*a^-1*b^-2*a*b^-1*a^-2*b^-3*a^-1*b^-2*a^4*b*a^-1*b^2*a*b,
  a^-1*b^-2*a*b^-1*a^-1*b^-2*a^-1*b^-2*a*b^-1*a^-1*b^-2*a^-1*b^-2*a*b^-1*a^-1*b^-1*a^-3*b^2*a*b^3*a^2*b*a^-1*b^2*a*b*a*b*a*b^-1*a^-1*b^-1,
  a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b^-1*a^-1*b^-1*a*b*a^-1*b^2*a*b^2*a^-3*b^2*a*b^3*a^2*b*a^-1*b^2*a*b*a*b^-2*a^2*b^2,
  a^-1*b^2*a*b^3*a*b^-2*a^2*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b^-1*a^-1*b^-2*a^-3*b^2*a*b^3*a^2*b*a^-1*b^2*a*b*a*b,
  a*b^-3*a^-1*b^-2*a^2*b^2*a^-1*b^-3*a^-1*b^-2*a*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b^-1*a^-1*b^-2*a*b^-1*a^-1*b^-1*a*b*a^-1*b^-1*a^-2*b^-3*a^-1*b^-2*a,
  b^-1*a*b*a^-2*b^2*a*b^3*a*b^-2*a^-1*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b*a^-2*b^2*a*b^3*a*b^-2*a^-1*b^-3*a^-1*b^-2*a^3*b^2*a^-1*b^-1,
  a*b^-2*a^2*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-2*a^-1*b*a^-1*b^-3*a^-1*b^-2*a^2*b^-3*a^-1*b^-2*a^-1*b^2*a*b^3*a^2*b*a^-1*b^2*a*b*a*b,
  a*b^-1*a^-3*b^2*a*b^3*a^-2*b^2*a*b^3*a*b^-1*a*b*a*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-2*a^-1*b^-1*a^-1*b^-2*a*b^-1*a^-1*b^-2*a^-1*b^-2*a*b^-1*a^-1*b^-1,
  b^2*a^-1*b^-1*a^-1*b^-1*a^-1*b^-2*a*b^-1*a^-2*b^-3*a^-1*b^-2*a^3*b^2*a*b^3*a^-2*b^2*a*b^3*a^-1*b^2*a*b^3*a^-2*b^2*a*b^3*a*b^-1*a*b*a^-1,
  b^-2*a^-1*b^-2*a*b^-1*a^-1*b*a^-1*b^-3*a^-1*b^-2*a^2*b^-3*a^-3*b^2*a^-2*b^2*a^-2*b^2*a*b^3*a^-2*b^2*a*b^3*a*b^-4*a^-1*b^-2*a*b^-1*a^-1*b^-1,
  a^-2*b^2*a*b^3*a^2*b*a^-1*b^2*a^2*b*a^-1*b^2*a*b^2*a*b*a^-1*b^2*a*b*a*b*a^-1*b^-1*a^-1*b^-1*a*b*a^-1*b^2*a*b^2*a*b*a^-1*b^2*a*b*a*b*a^-1*b^-1*a^-1*b^-1*a^-1,
  b^-2*a^-1*b^-2*a^2*b^-2*a*b^-1*a^-1*b*a*b*a*b^-1*a^-1*b*a^-1*b^-3*a^-1*b^-2*a^2*b^-3*a^-1*b^-2*a^2*b*a*b*a^-1*b^2*a*b*a*b^2*a^-2*b^2*a*b^3*a*b^-2*a^-1*b^-1,
  a^2*b^3*a^-2*b^2*a*b^3*a*b^-1*a*b*a^-1*b^2*a*b^2*a^-1*b^-2*a*b*a^-2*b^2*a*b^3*a*b^-2*a^-5*b^2*a*b^3*a^2*b*a^-1*b^2*a*b*a*b,
  b^-1*a^2*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b^-1*a^-1*b^-1*a*b^2*a^-2*b^2*a*b^3*a*b^-2*a^-2*b^4*a^-1*b^-3*a^-1*b^-2*a^2*b^-2*a^-1*b*a*b*a^-1*b^2*a*b*a,
  a*b*a^-2*b^2*a*b^3*a*b^-2*a^-2*b^2*a^-2*b^2*a*b^3*a*b^-2*a*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b*a^-1*b^-2*a*b^-1*a^-2*b^-3*a^-1*b^-2*a^3*b*a*b,
  b^-1*a*b^-1*a^-2*b^-3*a^-1*b^-2*a^3*b^-2*a^-3*b^2*a*b^3*a*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-2*a^-1*b*a*b*a^-1*b^2*a*b^2*a*b*a^-1*b^2*a*b*a*b*a^-1*b^-1*a^-1*b^-1,
  a^-2*b^2*a*b^3*a^-2*b^2*a*b^3*a*b^-1*a*b*a^-1*b^2*a*b^2*a^-1*b^-1*a^-1*b^-2*a*b^-1*a^-2*b^-3*a^-1*b^-2*a^4*b^2*a^-2*b^2*a*b^3*a*b^-2*a^-2*b^2,
  a*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b^2*a^-2*b^2*a*b^3*a^2*b*a^-1*b*a^-1*b^-2*a*b^-1*a^-2*b^-3*a^-1*b^-2*a^3*b*a^-1*b^-3*a^-1*b^-2*a^2*b^-3*a^-1*b^-2*a^3,
  b*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b^-1*a^-1*b^-2*a*b^-1*a^-1*b^-1*a*b*a^-4*b^2*a*b^3*a^-2*b^2*a*b^3*a*b^-1*a*b*a^-1*b^-1*a^-1*b^-1*a^-3*b^2*a*b^3*a^2*b*a^-1*b^2*a*b^-1*a,
  b^-1*a^-1*b^-1*a*b^2*a^-2*b^2*a*b^3*a*b^-2*a^-2*b^2*a^-1*b^-1*a^-1*b*a*b*a^-1*b^2*a*b*a*b*a^-2*b^2*a*b^3*a*b^-1*a^-3*b^2*a*b^3*a^-2*b^2*a*b^3*a*b^-1*a*b*a^-1,
  a^-1*b^2*a*b^3*a^-2*b^2*a*b^3*a*b^-1*a*b*a^-1*b^-1*a^-1*b^-2*a^2*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-2*a^-2*b^-3*a^-1*b^-2*a^3*b*a*b*a^-1*b^2*a*b^2*a^-1*b^-2*a*b^-1*a^-2,
  a^-3*b^2*a*b^3*a^2*b*a^-1*b^2*a*b*a*b^-2*a^-1*b^-2*a*b^-1*a^-1*b^-1*a^-1*b^-2*a*b*a^-2*b^2*a*b^3*a*b^-2*a^-2*b^2*a*b*a^-1*b*a*b*a^-1*b^2*a*b^2*a*b*a^-1*b^2*a*b,
  a^-1*b*a*b*a^-1*b^2*a*b*a*b*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b^-1*a^-1*b^-2*a*b^-1*a^-1*b^-1*a*b^-2*a^-1*b^-2*a^3*b^2*a^-1*b^-2*a*b*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b^-1*a^-1*b^-2*a*b^-1*a^-1*b^-1*a*b*a^-1,
  b^-1*a^-1*b*a^-1*b^-3*a^-1*b^-2*a^3*b^-2*a^-1*b^2*a*b^3*a^-2*b^2*a*b^3*a^2*b*a*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b^2*a^2*b*a^-1*b^2*a*b^2*a*b*a^-1*b^2*a*b*a*b*a^-1,
  a^-2*b^2*a*b^3*a^2*b*a^-1*b^2*a*b*a*b*a*b^-2*a^2*b^-2*a^2*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b^2*a*b^2*a*b*a^-1*b^2*a*b*a*b*a^-1*b^-1*a^-2*b^-3*a^-1*b^-2*a^2*b^-3*a^-1*b^-2,
  b^-2*a^-1*b^-2*a^3*b^2*a^-1*b^-2*a*b^-1*a^-2*b^-3*a^-1*b^-2*a^2*b^-2*a*b*a^-2*b^2*a*b^3*a*b^-2*a^-2*b^-2*a^2*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b^2*a*b^2*a*b*a^-1*b^2*a*b*a,
  a^2*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b^-3*a^-1*b^-2*a*b^-1*a^-1*b*a^-1*b^-3*a^-1*b^-2*a^3*b^-2*a^-1*b^2*a*b^3*a^-2*b^2*a*b^3*a^2*b*a^-2*b^2*a*b^3*a^-2*b^2*a*b^3*a^2*b,
  a^-2*b^2*a*b^3*a*b^-2*a*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b*a*b*a^-1*b^2*a*b^2*a*b*a^-1*b^2*a*b*a*b*a^-1*b^-1*a^-1*b^-2*a*b*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b^-1*a^-1*b^-2*a*b^-1*a^-1*b^-1*a*b*a^-1*b^2,
  b^-1*a^-3*b^2*a*b^3*a^-2*b^2*a*b^3*a*b^-1*a*b*a^2*b^3*a^-2*b^2*a*b^3*a*b^-1*a*b*a^-1*b^2*a*b^4*a^-1*b^-3*a^-1*b^-2*a^3*b^-2*a^2*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1,
  a*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b^2*a*b*a*b*a^-1*b^2*a*b^3*a*b^-1*a^-1*b^-1*a^-1*b^-2*a*b^-1*a^-1*b^-2*a^-1*b^-2*a*b^-1*a^-1*b^-1*a*b*a^-1*b^-1*a^-1*b^-1*a^-1*b^-2*a*b^-1*a^-2*b^-3*a^-1*b^-2*a^4*b^-1*a^-1*b^-2*a,
  a^-2*b^2*a*b^2*a^-1*b^-1*a^-1*b^-2*a*b^-1*a^-1*b^-2*a^-1*b^-3*a^-1*b^-2*a^-3*b^2*a*b^3*a^2*b*a^-1*b^2*a*b*a*b*a^2*b^2*a*b*a^-1*b^2*a*b*a*b*a*b^-2*a^2*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b^2,
  a^-4*b^2*a*b^3*a^2*b*a^-1*b^2*a*b*a*b*a*b^-2*a^-1*b^2*a*b^3*a^2*b*a^-1*b^2*a*b*a*b*a*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-2*a^-1*b^-1*a^-1*b^-2*a*b^-1*a^-1*b^-1*a*b*a^-2*b^2*a*b^3*a*b^-2,
  a^-1*b^-1*a^-2*b^-3*a^-1*b^-2*a^2*b^-3*a^-1*b^-2*a*b^2*a*b^3*a^-2*b^2*a*b^3*a^2*b*a^-3*b^2*a*b^3*a^-2*b^2*a*b^3*a*b^-1*a*b*a^-1*b^-1*a^-1*b^-1*a*b*a^-1*b^2*a*b^2*a*b*a^-1*b^2*a*b*a*b,
  b*a^-2*b^2*a*b^3*a*b^-1*a*b*a^-1*b^2*a*b^2*a^-3*b^2*a*b^3*a^2*b*a^-1*b^-1*a^-1*b^-2*a^2*b^-3*a^-1*b^-2*a^3*b^3*a*b^-1*a^-1*b^-1*a^-1*b^-2*a*b^-1*a^-1*b^-2*a^-1*b^-2*a*b^-1*a^-1*b^-1*a*b*a^-2*b^2*a*b^3*a,
  a^-1*b^2*a*b^3*a^2*b*a^-1*b^2*a*b*a*b*a^-1*b^2*a^-1*b^-1*a^-1*b^-1*a^-1*b^-2*a*b^-1*a^-2*b^-3*a^-1*b^-2*a^4*b^2*a^-1*b^-3*a^-1*b^-2*a*b^-3*a^-1*b^-2*a*b^-1*a^-1*b*a^-1*b^-3*a^-1*b^-2*a^2*b^-3*a^-1*b^-2*a^2*b^-2,
  b^-2*a^2*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b^2*a*b^2*a^-1*b^-2*a*b*a^-2*b^2*a*b^3*a*b^-2*a^-4*b^2*a*b^3*a*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b^-3*a^-1*b^-2*a^2*b*a^-2*b^2*a*b^3*a*b^-2,
  a^2*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-2*a^-1*b^-1*a^-1*b^-2*a*b^-1*a^-1*b^-1*a*b*a^-1*b^-1*a^-1*b^-1*a^-1*b^-2*a*b^-1*a^-2*b^-3*a^-1*b^-2*a^3*b^-1*a^-1*b^-2*a*b^-1*a^-1*b^-1*a^2*b^-1*a^-1*b*a*b*a^-1*b^2*a*b*a*b*a^-2*b^2*a*b^3*a*b^-1*a^-1*b^-1*a^-1*b^-2*a,
  b^2*a*b^3*a^-2*b^2*a*b^3*a^2*b*a^2*b^-2*a^2*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b^2*a^-2*b^2*a*b^2*a^-1*b*a*b*a^-1*b^2*a*b*a*b*a^-2*b^2*a*b^3*a*b^-1*a^-1*b*a^-1*b^-3*a^-1*b^-2*a^2*b^-3*a^-1*b^-2*a,
  b^2*a^-1*b^-1*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b^-1*a^-1*b^-2*a*b^-1*a^-1*b^-4*a^-3*b^2*a*b^3*a*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b^-1*a^-1*b^-1*a^-1*b^-2*a*b^-1*a^-2*b^-3*a^-1*b^-2*a^5*b*a^-2*b^2*a*b^3*a*b^-2*a^-2,
  b*a^-1*b^-3*a^-1*b^-2*a^2*b^-3*a^-1*b^-2*a*b^-1*a^-1*b*a*b*a^-1*b^2*a*b*a*b*a^-2*b^2*a*b^3*a*b^-1*a*b*a^-2*b^2*a*b^3*a*b^-2*a^-2*b^2*a^-3*b^2*a*b^3*a*b^-2*a*b*a^-1*b^2*a*b^2*a*b*a^-1*b^2*a*b*a*b*a^-1*b^-1*a^-1,
  a^-1*b^2*a*b^3*a^-2*b^2*a*b^3*a^2*b*a^-1*b^-1*a^-1*b^-2*a*b^-1*a^-1*b*a*b^3*a*b^2*a*b*a^-1*b^2*a*b*a*b*a*b^-2*a^2*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b^2*a^-2*b^2*a*b*a^-1*b^-1*a^-1*b^-2*a*b^-1*a^-1*b^-2*a^-1*b^-2*a*b^-1*a^-1*b^-1*a*b^-1,
  a^2*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b^2*a^-2*b^2*a*b^3*a^3*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b^2*a*b^-2*a^-1*b^-2*a*b^-1*a^-1*b^-1*a^2*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b^2*a*b*a*b*a^-1*b^2*a*b^2*a^-1*b^-2*a*b^-1*a^-1*b^-2,
  a*b*a^-2*b^2*a*b^3*a*b^-2*a^-1*b^-1*a^-1*b^-1*a^-1*b^-2*a*b^-1*a^-1*b^-2*a^-3*b^2*a*b^3*a^-1*b^2*a^-1*b^-1*a^-1*b^-1*a^-1*b^-2*a*b^-1*a^-2*b^-3*a^-1*b^-2*a^4*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-4*b^2*a*b^3*a^2*b*a^-1*b^2*a*b*a*b,
  a^-2*b^2*a^-2*b^2*a*b^3*a^-2*b^2*a*b^3*a*b^-1*a*b*a*b^-1*a^-1*b^-1*a^-1*b^-2*a*b^-1*a^-1*b^-1*a*b*a*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b^-3*a^-1*b^-2*a*b^-1*a^-1*b^-1*a^-1*b^-2*a*b*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b^-1*a^-1*b^-2*a*b^-1*a^-1*b^-1*a*b*a^-1*b^-1*a^-1*b^-2,
  b^2*a*b*a^-1*b^2*a*b*a*b*a*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-2*a^-1*b*a*b*a^-1*b^2*a*b*a*b*a^-1*b^-3*a^-1*b^-2*a^-1*b^2*a*b^3*a*b^-2*a^-6*b^2*a*b^3*a^2*b*a^-1*b^2*a*b*a*b*a*b^-3*a^-1*b^-2*a^-1*b^-3*a^-1*b^-2*a^3,
  b*a^-1*b^-3*a^-1*b^-2*a^2*b^-3*a^-1*b^-2*a^2*b^2*a^-2*b^2*a*b^3*a^-2*b^2*a*b^3*a*b^-1*a*b*a*b^-2*a^3*b^3*a^-2*b^2*a*b^3*a*b^-1*a*b*a^-1*b^2*a*b^4*a*b*a*b^-1*a^-1*b*a^-1*b^-3*a^-1*b^-2*a^2*b^-3*a^-1*b^-2*a^2,
  a^-1*b^2*a*b^3*a^-2*b^2*a*b^3*a^2*b*a^-1*b^-1*a^-1*b^-2*a*b^-1*a^-1*b*a^-1*b^-3*a^-1*b^-2*a^2*b^-3*a*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b^2*a*b^-2*a^-1*b^-2*a*b^-1*a^-1*b*a*b^3*a*b^3*a^-2*b^2*a*b^3*a*b^-1*a*b*a^-1*b^2*a*b^2*a^-1*b^-2*a*b^-1,
  a^-1*b^2*a*b^3*a^-2*b^2*a*b^3*a^2*b*a^2*b^2*a^-1*b^-3*a^-1*b^-2*a^3*b*a^-2*b^2*a*b^3*a*b^-2*a^-5*b^2*a*b^3*a^-2*b^2*a*b^3*a*b^-1*a*b*a^-1*b^-1*a^-1*b^-1*a^-1*b^-2*a*b*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b^-1*a^-1*b^-2*a*b^-1*a^-1*b^-1*a*b*a^-1*b^-1*a^-1*b^-2,
  b^-2*a*b*a^-2*b^2*a*b^3*a*b^-2*a^-2*b^2*a^-1*b^-1*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b^-1*a^-1*b^-2*a*b^-1*a^-1*b^-1*a*b^-1*a^-1*b*a^-1*b^-3*a^-1*b^-2*a^2*b^-3*a^-1*b^-2*a^5*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b^-3*a^-3*b^2*a*b^3*a*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-1,
  b^-1*a*b*a^-1*b^-1*a^-1*b^-1*a^-1*b^-2*a*b^-1*a^-3*b^2*a*b^3*a^-2*b^2*a*b^3*a*b^-1*a*b*a^-1*b^-1*a^-1*b^-2*a*b^2*a^-1*b^-3*a^-1*b^-2*a^2*b^-1*a^-1*b*a*b*a^-1*b^2*a*b^2*a*b*a^-1*b^2*a*b*a*b^2*a*b*a^-2*b^2*a*b^3*a*b^-2*a^-5*b^2*a*b^3*a^-2*b^2*a*b^3*a
];
mats := [
  # a  (AA in the source file)
  [ [ (6*zeta^5+2*zeta^4+4*zeta^3+4*zeta^2-zeta)/5, (-2*zeta^5-4*zeta^4+2*zeta^3-4*zeta)/5, (-zeta^5-zeta^4+3*zeta^3+2*zeta^2-4*zeta-3)/5 ],
    [ (-2*zeta^5-4*zeta^4-4*zeta^3-8*zeta^2-2*zeta-4)/5, (-4*zeta^5+2*zeta^3-5*zeta^2-2*zeta-4)/5, (-2*zeta^5-2*zeta^4-4*zeta^3-6*zeta^2-6*zeta-2)/5 ],
    [ (5*zeta^5-zeta^4+2*zeta^3+2*zeta^2+2*zeta+5)/5, (4*zeta^5-4*zeta^4+2*zeta^3+2*zeta^2)/5, (-2*zeta^5-7*zeta^4-6*zeta^3-4*zeta^2-2*zeta-6)/5 ] ]*one,
  # b  (BB in the source file)
  [ [ (6*zeta^5-3*zeta^4-6*zeta^3-3*zeta^2-zeta)/7, (-2*zeta^5-7*zeta^4-zeta^3-5*zeta^2-5*zeta-1)/7, (7*zeta^5+5*zeta^4+zeta^3+2*zeta^2+8*zeta+5)/7 ],
    [ (zeta^5+6*zeta^4+8*zeta^3+7*zeta^2+3*zeta+3)/7, (6*zeta^5+3*zeta^4+12*zeta^3+5*zeta^2+3*zeta+6)/7, (zeta^5-4*zeta^4-zeta^3-4*zeta^2-6*zeta)/7 ],
    [ (5*zeta^5-zeta^4+3*zeta^3-4*zeta^2-zeta+12)/14, (-8*zeta^5-zeta^4-7*zeta^3-5*zeta^2-2*zeta-5)/7, (-12*zeta^5-7*zeta^4-6*zeta^3-9*zeta^2-9*zeta-6)/7 ] ]*one
];
Add(FakeProjectivePlaneGroups, rec(
  name := "Q(sqrt(-7)), p=2, T1={5}",
  fieldGens:=[[zeta+zeta^2-zeta^3+zeta^4-zeta^5-zeta^6,zeta+zeta^6],
    ["ER(-7)","EC(7)"]],
  csName := "(a=7,p=2,\\{5\\})",
  k := "Q", ell := "Q(sqrt(-7))", p := 2, T1 := "{5}",
  N := 1, numberOfFakePlanes := 1,
  presentation := G, matrix := mats, field := F, form := form, conj := conj,
  fakePlanes := [
    rec(name := "(a=7,p=2,\\{5\\})",
        generators := List([a, b], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 1, abInv := [ 2, 2, 9 ]) ] ));

# Q(sqrt(-7)), p=2, T1={5,7}   [(a=7,p=2,\{5,7\})]
f := FreeGroup("a", "b", "d");
a := f.1;
b := f.2;
d := f.3;
G := f / [
  a^-1*d*b^-1*d^2*a^-1*d*a^-1*d*b^-1*a*d^-1*b*d^-1*b*d^-1*a*d^-1*a*d^-1,
  d^-1*a*d^-1*b*d*b^-1*d*a^-1*d*b*a*b*a^-2*b^-1*d^-1*a*d^-1*b*d^-1*a^-1,
  d^-1*b*d^-1*a^-2*b^-1*d^-1*a*d^-1*b*d^-1*a^-1*d*b*d^-1*a^-2*b^-1*d^-1*a*d^-1*b*d^-1,
  d^-1*a*d^-1*b*d*a^-1*d*a^-1*d*a^3*b^-1*d*a^-1*d*b*a^-1*d^-1*a*d^-1*a*d^-2*b*d^-1,
  a^-1*b^-1*d^-1*a*d^-1*b*d^-2*b*d^-1*a*d*b^-1*d*a^-1*d*b*a^2*b^-1*a^2*b^-1*d*a^-1*d*b,
  d^-1*a*b^-1*d*a^-1*d*b*a*b^-1*a*b*a^-2*b^-1*d^-1*a*d^-1*b*d^-1*b*a^-2*b^-1*d^-1*a*d^-1*b,
  d^-1*a*d^-1*a*b^-1*d*a^-1*d*b*a*d^-1*a^-1*b*a^-2*b^-1*d^-1*a*d^-1*b*d^-1*a^-1*b*a^2*b^-1*a^-1,
  b*a^3*b^-1*d*a^-1*d*b*a^2*d^-1*b^-1*d*a^-1*d*b*a^-2*b^-1*d^-1*a*d^-1*b*d^-2*b*d^-1,
  d*a^3*b^-1*d*a^-1*d*b*a^2*d^-1*a^-1*d*a^-1*d*b^-1*d^3*b^-1*d*a^-1*d*b*a^2*d*a^-1,
  b*d^-1*a*d^-1*a*d^-2*b*d^-1*a*d^-1*b*d^-1*b*d^-1*a*d^-1*a*d^-2*b*d^-1*a*d^-1*b*d^-1*a*d^-1*b*d^-1,
  d*a^-1*d*a*b*a^-2*b^-1*d^-1*a*d^-1*b*a^-1*d*a^-1*d*b^-1*d^-1*b*d^-1*a*d^-1*a*d*b^-1*d*a^-1*d*b*a,
  a*b^-1*d*a^-1*d*b*a*b^-1*a^-1*d*b^-1*d^-1*b*a*b^-1*d^-1*a*d^-1*b*a^-3*b^-1*d*b*d^-1*a*d^-1*a*d^-1,
  b^-1*d^-1*a*d^-1*b*d^-2*b*d^-1*a*d^-1*a*d*b^-1*d*a^-1*d*b*a^2*d*a^-2*b^-1*d^-1*a*d^-1*b*a^-3,
  b^-1*d^-1*a*d^-1*b*a^-2*b^-1*d^-1*a*d^-1*b*a^-2*b^-1*d^-1*a*d^-1*b*a^-3*d^-1*a*d^-1*a*b^-1*d*a^-1*d*b*a,
  b^-1*a^-1*d^-1*a*d^-1*b*d*b^-1*d^2*b^-1*d*a^-1*d*b*a^3*b^-1*d^-1*a*d^-1*b*d^-1*b^-1*a*b^-1*d*a^-1*d*b*a,
  b^-1*d*a^-1*d*a*d^-1*a*d*b^-1*d*a^-1*d*b*a^2*d*a^-2*d^-1*a^-2*b^-1*d^-1*a*d^-1*b*d^-2*a^-1*d*b^-1*d,
  d^-1*a^-2*b^-1*d^-1*a*d^-1*b*d^-2*a*b^-1*d*a^-1*d*b*a*b^-2*d^-1*a*d^-1*b*d^-1*b^-1*a*b^-1*d*a^-1*d*b*a,
  a^-1*d^4*b^-1*d*a^-1*d*b*a^2*d*a^-1*d*b^-1*d^-1*b*a*b^-1*d^-1*a*d^-1*b*a^-3*d^-1*a*d^-1*a*b^-1*d,
  a*b*a^-1*b^-1*d^-1*a*d^-1*b*a^-1*b*a^-2*b^-1*d^-1*a*d^-1*b*d^-1*a^-1*b*d^-1*a*d^-1*b*d^-1*b*d^-1*a*d^-1*a*d^-2*b,
  b*a^-1*b^-1*d^-1*a*d^-1*b*a^-1*d*a^-3*b^-1*d^-1*a*d^-1*b*d^-2*b*d^-1*a*b*a^-1*b^-1*d^-1*a*d^-1*b*a^-1*d*a^-1*d,
  a^2*b^-1*d*a^-1*d*b*a*b^-1*d^-1*a*d^-1*b*d*b^-1*d*a^-1*d*b*a^-1*b^-1*d^2*a^-1*d*a^-1*d*b^-1*d*b^-1*d*a^-1*d*b^-1,
  a*d*a^-2*b^-1*d^-1*a*d^-1*b*a^-3*b^-1*d^-1*a*d*b^-1*d*a^-1*d*b*a^2*b^-1*d^2*a^-1*d*a^-1*d*b^-1*d*b^-1*d*a^-1*d*b^-1,
  d^-1*a^-2*b^-1*d^-1*a*d^-1*b*d^-2*a^-1*d*b^-1*d^3*b^-1*d*a^-1*d*b*a*b*d^-1*a*d^-1*b*d^-1*b*d^-1*a*d^-1*a*d^-2*b*a,
  d^-1*a*b^-1*d*a^-1*d^2*b*d^-1*a*d^-1*a^-2*b^-1*d^-1*a*d^-1*b*d^-3*b*a^-2*b^-1*d^-1*a*d^-1*b*d^-2*b*d^-2*b*d^-1*a,
  d*a^-1*d*b^-1*d^2*a^-1*d^3*b^-1*d*a^-1*d*b*a^2*d*a^2*b^-1*d*a^-1*d*a^-1*d*b^-1*d^-1*b*d^-1*a*d^-1*a*b^-1*d*a^-1*d,
  b^-1*d^-1*a*d^-1*b*a^-1*d*a^-1*d*b^-1*d*b*d^-1*a*b^-1*d^-1*a*d^-1*b*d^-1*b^-1*a^2*b^-1*d*a^-1*d*b*a*b^-1*d^-1*a*d^-1*b*d*a^-3,
  a^-2*b^-1*d^-1*a*d^-1*b*d^-2*b*d^-1*b*d^-1*a*d^-1*a*b^-1*d*a^-1*d*b*a^2*b^-1*a^-1*b^-1*d^2*a^-1*d*a^-1*d*b^-1*d*b^-1*d*a^-1*d,
  d^-1*a^-2*b^-1*d^-1*a*d^-1*b*d^-2*a^-1*b^-1*d^2*a^-1*d*a^-1*d*b^-1*d*b^-1*d*a^-1*d*b^-1*d^-1*a*d^-1*b*a^-1*d*a^-1*d*b^-1*d*b*d^-1*a*b,
  b*a^-2*d^-1*a^-2*b^-1*d^-1*a*d^-1*b*d^-3*a*b^-1*d*a^-1*d*a*d^-1*b^2*d^-1*a*d^-1*a^-2*b^-1*d^-1*a*d^-1*b*d^-3*b*a^2,
  b^-1*d^-1*a*d^-1*b*a^-1*d*a^-1*d*a*b*a^-1*b^-1*d^-1*a*d^-1*a*b^-1*d*a^-1*d*b*a*b^-1*a^-1*d*b^-1*d*a^-1*d*b*d^-1*a*b^-1*d*a^-1*d*b*a,
  b^-1*d^-1*a*d^-1*b*d^-2*a*d^-1*b*d^-1*b*d^-1*a*d^-1*a*d^-2*b*a^3*d^-1*b^-1*a*b^-1*d*a^-1*d*b*a*b^-1*a^-1*d^-1*a*d^-1*b^2*d^-1*a,
  a^-1*b^-1*d^-1*a*d^-1*b*a^-1*d*a^-1*d*a*b*a*b^-1*d*a^-1*d*b*a^2*b^-1*d*a^-1*d*b^2*a^-1*b^-1*d^-1*a*d^-1*b*a^-1*b*a^-2*b^-1*d^-1*a*d^-1*b,
  d^-1*a*d^-1*b^2*d^-1*a*d^-1*a^-2*b^-1*d^-1*a*d^-1*b*d^-3*b*a*d^-1*a*d^-1*b*d*b^-1*d*a^-1*d*b^2*a^-2*b^-1*d^-1*a*d^-1*b*d^-2*b,
  d*a^-2*b^-1*d^-1*a*d^-1*b*a^-1*b^-1*a^-1*d^-1*a*d^-1*a*b^-1*d*a^-1*d*b*d*a*b*a^-2*b^-1*d^-1*a*d^-1*b*d^-2*a*d*b^-1*d*a^-1*d*b*a^2*d,
  a^-1*d*b^-1*d*a^-1*d^-1*a*d^-1*b*d*b^-1*d*a^-1*d^3*a^-1*d*a^-1*d*b^-1*d*b^-1*d*a^-1*d*b^-1*d^-1*a*d^-1*b*d*b^-1*d*a^-1*d*b^2*a^-2*b^-1*d^-1*a*d^-1*b*d^-1,
  a*b^-1*a^-1*b^-1*d^2*a^-1*d*a^-1*d*b^-1*d*b^-1*d*a^-1*d*a*d^-1*a^-2*b^-1*d^-1*a*d^-1*b*d^-1*a^-1*d*a^-1*d*b^-2*d*a^-1*d*a*d^2*b^-1*d*a^-1*d*b*a^2*d,
  a^-1*d*b^-1*d*b^-1*d^2*b^-1*d*a^-1*d*b*a^5*d^-1*b^-1*d*a^-1*d*b*a^-1*b^-1*d^-1*a*d^-1*b*a^-1*b^-1*d*a^-1*d*b*a*b^-1*d*b^-1*d*a^-1*d*b*a^2*b^-1*a^-1,
  a^-2*b^-1*d^-1*a*d^-1*b*d^-1*b^-1*d^2*b^-1*d*a^-1*d*b*a^3*b^-1*d^-1*a*d^-1*b*a^-2*b^-1*d^-1*a*d^-1*b*a^-5*b^-1*d^-1*a*d^-1*b*d^-2*b*d^-1*b*d^-1*a*d^-1,
  a*d*a^-2*b^-1*d^-1*a*d^-1*b*a^-3*d^-1*b^-1*d^-1*a*d^-1*b*a^-1*b*d^-1*a*d^-1*b*d^-1*b*d^-1*a*d^-1*a*d^-3*a*d^-1*b*d*b^-1*d*a^-1*d*b^2*a^-2*b^-1*d^-1*a*d^-1*b*d^-2,
  b^-2*d^2*a^-1*d*a^-1*d*b^-1*d*b^-1*d*a^-1*d*a*b^-1*d^-1*a*d^-1*b*a^-5*b^-1*d^-1*a*d^-1*b*d^-2*b*d^-1*b*d^-1*a^4*b^-1*d*a^-1*d*b*a^2*d^-1*a*b^-1*d*a^-1*d*b*a
];
mats := [
  # a  (AA in the source file)
  [ [ (6*zeta^5+2*zeta^4+4*zeta^3+4*zeta^2-zeta)/5, (-2*zeta^5-4*zeta^4+2*zeta^3-4*zeta)/5, (-zeta^5-zeta^4+3*zeta^3+2*zeta^2-4*zeta-3)/5 ],
    [ (-2*zeta^5-4*zeta^4-4*zeta^3-8*zeta^2-2*zeta-4)/5, (-4*zeta^5+2*zeta^3-5*zeta^2-2*zeta-4)/5, (-2*zeta^5-2*zeta^4-4*zeta^3-6*zeta^2-6*zeta-2)/5 ],
    [ (5*zeta^5-zeta^4+2*zeta^3+2*zeta^2+2*zeta+5)/5, (4*zeta^5-4*zeta^4+2*zeta^3+2*zeta^2)/5, (-2*zeta^5-7*zeta^4-6*zeta^3-4*zeta^2-2*zeta-6)/5 ] ]*one,
  # b  (BB in the source file)
  [ [ (-23*zeta^5-11*zeta^4-27*zeta^3-22*zeta^2-17*zeta+30)/35, (-24*zeta^5+22*zeta^4+19*zeta^3-5*zeta^2-8*zeta+10)/35, (48*zeta^5+33*zeta^4+11*zeta^3+24*zeta^2+37*zeta-6)/35 ],
    [ (11*zeta^5+22*zeta^4+47*zeta^3+9*zeta^2+6*zeta-18)/35, (27*zeta^5+5*zeta^4+4*zeta^3+10*zeta^2+16*zeta+57)/35, (-19*zeta^5-24*zeta^4-43*zeta^3-27*zeta^2+3*zeta-9)/35 ],
    [ (40*zeta^5+31*zeta^4+8*zeta^3+83*zeta^2-17*zeta+30)/70, (-47*zeta^5-38*zeta^4-36*zeta^3-41*zeta^2-25*zeta-65)/35, (-4*zeta^5+6*zeta^4+23*zeta^3+12*zeta^2+zeta+53)/35 ] ]*one,
  # d  (DD in the source file)
  [ [ (-zeta^5-2*zeta^4-3*zeta^3+3*zeta^2+2*zeta+8)/7, (2*zeta^5+4*zeta^4-8*zeta^3+zeta^2+3*zeta-2)/7, (3*zeta^5-zeta^4-5*zeta^3-2*zeta^2-6*zeta-3)/7 ],
    [ (9*zeta^5+4*zeta^4+6*zeta^3+zeta^2+3*zeta+5)/7, (3*zeta^5+6*zeta^4+2*zeta^3+5*zeta^2+zeta+11)/7, (8*zeta^5+9*zeta^4+10*zeta^3+11*zeta^2+12*zeta+6)/7 ],
    [ (-15*zeta^5+5*zeta^4+4*zeta^3-4*zeta^2+2*zeta-13)/14, (-6*zeta^5-5*zeta^4+3*zeta^3-3*zeta^2-2*zeta-1)/7, (-2*zeta^5+3*zeta^4+zeta^3-zeta^2+4*zeta+9)/7 ] ]*one
];
Add(FakeProjectivePlaneGroups, rec(
  name := "Q(sqrt(-7)), p=2, T1={5,7}",
  fieldGens:=[[zeta+zeta^2-zeta^3+zeta^4-zeta^5-zeta^6,zeta+zeta^6],
    ["ER(-7)","EC(7)"]],
  csName := "(a=7,p=2,\\{5,7\\})",
  k := "Q", ell := "Q(sqrt(-7))", p := 2, T1 := "{5,7}",
  N := 1, numberOfFakePlanes := 1,
  presentation := G, matrix := mats, field := F, form := form, conj := conj,
  fakePlanes := [
    rec(name := "(a=7,p=2,\\{5,7\\})",
        generators := List([a, b, d], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 1, abInv := [ 2, 9 ]) ] ));
end, []);

#############################################################################
##  k = Q,  ell = Q(sqrt(-15)),  p = 2
##  Field generators: s^2 = -15; Z^3 = 3*Z+3
##  (conj: s -> -s, Z -> Z)
CallFuncList(function()
local x, F, t, tbar, conj, form, f, G, mats, H, subgens, one, s, Z, a, b;
x := Indeterminate(Rationals, "x");
F := FieldExtension(Rationals, x^6+90*x^4+2025*x^2+30375);
one := One(F);
t := RootOfDefiningPolynomial(F);   # t = s*Z
s := (-1/45*t^3-t)*one;
Z := (1/675*t^4+1/15*t^2)*one;
tbar := (-t)*one;   # image of t under conj
conj := e -> ValuePol(ExtRepOfObj(e), tbar);
form := [ [ 2, 0, 0 ],
          [ 0, 0, 1 ],
          [ 0, 1, 0 ] ]*one;

# Q(sqrt(-15)), p=2, T1={}   [(a=15,p=2,\emptyset)]
f := FreeGroup("a", "b");
a := f.1;
b := f.2;
G := f / [
  (b*a*b*a^-1)^3,
  (b*a*b^-3*a^-1)^3,
  (b^2*a*b*a^-1*b^-1*a^2)^3,
  a^-1*b^-1*a^-3*b*a*b*a^-1*b^-1*a*b^3*a*b^-3*a^-2,
  b^2*a*b^4*a^-1*b*a*b*a^-1*b^-1*a^2*b*a^3*b^3*a*b,
  b^-1*a^2*b^-3*a^-3*b*a*b^-1*a^-1*b^-2*a^-1*b*a*b^-1*a^-1,
  b^-3*a^-2*b^-3*a^-2*b*a*b^-1*a^-1*b^-1*a*b^-1*a*b*a^-1*b*a,
  b*a*b*a^-1*b^-1*a^2*b*a^2*b^-3*a^-3*b^2*a*b*a*b^-3*a^-1*b,
  b^-1*a*b^2*a^-1*b^-1*a*b^2*a*b*a^-1*b*a^2*b^4*a^-1*b^-1*a^-1*b*a*b^-1*a^-1*b^-1*a
];
mats := [
  # a  (AE in the source file)
  [ [ (2*s*Z^2-3*s*Z+5*Z-9*s-5)/30, (-3*s*Z^2-5*Z^2+2*s*Z+10*Z+6*s+20)/30, (Z^2-Z-2)/3 ],
    [ (-s*Z^2-5*Z^2-s*Z+5*Z+2*s+10)/15, (-2*s*Z^2+3*s*Z+5*Z-s-5)/30, (s*Z^2-5*Z^2+s*Z-5*Z-2*s+20)/30 ],
    [ (2*s*Z^2+10*Z^2-3*s*Z-5*Z-4*s-10)/15, (s*Z^2-5*Z^2+s*Z+5*Z-2*s+10)/15, (-2*Z-s-1)/6 ] ]*one,
  # b  (BE in the source file)
  [ [ (-s-1)/6, (3*s*Z^2-5*Z^2-2*s*Z-6*s+20)/30, (s*Z^2+5*Z^2+s*Z-15*Z-2*s-10)/60 ],
    [ (s*Z^2+5*Z^2-4*s*Z-2*s-10)/30, (-s-1)/6, (Z^2-1)/3 ],
    [ (-3*s*Z^2-5*Z^2+2*s*Z+6*s+20)/15, (-2*s*Z^2-10*Z^2+3*s*Z+15*Z+4*s+20)/30, (-s-1)/6 ] ]*one
];
Add(FakeProjectivePlaneGroups, rec(
  name := "Q(sqrt(-15)), p=2, T1={}",
  fieldGens:=[[s,Z],["ER(-23)","Z"]],
  csName := "(a=15,p=2,\\emptyset)",
  k := "Q", ell := "Q(sqrt(-15))", p := 2, T1 := "{}",
  N := 3, numberOfFakePlanes := 2,
  presentation := G, matrix := mats, field := F, form := form, conj := conj,
  fakePlanes := [
    rec(name := "(a=15,p=2,\\emptyset,D_3)",
        generators := List([a, b^3, b^-1*a*b], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 3, abInv := [ 2, 2, 7 ]),
    rec(name := "(a=15,p=2,\\emptyset,3_3)",
        generators := List([a, b^2, b*a*b*a^-1*b^-1], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 3, abInv := [ 2, 2, 2, 9 ]) ] ));

# Q(sqrt(-15)), p=2, T1={3}   [(a=15,p=2,\{3\})]
f := FreeGroup("a", "b");
a := f.1;
b := f.2;
G := f / [
  (b*a^-1*b^-1*a*b*a)^3,
  b^-1*a^-1*b^2*a^-1*b^-1*a*b*a^3*b^-1*a*b^-1*a^2*b^-1*a^-1*b^-1*a^-1,
  b*a*b*a^-1*b^-1*a*b*a^3*b^-1*a^-1*b^-2*a^-2*b^-1*a^-1*b^2,
  a^-1*b^-1*a^-1*b*a^-2*b^-1*a^-1*b*a^-2*b^-1*a^-1*b*a*b^-1*a^-1*b^-2*a^-1,
  a*b*a*b^-1*a^-2*b^-1*a^-1*b^2*a^-2*b*a^-1*b*a^-1*b^-1*a*b*a,
  b*a^-1*b^-2*a*b*a^2*b^2*a*b^-1*a*b*a*b*a*b^-1*a*b*a^2,
  b*a*b^-1*a^-1*b*a*b^-1*a*b*a^2*b*a^-2*b*a^2*b*a^-2*b*a^-1*b*a^-1,
  b*a^2*b*a^-1*b^-1*a^2*b^-1*a^-2*b^-1*a*b^-2*a*b*a*b^2*a^-1*b^-1*a*b*a^2,
  a^-1*b^-1*a^-1*b*a^-1*b^-2*a^-2*b^-1*a^-1*b^2*a^-1*b*a^2*b*a^-2*b*a^-1*b*a^-1*b*a*b^-1*a^-1,
  (b*a*b^-1*a^2*b^-2*a*b*a)^3,
  b*a^-2*b^-1*a^-1*b^2*a^-2*b*a^-1*b^-1*a*b*a^-1*b^-1*a^-1*b*a^-1*b^-2*a^-1*b*a^-1*b^-1*a*b^-2*a*b*a^2,
  b^2*a*b^-1*a*b*a^2*b*a^-1*b^-1*a^2*b^-1*a^-1*b^-1*a^-2*b^-1*a^-1*b^2*a^-1*b*a^2*b*a^-1*b*a*b^-1*a,
  b*a^-1*b*a^2*b^-1*a^2*b^-2*a*b*a*b^-1*a^-1*b*a*b^-1*a^2*b^-1*a^-1*b^-2*a^-1*b*a*b^-1*a*b*a^2,
  b*a*b^-1*a*b*a*b^-1*a^-1*b*a^-1*b^-1*a^-1*b*a^-1*b*a^-1*b*a^-1*b*a^2*b*a^-2*b*a*b^-2*a*b*a^2*b*a^-1
];
mats := [
  # a  (A3 in the source file)
  [ [ (2*s*Z^2-3*s*Z+15*Z-9*s-15)/30, 0, 0 ],
    [ 0, (-4*s*Z^2+6*s*Z+3*s-15)/30, 0 ],
    [ 0, 0, (2*s*Z^2-3*s*Z-15*Z-9*s-15)/30 ] ]*one,
  # b  (B3 in the source file)
  [ [ (s-3)/6, (-s-3)/6, (-s+3)/12 ],
    [ (-s+3)/6, (s-3)/6, (-s-3)/6 ],
    [ (-s-3)/3, (-s+3)/6, (s-3)/6 ] ]*one
];
Add(FakeProjectivePlaneGroups, rec(
  name := "Q(sqrt(-15)), p=2, T1={3}",
  fieldGens:=[[s,Z],["ER(-15)","Z"]],
  csName := "(a=15,p=2,\\{3\\})",
  k := "Q", ell := "Q(sqrt(-15))", p := 2, T1 := "{3}",
  N := 3, numberOfFakePlanes := 3,
  presentation := G, matrix := mats, field := F, form := form, conj := conj,
  fakePlanes := [
    rec(name := "(a=15,p=2,\\{3\\},D_3)",
        generators := List([a, b*a*b^-1, b^-1*a*b], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 3, abInv := [ 2, 3, 7 ]),
    rec(name := "(a=15,p=2,\\{3\\},3_3)",
        generators := List([b*a^-1, a*b*a, a^-1*b], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 3, abInv := [ 2, 2, 2, 3 ]),
    rec(name := "(a=15,p=2,\\{3\\},(D3)_3)",
        generators := List([b, a^3, a*b*a^-1, a^-1*b*a], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 3, abInv := [ 2, 3 ]) ] ));

# Q(sqrt(-15)), p=2, T1={5}   [(a=15,p=2,\{5\})]
f := FreeGroup("a", "b");
a := f.1;
b := f.2;
G := f / [
  (b^-1*a)^3,
  b*a^3*b^-1*a*b^2*a^2*b^-1*a^-1*b^2*a*b^-2*a*b^-1*a^-2*b^3,
  b*a^2*b*a^-1*b^3*a^2*b^-1*a^-1*b^2*a*b^-1*a^-1*b*a^-3*b^3,
  b^2*a*b^-1*a*b^2*a^2*b*a*b^-2*a*b^-3*a*b^-1*a^-2*b*a^2*b*a^-1,
  a^2*b*a*b^-1*a^-1*b*a^-2*b^-1*a^-2*b*a^-3*b^3*a^2*b*a*b^-2*a,
  b^2*a^-1*b^-3*a^3*b^-1*a*b*a^-1*b^-1*a^-3*b^3*a^2*b*a*b*a^-1,
  b^2*a^-2*b^-3*a^3*b^-1*a*b*a^-1*b*a^2*b*a*b*a^-1*b^2*a^-1*b^-2*a^2*b*a^-1,
  b^-1*a^-1*b*a^-3*b*a^-2*b^-3*a*b^-1*a^-2*b^-2*a^2*b*a^-1*b^3*a^-1*b^3*a^-1*b^2*a^-1*b^-1,
  b^3*a*b*a^-1*b*a*b*a^-1*b^2*a^-2*b^-3*a^3*b^-1*a^-1*b^3*a^2*b*a*b*a^-1*b^2*a*b*a^-1,
  b^2*a^-1*b^-1*a^-3*b^-1*a^3*b^-1*a*b*a^-1*b^-1*a^-3*b^-1*a^2*b*a^-1*b^2*a^-1*b^-1*a^-3*b^-1*a^2*b*a^-1
];
mats := [
  # a  (A5 in the source file)
  [ [ (-2*s*Z^2+3*s*Z-5*Z-s-5)/30, (2*s*Z^2-8*Z^2-s*Z+17*Z-5*s+11)/30, (2*s*Z^2+10*Z^2-3*s*Z-5*Z-4*s-20)/30 ],
    [ (-3*s*Z^2-5*Z^2+2*s*Z+10*Z+6*s+10)/15, (2*s*Z^2-3*s*Z-5*Z-9*s-5)/30, (-2*s*Z^2+10*Z^2+4*s*Z-10*Z+3*s-25)/30 ],
    [ (-2*Z^2-3*s*Z-7*Z-s-1)/15, (s*Z^2-5*Z^2+s*Z-5*Z-2*s+10)/15, (2*Z-s-1)/6 ] ]*one,
  # b  (B5 in the source file)
  [ [ (-s-1)/6, (3*s*Z^2-5*Z^2-2*s*Z-6*s+20)/30, (s*Z^2+5*Z^2+s*Z-15*Z-2*s-10)/60 ],
    [ (s*Z^2+5*Z^2-4*s*Z-2*s-10)/30, (-s-1)/6, (Z^2-1)/3 ],
    [ (-3*s*Z^2-5*Z^2+2*s*Z+6*s+20)/15, (-2*s*Z^2-10*Z^2+3*s*Z+15*Z+4*s+20)/30, (-s-1)/6 ] ]*one
];
Add(FakeProjectivePlaneGroups, rec(
  name := "Q(sqrt(-15)), p=2, T1={5}",
  fieldGens:=[[s,Z],["ER(-15)","Z"]],
  csName := "(a=15,p=2,\\{5\\})",
  k := "Q", ell := "Q(sqrt(-15))", p := 2, T1 := "{5}",
  N := 3, numberOfFakePlanes := 2,
  presentation := G, matrix := mats, field := F, form := form, conj := conj,
  fakePlanes := [
    rec(name := "(a=15,p=2,\\{5\\},D_3)",
        generators := List([a, b*a*b^-1, b^-1*a*b], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 3, abInv := [ 2, 7 ]),
    rec(name := "(a=15,p=2,\\{5\\},3_3)",
        generators := List([a, b^2, b*a*b*a^-1*b^-1], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 3, abInv := [ 2, 2, 9 ]) ] ));

# Q(sqrt(-15)), p=2, T1={3,5}   [(a=15,p=2,\{3,5\})]
f := FreeGroup("a", "b");
a := f.1;
b := f.2;
G := f / [
  (b^3*a^-1*b^-1*a)^3,
  b^-1*a^-1*b^-1*a^-3*b^-1*a*b*a^-1*b^-1*a*b^2*a*b^-2*a^-1,
  b^-1*a*b^-2*a^-1*b*a*b^-1*a^3*b*a*b*a^2*b^2*a*b^-1*a,
  a*b*a*b^2*a^-1*b*a^-1*b^-2*a^-1*b*a*b^-1*a^-1*b^-1*a^-1*b^-1*a^-2*b^-1*a*b,
  (b^-1*a*b^2*a*b^-1*a*b^-1)^3,
  b^-1*a^-1*b*a*b^-1*a^-1*b*a^-1*b^-2*a^-1*b^-1*a^-2*b^-1*a^-3*b^-2*a^-1*b^-1*a^-1*b*a,
  a^2*b*a^2*b*a*b*a*b*a^-1*b*a^-1*b*a^-1*b^-2*a^-1*b*a*b^-2*a^-1*b*a*b^-1,
  b*a^-1*b^-2*a^-2*b^-1*a*b*a*b^2*a*b^-1*a*b*a^-1*b^-2*a^-1*b^-1*a^-2*b^-1*a^-3,
  a^-1*b^-1*a*b*a*b^2*a*b^-1*a^2*b*a^2*b*a*b*a*b^-1*a^-1*b*a*b^-3*a^-1*b^-1*a^-1,
  a*b*a^2*b*a*b*a*b*a^-1*b^-1*a^-1*b^-1*a^-2*b^-1*a*b*a*b^2*a*b^-3*a^-1*b^-1*a^-1*b*a*b^-1*a^-1*b*a*b^-1,
  b^-1*a^-1*b*a*b*a*b^-1*a^-1*b*a*b^-1*a*b*a^2*b*a*b*a*b*a^-1*b*a^2*b*a^2*b*a*b*a*b^-1*a^-1*b^-1*a^-1,
  a*b*a^-1*b^-1*a^-1*b^-1*a^-2*b^-1*a^-1*b*a^-1*b^-2*a^-1*b^-1*a^-1*b*a*b*a*b^-2*a^-1*b*a*b^-1*a^2*b*a^-1*b^-1*a*b*a^-1*b^-1*a*b,
  b^2*a^3*b*a*b*a*b*a*b^-2*a^-1*b*a*b^-1*a*b*a^-1*b^-1*a*b*a^-1*b^-1*a^-1*b^-1*a^-2*b^-1*a*b*a^-1*b^-1*a*b*a*b*a,
  a*b*a^-1*b^-1*a^-1*b^-1*a^-2*b^-1*a*b*a^2*b*a*b*a*b*a^-1*b^2*a^-1*b^-1*a*b^2*a^-1*b^-1*a^-1*b^-1*a^-1*b^-1*a^-1*b*a^-1*b^-1*a*b*a^-1*b^-1*a*b,
  (b^2*a*b^-1*a^2*b*a^-1*b^-1*a*b*a^-1*b^-1*a^-1*b^-1*a*b*a)^3,
  (b^2*a*b^-1*a^2*b*a^-1*b^-1*a*b*a^-1*b^-1*a^-1*b^-1*a*b*a^-1*b^-1*a*b*a)^3
];
mats := [
  # a  (A35 in the source file)
  [ [ (2*s*Z^2-3*s*Z+15*Z-9*s-15)/30, 0, 0 ],
    [ 0, (-4*s*Z^2+6*s*Z+3*s-15)/30, 0 ],
    [ 0, 0, (2*s*Z^2-3*s*Z-15*Z-9*s-15)/30 ] ]*one,
  # b  (B35 in the source file)
  [ [ (2*s*Z^2+10*Z^2-3*s*Z-15*Z-4*s)/30, (8*Z^2+3*s*Z+3*Z+s-21)/30, (4*Z^2-s-9)/12 ],
    [ (-6*s*Z^2-10*Z^2+4*s*Z+7*s+15)/30, (-s*Z^2-5*Z^2-s*Z+15*Z+2*s+30)/30, (-3*s*Z^2+5*Z^2+s*Z-15*Z+7*s-15)/30 ],
    [ (3*s*Z^2-13*Z^2-4*s*Z+12*Z-5*s+21)/15, (6*s*Z^2-10*Z^2-4*s*Z-17*s+15)/30, (-s*Z^2-5*Z^2+4*s*Z+2*s+30)/30 ] ]*one
];
Add(FakeProjectivePlaneGroups, rec(
  name := "Q(sqrt(-15)), p=2, T1={3,5}",
  fieldGens:=[[s,Z],["ER(-15)","Z"]],
  csName := "(a=15,p=2,\\{3,5\\})",
  k := "Q", ell := "Q(sqrt(-15))", p := 2, T1 := "{3,5}",
  N := 3, numberOfFakePlanes := 3,
  presentation := G, matrix := mats, field := F, form := form, conj := conj,
  fakePlanes := [
    rec(name := "(a=15,p=2,\\{3,5\\},D_3)",
        generators := List([a, b*a*b^-1, b^-1*a*b], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 3, abInv := [ 3, 7 ]),
    rec(name := "(a=15,p=2,\\{3,5\\},3_3)",
        generators := List([a*b, b*a], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 3, abInv := [ 2, 2, 3 ]),
    rec(name := "(a=15,p=2,\\{3,5\\},(D3)_3)",
        generators := List([a^3, a*b*a, a^-1*b], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 3, abInv := [ 3 ]) ] ));
end, []);

#############################################################################
##  k = Q,  ell = Q(sqrt(-23)),  p = 2
##  Field generators: s^2 = -23; Z^3 = Z+1
##  (conj: s -> -s, Z -> Z)
CallFuncList(function()
local x, F, t, tbar, conj, form, f, G, mats, H, subgens, one, s, Z, a, b;
x := Indeterminate(Rationals, "x");
F := FieldExtension(Rationals, x^6+46*x^4+529*x^2+12167);
one := One(F);
t := RootOfDefiningPolynomial(F);   # t = s*Z
s := (-1/23*t^3-t)*one;
Z := (1/529*t^4+1/23*t^2)*one;
tbar := (-t)*one;   # image of t under conj
conj := e -> ValuePol(ExtRepOfObj(e), tbar);
form := [ [ 2, 0, 0 ],
          [ 0, 0, 1 ],
          [ 0, 1, 0 ] ]*one;

# Q(sqrt(-23)), p=2, T1={}   [(a=23,p=2,\emptyset)]
f := FreeGroup("a", "b");
a := f.1;
b := f.2;
G := f / [
  b^3*a^-1*b^-1*a*b^3*a^-1*b^-1*a*b^3*a^-1*b^2*a*b^-3*a^-1*b^-1*a*b^8*a^-1*b^-1*a*b^3*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1,
  b^2*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b^3*a^-1*b^-1*a*b^3*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^3,
  a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^3*a*b^3*a^-1*b^-2*a*b^-3*a^-1*b*a*b^-2*a^-1*b*a*b^-5*a^-1*b*a*b^3*a^-1*b^-2*a*b^-3*a^-1*b*a*b^-2,
  b^3*a^-1*b^-2*a*b^-3*a^-1*b*a*b*a^-1*b^-1*a*b^3*a^-1*b^2*a*b^-3*a^-1*b^-1*a*b^5*a^-1*b^-1*a*b^-3*a^-1*b*a*b^3*a^-1*b^-2*a*b^-3*a^-1*b*a*b^-3*a^-1*b^2*a,
  a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^3*a*b^3*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^-2*a^-1*b*a*b^3*a^-1*b^-2*a*b^-3*a^-1*b*a*b^-1,
  b*a*b^3*a^-1*b*a^-1*b^-2*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b*a^-1*b*a*b^3*a^-1*b*a*b^3*a^-1*b^-2*a*b*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^3*a*b^3*a^-1*b^-1*a*b^3*a^-1*b^2,
  b^5*a^-1*b^-2*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b*a^-1*b*a*b^3*a^-1*b*a*b^3*a^-1*b^-7*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b^-1*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^2*a,
  b*a*b^-3*a^-1*b*a*b^-2*a^-1*b*a*b^3*a^-1*b*a*b^3*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^-2*a^-1*b^-1*a*b^2*a^-1*b^-1*a*b^3*a^-1*b^2*a*b^-3*a^-1*b^-1*a*b^-3*a*b^-3*a^-1*b^-1*a*b^-3*a^-1,
  a*b^3*a^-1*b^-1*a*b^3*a^-1*b^2*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b^3*a^-1*b^-2*a*b^-3*a^-1*b*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^3,
  b^2*a*b^-3*a^-1*b*a*b^-3*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^-2*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b^-2*a^-1*b*a*b^-5*a^-1*b*a*b^3*a^-1*b^-3*a*b^3*a^-1*b*a*b^3*a^-1*b^3,
  b^-2*a^-1*b^-2*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b*a^-1*b^2*a*b^-3*a^-1*b^-3*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b^-2*a^-1*b^-1*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b*a^-1*b*a*b^3*a^-1*b*a*b^3*a^-1*b^-2,
  a^-1*b^-2*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^4*a*b^2*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b^-2*a*b^3*a^-1*b*a*b^3*a^-1*b^3,
  b*a*b^-6*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b^-4*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b^-4*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b^3*a*b^-3*a^-1*b^-1*a*b^2*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b^-3*a^-1,
  b*a*b^3*a^-1*b*a*b^3*a^-1*b*a^-1*b^-1*a*b^3*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^-2*a^-1*b^-2*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b^-1*a^-1*b*a*b^-5*a^-1*b*a*b^3*a^-1*b^-2*a*b^-3*a^-1*b*a*b^-2*a^-1,
  a*b*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^3*a*b^3*a^-1*b^-1*a*b^3*a^-1*b^2*a*b^5*a^-1*b^-1*a*b^2*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^3*a*b^3*a^-1*b^-3*a*b^3*a^-1*b*a*b^3*a^-1*b^3,
  b*a*b^3*a^-1*b*a^-1*b^-2*a*b^-3*a^-1*b*a*b^-3*a^-1*b^-3*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b^-4*a^-1*b*a*b^3*a^-1*b^-2*a*b^-3*a^-1*b*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b^2*a*b^3*a^-1,
  b^-2*a*b^3*a^-1*b*a*b^3*a^-1*b^3*a*b^3*a^-1*b^-1*a*b^3*a^-1*b^3*a^-1*b^-2*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b*a^-1*b*a*b^3*a^-1*b^2*a*b^-3*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b*a*b^3*a^-1*b^-1,
  a*b^3*a^-1*b^-1*a*b^3*a^-1*b^2*a*b^-3*a^-1*b^-1*a*b^2*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^2*a*b^-8*a^-1*b^-1*a*b*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^3*a*b^3*a^-1*b^-1*a*b^3*a^-1*b^2*a,
  a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b^-2*a*b^3*a^-1*b*a*b^3*a^-1*b^3*a*b^3*a^-1*b^-1*a*b^3*a^-1*b^3*a*b^3*a^-1*b^-1*a*b^3*a^-1*b^2*a*b^-3*a^-1*b^-1*a*b^2*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^2*a*b^-1,
  b^-3*a^-1*b^-2*a*b^-3*a^-1*b*a*b^-3*a^-1*b^-3*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b^-1*a^-1*b^2*a*b^3*a^-1*b^-1*a*b^3*a^-1*b^-2*a^-1*b*a*b^3*a^-1*b^-2*a*b^-3*a^-1*b*a*b^-2*a^-1*b*a*b^2*a*b^-3*a^-1*b^-1*a*b^-3*a^-1,
  b^-1*a*b^-3*a^-1*b^-1*a*b^4*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b^-2*a*b^3*a^-1*b*a*b^3*a^-1*b^3*a*b^3*a^-1*b^-1*a*b^3*a^-2*b^-1*a*b*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^3*a*b^3*a^-1*b^-1*a*b^3*a^-1*b^2*a,
  b^-1*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b^-2*a^-1*b*a*b^3*a^-1*b^-1*a*b^3*a^-1*b^-5*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b^-1*a^-1*b*a*b^3*a^-1*b^-2*a*b^-3*a^-1*b*a*b^-2*a^-1*b*a*b^2*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b^2*a^-1*b^-1,
  b^6*a^-1*b^-2*a*b^-3*a^-1*b*a*b^-3*a^-1*b^-3*a*b^-3*a^-1*b*a*b^-3*a^-1*b^-1*a*b^2*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b^-3*a^-1*b^2*a*b^3*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1,
  b^3*a^-1*b^3*a^-1*b^-2*a*b^3*a^-1*b*a*b^3*a^-1*b^3*a*b^3*a^-1*b^-1*a*b^3*a^-1*b^3*a*b^3*a^-1*b^-2*a*b^-1*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^2*a^2*b^3*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^-1*a*b^3*a^-1*b*a,
  b^5*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b^-2*a*b^3*a^-1*b*a*b^3*a^-1*b^-2*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b^-1*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^2*a*b*a*b^3*a^-1*b*a*b^3*a^-1*b^4*a*b^3*a^-1*b*a*b^3*a^-1,
  b^8*a^-1*b^-1*a*b^2*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^2*a*b^5*a^-1*b^-1*a*b^3*a^-1*b^-1*a*b^3*a^-1*b^2*a*b^-3*a^-1*b^-2*a*b^2*a^-1*b^-1*a*b^3*a^-1*b^2*a*b^-3*a^-1*b^-1*a*b^2*a*b^-3*a^-1*b*a*b^-3*a^-1*b^-1*a,
  b^3*a^-1*b*a*b^3*a^-1*b^-2*a*b^-3*a^-1*b*a*b^-3*a^-2*b^-2*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^3*a*b^2*a^-1*b^-1*a*b^3*a^-1*b^2*a*b^-3*a^-1*b^-1*a*b^2*a*b^-3*a^-1*b*a*b^-3*a^-1*b^-1*a,
  b*a*b^3*a^-1*b^-1*a*b^3*a^-1*b^3*a^-1*b^-2*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b*a^-1*b^3*a^-1*b^-2*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b*a^-1*b*a*b^3*a^-1*b*a*b^3*a^-1*b^-2*a*b^-2*a^-1*b*a*b^3*a^-1*b^-2*a*b^-3*a^-1*b*a*b^-3*a^-1*b,
  b^5*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b^-2*a*b^3*a^-1*b*a*b^3*a^-1*b^3*a*b*a^-1*b*a*b^-5*a^-1*b*a*b^3*a^-1*b^-2*a*b^-3*a^-1*b*a*b^-1*a^-1*b*a*b^3*a^-1*b*a*b^3*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b*a^-1*b*a*b^3*a^-1,
  b*a*b^2*a^-1*b^-2*a*b^-3*a^-1*b*a*b^-3*a^-1*b*a*b^-1*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b^-1*a*b^-1*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b*a*b^3*a^-1*b^-1*a*b^3*a^-1*b^2*a*b^-3*a^-1*b^2*a*b^-3*a^-1*b^-3*a*b^-3*a^-1*b*a*b^-3*a^-1*b^-3*a*b^-3*a^-1*b^-1*a*b^-3*a^-1,
  b^-1*a*b^-1*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^2*a*b^-1*a*b^-3*a^-1*b^-3*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^3*a^-1*b^-2*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b^-2*a^-1*b*a*b^-3*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b*a*b^3*a^-1*b^-1,
  b^5*a*b^-3*a^-1*b^-3*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b^-2*a^-1*b*a*b^-5*a^-1*b*a*b^3*a^-1*b*a*b^3*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^3*a^-1*b^-1*a*b^2*a^-1*b^-1*a*b^3*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^2,
  b^-1*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b^-4*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b^-3*a^-1*b*a*b*a^-1*b*a*b^3*a^-1*b*a*b^3*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^-2*a^-1*b^-1*a*b^-1*a^-1*b^-1*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b^-2*a^-1*b*a*b^3*a^-1*b^-2*a*b^-3*a^-1*b*a*b^-3*a^-1,
  b^-2*a^-1*b^-1*a*b*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^3*a*b^3*a^-1*b^-1*a*b^3*a^-1*b^2*a*b^-5*a^-1*b*a*b^3*a^-1*b^-2*a*b^-3*a^-1*b*a*b^-2*a^-1*b*a*b^-3*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b^-3*a^-1*b^3*a*b^3*a^-1*b*a*b^3*a^-1,
  b^6*a^-1*b^-2*a*b^-3*a^-1*b*a*b^-3*a^-1*b^-3*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b^-2*a^-1*b*a*b^3*a^-1*b*a*b^3*a^-1*b^5*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b^-2*a*b^3*a^-1*b*a*b^3*a^-1*b^3*a*b^-2*a^-1*b*a*b^3*a^-1*b^-2*a*b^-3*a^-1*b*a*b^-3*a^-1*b*a*b^2,
  b^8*a^-1*b^-2*a*b^-3*a^-1*b*a*b^-3*a^-1*b^-3*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b^-2*a^-2*b^-2*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^4*a*b^7*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b^-2*a*b^3*a^-1*b*a*b^3*a^-1*b^2*a,
  b*a*b^3*a^-1*b*a*b^3*a^-1*b^3*a^-1*b^-1*a*b*a^-1*b^-1*a*b^3*a^-1*b*a*b^3*a^-1*b^3*a*b^3*a^-1*b^-1*a*b^3*a^-1*b^2*a*b^-5*a^-1*b*a*b^3*a^-1*b*a^-1*b^-2*a*b^-3*a^-1*b^-1*a*b^-3*a^-1*b*a*b*a^-1*b*a*b^3*a^-1*b*a*b^-2*a^-1*b*a*b^3*a^-1*b^-2*a*b^-3*a^-1*b*a*b^-3*a^-1*b*a
];
mats := [
  # a  (AA in the source file)
  [ [ (-5*s*Z^2-23*Z^2-4*s*Z+11*s+46)/23, (9*s*Z^2+69*Z^2-2*s*Z-92*Z-6*s)/46, (15*s*Z^2+23*Z^2-11*s*Z-23*Z-10*s)/46 ],
    [ (-9*s*Z^2+23*Z^2+2*s*Z+46*Z+6*s)/23, (7*s*Z^2-23*Z^2+s*Z+23*Z+3*s+46)/23, (-3*s*Z^2-7*s*Z+23*Z+2*s+23)/23 ],
    [ (-3*s*Z^2-69*Z^2+16*s*Z+46*Z+2*s+92)/23, (-6*s*Z^2-46*Z^2+9*s*Z-23*Z+4*s+46)/23, (-2*s*Z^2+46*Z^2+3*s*Z-23*Z+9*s)/23 ] ]*one,
  # b  (BB in the source file)
  [ [ (-8*s*Z^2-11*s*Z-23*Z+13*s-23)/92, 0, 0 ],
    [ 0, (7*s*Z^2-69*Z^2+s*Z+69*Z+3*s+23)/92, 0 ],
    [ 0, 0, (s*Z^2+69*Z^2+10*s*Z-46*Z+7*s-69)/92 ] ]*one
];
Add(FakeProjectivePlaneGroups, rec(
  name := "Q(sqrt(-23)), p=2, T1={}",
  fieldGens:=[[s,Z],["ER(-23)","Z"]],
  csName := "(a=23,p=2,\\emptyset)",
  k := "Q", ell := "Q(sqrt(-23))", p := 2, T1 := "{}",
  N := 1, numberOfFakePlanes := 1,
  presentation := G, matrix := mats, field := F, form := form, conj := conj,
  fakePlanes := [
    rec(name := "(a=23,p=2,\\emptyset)",
        generators := List([a, b], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 1, abInv := [ 2, 3, 7 ]) ] ));

# Q(sqrt(-23)), p=2, T1={23}   [(a=23,p=2,\{23\})]
f := FreeGroup("a", "b");
a := f.1;
b := f.2;
G := f / [
  b^-5*a^-1*b^-5*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^-2*a^-1*b^-3*a^2*b^-3*a*b^5*a*b^5*a^-1,
  b^2*a^-1*b^-3*a*b^3*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^2*a^3*b^-5*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-1*b^-3*a^-1*b^3*a,
  b^3*a^-1*b^-2*a*b^-3*a*b^5*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-8*a^-1*b^3*a^-2*b^-2*a^-1*b^-5*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1,
  a^2*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^3*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^8*a*b^5*a^-2*b*a*b^-3*a*b^8*a^-1*b*a*b^-3*a*b^2,
  b*a^-1*b^-2*a*b^-3*a*b^8*a^-1*b*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^3*a^-1*b^3*a*b^5*a^-2*b*a*b^-3*a*b^8*a^-1*b*a*b^-3*a*b^5*a*b^4,
  b^-1*a*b^-8*a^-1*b^3*a^-1*b^-1*a^2*b^-10*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-1*b^-1*a*b^5*a^-1*b*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^8*a^-1,
  a^-1*b^-5*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-4*a^2*b^-3*a*b^5*a*b^5*a^-2*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-3*a*b^5*a^-1*b^-3*a*b^3,
  a^2*b^-3*a*b^5*a*b^5*a^-1*b^3*a^-1*b*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a*b^10*a^-2*b*a*b^-3*a*b^2*a*b^3*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^2,
  b^-5*a^-1*b^3*a^-1*b*a*b^-8*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-8*a^-1*b^3*a*b^-10*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-1*b^-1*a*b^-3,
  b^5*a^-1*b^-3*a^-1*b^3*a*b^5*a^-1*b*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^5*a*b^2*a*b^-3*a^-1*b^3*a*b^5*a^-1*b*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a*b^5,
  b^-5*a^-1*b^3*a^-1*b^-1*a*b^-3*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-8*a^-1*b^3*a^-1*b^3*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^5*a*b^-3*a^-1*b^3*a*b^-5*a^-1,
  b^10*a^-1*b^-3*a*b^-3*a*b^5*a*b^5*a^-1*b^3*a*b^-10*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-1*b^-1*a*b^2*a^-1*b*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a,
  a*b^-5*a^-1*b^-3*a^2*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a*b^5*a^-3*b*a*b^-3*a*b^5*a*b^3*a^-1*b*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a*b^10*a^-2*b^4,
  a^2*b^-5*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-2*b^3*a*b^5*a^-1*b^-3*a^-1*b^3*a*b^2*a^-1*b^3*a^-1*b*a*b^-8*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-8,
  a^2*b^-5*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-2*b^3*a*b^5*a^-1*b^-3*a^-1*b^-2*a^-1*b^3*a^-1*b^-1*a*b^-3*a*b^3*a^-1*b*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a*b^10*a^-2*b*a,
  a^2*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a*b^5*a^-3*b*a*b^-3*a*b^8*a^-1*b*a*b^-3*a*b^5*a*b^10*a^-1*b*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^5*a*b^2,
  a*b^5*a^-1*b^-3*a*b^5*a*b^5*a^-2*b*a*b^-3*a*b^8*a^-1*b*a*b^-3*a*b^5*a*b^10*a^-1*b^-1*a*b^-3*a*b^5*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-3,
  b^-3*a^-1*b^3*a*b^2*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-8*a^-1*b^3*a^-1*b^3*a*b^-5*a^-1*b^-3*a*b^-3*a^-1*b^3*a*b*a^-1*b^-3*a*b^3*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^2*a,
  a*b^2*a*b^2*a*b^5*a^-2*b*a*b^-3*a*b^8*a^-1*b*a*b^-3*a*b^5*a*b^7*a*b^5*a*b^5*a^-1*b^-3*a*b^8*a^-1*b^2*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^5,
  a*b^-3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^-10*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-1*b^-1*a*b^-5*a^-1*b*a*b^-5*a^-1*b^-3*a*b^-1*a*b^-8*a^-1*b^3*a^-1*b^-1*a^2*b^-5*a^-1*b^-3,
  a^-1*b^3*a*b^5*a^-2*b*a*b^-3*a*b^8*a^-1*b*a^-1*b^3*a*b^5*a^-1*b^-1*a*b^-5*a^-1*b^-3*a*b^3*a*b^-5*a^-1*b^-3*a^2*b^-5*a^-1*b^-3*a^2*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a*b^5*a^-2*b^3,
  b^-4*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-2*a*b^-3*a*b^2*a*b^8*a^-1*b^2*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^5*a*b^2*a*b^-1*a*b^-3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^3*a^-1*b*a^-1*b^-2*a^-1*b^-1,
  b^-7*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-1*b^-1*a*b^-3*a^-1*b^-3*a*b^3*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^3*a*b^-3*a*b^8*a^-1*b*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^3*a*b^-3,
  b^-3*a^-1*b^3*a*b^3*a^-1*b*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a*b^10*a^-1*b^-6*a*b^3*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^6*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^5*a,
  b^-5*a^-1*b^3*a*b^-2*a^-1*b*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a*b^10*a^-2*b*a^-1*b^-2*a^-1*b^3*a^-1*b^-1*a*b^-3*a*b^-5*a^-1*b^3*a^-1*b*a^2*b^-5*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-1*b^-3*a^-1*b^-2*a^-1,
  b^5*a^-1*b*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^8*a^-1*b^-1*a*b^-3*a*b^-5*a^-1*b^3*a^-1*b^2*a*b^-5*a^-1*b^-3*a*b^-1*a*b^-8*a^-1*b^3*a^-1*b^-1*a^3*b^-5*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-1,
  b^8*a^-1*b*a*b^-3*a*b^5*a*b^5*a^-2*b*a*b^-8*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-5*a^-1*b^-2*a^-1*b^-5*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-5*a^-1*b^-3*a^2*b^-3*a,
  b^3*a*b^5*a^-2*b*a*b^-3*a*b^8*a^-1*b*a*b^-3*a*b^2*a*b^-1*a^2*b^-10*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-1*b^-1*a*b^-3*a^-2*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-8*a^-1*b^3*a^-1*b^2,
  b^13*a^-1*b*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a*b^12*a^-1*b^-3*a*b^3*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^3*a*b^-3*a*b^8*a^-1*b*a^-1*b^3*a*b^5*a^-1*b^-2*a*b^-3*a,
  b^10*a^-2*b*a^-1*b^3*a*b^5*a^-1*b^-1*a*b^-3*a*b^8*a*b^-10*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-1*b^-1*a*b^-3*a^-1*b^-3*a*b^2*a*b^-3*a*b^3*a^-1*b*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a,
  a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-3*a*b^5*a^2*b^-5*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-2*b^3*a*b^5*a^-1*b^-3*a^-1*b^3*a*b^-3*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-1*b^-1*a*b^-8*a^-1*b^3,
  b^-5*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a^2*b^-5*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-1*b^2*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-1*b^-1*a*b^5*a^-1*b^-1*a*b^-3*a*b^5*a^-1*b^3*a^-1*b*a*b^-3,
  b^3*a^-1*b^-2*a^2*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-3*a*b^5*a^-1*b^3*a^-1*b*a*b^-3*a*b^5*a*b^4*a^-1*b^-3*a*b^3*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^2*a*b^-3*a^-1*b^-2*a^-1*b^-5*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1,
  a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-8*a^-1*b^3*a^2*b^-5*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-2*b^3*a*b^5*a^-1*b^-3*a^-1*b^-2*a^-1*b^-5*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-8,
  b^8*a^-1*b*a*b^-3*a*b^5*a*b^5*a^-1*b^-8*a^-1*b^3*a^-1*b^-1*a^2*b^-5*a^-2*b*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^8*a^-1*b^-1*a*b^-3*a*b^-5*a^-1*b^3*a^-1*b*a*b^-10*a^-1*b^-3*a^2*b^-3*a,
  b^10*a^-1*b^-2*a*b^-3*a*b^8*a^-1*b*a^-1*b^-2*a^-1*b^-5*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^8*a^-1*b*a*b^5*a^-1*b*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a,
  b^-2*a^-1*b^3*a*b^-1*a^-1*b^-3*a*b^3*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^2*a*b^-3*a^-1*b^3*a*b^-3*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-1*b^-2*a^3*b^-5*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-2*b^3*a*b^5*a^-1*b^-4,
  b^10*a^-1*b^-3*a*b^-1*a^-1*b^-3*a*b^3*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^2*a*b^-3*a^-1*b^3*a*b^2*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a^2*b^-5*a^-1*b^-5*a^-1*b^-5*a^-1*b^3*a*b^3*a^-1*b*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a,
  b^5*a*b^5*a^-2*b^3*a^-1*b^2*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a*b^7*a^-1*b^-3*a*b^3*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^2*a*b^-1*a*b^-6*a*b^3*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^2*a^2*b^-3*a,
  a^-1*b^-3*a*b^3*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^2*a^2*b^-3*a*b^5*a*b^5*a^-2*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-6*a*b^3*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^2*a^2*b^-3*a*b^5*a*b^5*a^-1,
  b^10*a^-1*b^-3*a^2*b^-5*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-2*b^3*a*b^5*a^-2*b^3*a*b^5*a^-2*b^-2*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-3*a^-1*b^3*a*b^2*a^-1*b*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a,
  b^10*a^-1*b^-3*a^-1*b*a*b^-3*a*b^8*a^-1*b*a^-1*b^3*a*b^5*a^-1*b^-2*a^2*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-3*a*b^5*a^-1*b^3*a^-1*b*a*b^-3*a*b^5*a*b^9*a^-1*b*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a,
  b^15*a^-1*b*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^8*a^-2*b^3*a*b^5*a^-1*b^-1*a*b^-5*a^-1*b^-3*a*b^3*a*b^-5*a^-1*b^-3*a*b^-3*a^-1*b^3*a*b^-3*a^-1*b^3*a^-1*b^2*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a,
  b^10*a^-1*b^-4*a*b^-3*a^2*b^-5*a^-1*b^-5*a^-1*b^3*a^-2*b^-2*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-3*a^-1*b^3*a*b^5*a^-1*b^3*a^-1*b*a*b^-3*a*b^5*a*b^10*a^-1*b*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a,
  a*b^5*a*b^2*a*b^5*a*b^5*a^-2*b*a*b^-3*a*b^8*a^-1*b*a*b^-3*a*b^5*a*b^7*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a^2*b^-5*a^-3*b*a*b^-3*a*b^8*a^-1*b*a*b^-3*a*b^5*a*b^10*a^-1*b^-1*a*b^-3*a*b^2,
  b^-2*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^3*a*b^-5*a^-1*b^-3*a^2*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a*b^5*a^-3*b^2*a*b^5*a^-1*b*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a*b^10*a^-1*b^-2*a*b^-3*a*b^8*a^-1,
  b^3*a^-1*b*a*b^-3*a*b^5*a*b^5*a^-2*b*a*b^-3*a*b^2*a*b^-3*a^-1*b^3*a*b^-1*a^-1*b^-3*a*b^3*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^2*a*b^-3*a^-1*b^3*a*b^2*a^-1*b^-3*a*b^-3*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-3*a^-1*b^3*a*b^-5*a^-1,
  b^10*a^-1*b^-3*a*b^-5*a^-1*b^3*a^-1*b*a*b^-3*a*b^5*a*b^5*a^-1*b^-6*a*b^3*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^2*a^2*b^-3*a*b^5*a*b^5*a^-2*b^3*a*b^3*a^-1*b*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a,
  b^10*a^-1*b^-1*a*b^5*a^-1*b*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a*b^10*a^-1*b^-2*a*b^-3*a*b^8*a^-1*b^-2*a^-1*b^-2*a^-1*b^-5*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^8*a^-1*b*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a,
  a^-1*b^-2*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-3*a^-1*b^3*a*b^-1*a^-1*b^-3*a*b^3*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^2*a*b^-3*a^-1*b^3*a*b^-3*a^-1*b^-3*a*b^3*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^2*a^2*b^-3*a*b^5*a*b^5*a^-2*b^3,
  b^-3*a^-1*b^3*a*b*a^-1*b^-3*a*b^3*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^2*a*b^-3*a^-1*b^3*a*b^-3*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-3*a*b^5*a^-1*b^3*a^-1*b*a*b^-3*a*b^2*a*b^3*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a*b^5*a^-2,
  a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-3*a*b^-5*a^-1*b^3*a^-1*b*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^5*a^-1*b^3*a^-1*b*a*b^-8*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-5*a^-1*b^-2*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-3*a^-1*b^3*a*b^-3,
  b^3*a^-1*b*a*b^-3*a*b^8*a^-1*b*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^3*a^-1*b^-2*a^-1*b^-5*a^-1*b^3*a*b^-2*a^-1*b*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a*b^10*a^-2*b*a^-1*b^3*a*b^2*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-3*a*b^-5*a^-1*b^-5*a^-1,
  b^13*a^-1*b*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a*b^7*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-3*a*b^-5*a^-1*b^3*a^-1*b*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^3*a^-1*b^-3*a*b^3*a^-1*b^3*a*b^5*a^-1*b^-3*a^-1*b^3*a*b^5*a^-1*b^-1*a*b^-3*a,
  b^8*a^-1*b*a*b^-3*a*b^5*a*b^5*a^-2*b*a*b^-3*a*b^5*a*b^-2*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-3*a*b^-5*a^-1*b^3*a^-1*b*a^-1*b^-2*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-3*a^-1*b^3*a*b^3*a^-1*b^-3*a*b^-3*a*b^5*a*b^5*a^-1*b^3*a^-1*b*a*b^-3*a,
  b^10*a^-2*b^3*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^5*a*b^2*a*b^-3*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-3*a^-1*b^3*a*b^-5*a^-1*b^3*a^-1*b*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^3*a^-1*b*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a,
  b^-7*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-1*b^-1*a^2*b^-5*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-1*b^-3*a^-1*b^-2*a^-1*b^-5*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b*a*b^-10*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-1*b^-1*a*b^-8,
  a*b^5*a^-1*b^3*a^-1*b*a*b^-8*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-3*a*b^5*a*b^5*a^-2*b*a*b^-3*a*b^2*a*b^3*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a*b^5*a^-2*b^-1*a*b^-8*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-3,
  b^-1*a*b^3*a^-1*b^-2*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-3*a^-1*b^3*a*b*a^-1*b^3*a^-1*b*a*b^-8*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-11*a*b^5*a*b^2*a*b^2*a*b^-3*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-8*a^-1*b^3*a^-1,
  b^8*a^-1*b^-3*a*b^3*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^2*a*b^-3*a*b^-3*a*b^5*a*b^5*a^-1*b^-5*a^-1*b^3*a^-1*b*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^8*a^-1*b*a*b^-3*a*b^5*a*b^5*a^-2*b^2*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a,
  a*b^-3*a*b^-3*a*b^5*a*b^5*a^-1*b^3*a^-1*b^-2*a^-1*b^-2*a^-1*b^-5*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-2*b^-3*a*b^3*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^2*a*b^-1*a*b^-3*a*b^5*a^-1*b^3*a^-1*b*a^-1*b^-2*a^-1*b^3*a^-1*b^-1*a*b^-8*a^-1*b^3*a^-1*b^-1*a^2*b^-5*a^-1*b^-6,
  b^5*a*b^5*a^-1*b^-3*a*b^2*a*b^-3*a^-1*b^3*a*b^3*a^-1*b^-3*a*b^3*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^2*a*b^-3*a^-1*b^3*a*b^5*a^-1*b^-1*a*b^-3*a*b^13*a^-1*b*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a*b^9*a^-1*b^-3*a*b^3*a*b^-3*a,
  b^8*a^-1*b*a*b^-3*a*b^5*a*b^5*a^-2*b*a*b^-3*a*b^5*a*b^10*a^-1*b*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a*b^10*a^-1*b^-1*a*b^-10*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-1*b^-1*a*b^-10*a^-1*b^-3*a^2*b^-3*a,
  b^7*a^-1*b^-3*a*b^3*a^2*b^-5*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-1*b^-3*a^-1*b^-2*a^-1*b^3*a^-1*b^-1*a*b^-3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b*a*b^-3*a*b^5*a*b^-5*a^-1*b^3*a^-1*b*a*b^-3*a*b^5*a*b^5*a^-2*b^2*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a,
  b^10*a^-2*b*a^-1*b^3*a*b^5*a^-1*b^-3*a*b^3*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^2*a*b^-3*a*b^-3*a*b^5*a*b^5*a^-1*b^3*a^-1*b^-2*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-2*b^-2*a^-1*b^-5*a^-1*b^3*a*b^-2*a^-1*b*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a,
  b^-2*a^-1*b^-5*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-2*a*b^-3*a*b^2*a*b^5*a*b^2*a*b^5*a*b^2*a*b^2*a*b^-3*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-8*a^-1*b^3*a^-1*b^-1*a*b^3*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^5*a*b^5*a^-1*b^3*a^-1*b*a^-1,
  b^10*a^-1*b^-6*a*b^5*a*b^5*a*b^3*a^-1*b*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a*b^10*a^-1*b^-8*a^-1*b^3*a^-1*b^-1*a*b^-3*a*b^5*a*b^5*a^-1*b^3*a^-1*b*a*b^-3*a*b^5*a*b^6*a^-1*b*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a,
  b^5*a*b^5*a^-1*b^3*a^-1*b*a*b^-3*a*b^5*a*b^3*a^-1*b^-3*a*b^3*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^2*a*b^-3*a*b^-3*a*b^5*a*b^5*a^-1*b^3*a^-1*b^6*a*b^5*a^-2*b*a*b^-3*a*b^8*a^-1*b*a*b^-3*a*b^2*a*b^-1*a*b^-8*a^-1*b^3*a^-1*b^-1*a*b^-3*a,
  b^-3*a*b^5*a*b^8*a*b^-10*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-1*b^-1*a*b^-4*a^-1*b^-3*a*b^3*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^2*a*b^-3*a^-1*b^3*a*b^2*a^-1*b^-3*a*b^3*a*b^-5*a^-1*b^-3*a^2*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a*b^5*a^-2,
  b^-3*a*b^5*a*b^5*a^-1*b^3*a^-1*b*a*b^-3*a*b^5*a*b^-2*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-3*a*b^-5*a^-1*b^3*a^-1*b*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a*b^5*a^-2*b^3*a^-1*b*a^-1*b^-2*a^-1*b^3*a^-1*b^-1*a*b^-8*a^-1*b^3*a^-1*b^-1*a^2*b^-5*a^-1*b^-6*a^2*b^-5*a^-1*b^-3*a*b^-3,
  b^-3*a*b^5*a*b^8*a*b^-10*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-1*b^-1*a*b^-3*a^-1*b^-3*a*b^6*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a*b^5*a^-2*b^-1*a*b^-3*a*b^5*a^-1*b^3*a*b^-10*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-1*b^-1*a*b^-3*a^-1,
  b^13*a^-1*b*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^8*a^-2*b^3*a*b^5*a^-1*b^-2*a^2*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-3*a*b^5*a^-1*b^3*a^-1*b*a*b^-3*a*b^5*a*b*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-3*a*b^-5*a^-1*b^3*a^-1*b*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a,
  b^5*a*b^5*a^-2*b^2*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a*b^3*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-3*a*b^-5*a^-1*b^3*a^-1*b*a*b^-3*a*b^5*a*b^5*a^-2*b^2*a*b^-5*a^-1*b^-3*a*b^-3*a^-1*b^3*a*b^-1*a^-1*b^-3*a*b^3*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^2*a*b^-3*a^-1*b^3*a*b^-3*a^-1*b^3*a^-1*b*a*b^-3*a,
  b^10*a^-2*b^4*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^2*a^2*b^-3*a*b^5*a*b^5*a^-2*b^-3*a*b^5*a*b^2*a*b^3*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^6*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^3*a^-1*b^-5*a^-1*b^3*a*b^-2*a^-1*b*a*b^-5*a^-1*b^-3*a^2*b^-3*a*b^5*a,
  a*b^-3*a*b^8*a^-1*b*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^3*a^-1*b*a^2*b^-5*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-1*b^-3*a^-1*b^-2*a^-1*b^3*a^-1*b^-1*a^2*b^-5*a^-1*b^-5*a^-1*b^-10*a^-1*b^3*a^-1*b*a*b^-5*a^-1*b^-3*a*b^3*a^-1*b^-2*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-3*a^-1*b^3*a*b^-3*a^-1*b^-3*a,
  b^8*a^-1*b^-1*a*b^-3*a*b^-5*a^-1*b^3*a^-1*b*a*b^-8*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-3*a*b^5*a^-1*b^3*a^-1*b*a*b^-3*a*b^5*a*b^-2*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-3*a*b^-5*a^-1*b^3*a^-1*b*a^2*b^-5*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-1*b^2*a^-1*b*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a,
  b^3*a^-1*b^3*a*b^-10*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-1*b^-1*a*b^-7*a^-1*b^-3*a*b^3*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^2*a*b^-3*a*b^-10*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-1*b^-1*a*b^-3*a^-1*b^3*a^-1*b*a*b^-8*a^-1*b^3*a*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-5*a^-1*b^-2*a^-1,
  b^-5*a^-1*b^-5*a^-1*b^3*a*b^-3*a^-1*b^-3*a*b^3*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^2*a^2*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^8*a^-1*b*a*b^-3*a*b^5*a*b^5*a^-2*b^2*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a*b^8*a^-1*b^-1*a^2*b^-10*a^-1*b^-5*a^-1*b^3*a^-2*b^3*a*b^5*a^-1*b^-1*a*b^-3,
  b^3*a^-1*b^-3*a^2*b^-3*a*b^8*a^-1*b*a*b^-3*a*b^5*a*b^5*a^-1*b^-8*a^-1*b^3*a^-1*b^-1*a^2*b^-5*a^-1*b^-5*a^-1*b^3*a*b^5*a^-2*b*a*b^-3*a*b^8*a^-1*b*a^2*b^-5*a^-1*b^-5*a^-1*b^3*a^-1*b^-3*a^-1*b^3*a*b^-2*a^-1*b^-5*a^-1*b^3*a^-1*b^-1*a*b^-3*a*b^-5*a^-1*b^3*a^-1*b*a*b^-3*a*b^5*a*b^5*a^-1*b^-3*a
];
mats := [
  # a  (AD in the source file)
  [ [ (s*Z^2-23*Z^2+10*s*Z+92*Z+7*s-23)/46, (10*s*Z^2-60*Z^2-2*s*Z-2*Z-15*s+63)/46, (4*s*Z^2-6*s*Z+5*s+69)/46 ],
    [ (-2*s*Z^2+3*s*Z+23*Z+9*s+69)/23, (-8*s*Z^2+46*Z^2+12*s*Z-92*Z+13*s-69)/46, (7*s*Z^2+69*Z^2-2*s*Z-13*s-23)/46 ],
    [ (-17*s*Z^2-9*Z^2+4*s*Z+2*Z+3*s+29)/23, (-2*s*Z^2+3*s*Z-23*Z+9*s+69)/23, (7*s*Z^2-23*Z^2-22*s*Z+3*s-23)/46 ] ]*one,
  # b  (BD in the source file)
  [ [ (-8*s*Z^2-11*s*Z-23*Z+13*s-23)/92, 0, 0 ],
    [ 0, (7*s*Z^2-69*Z^2+s*Z+69*Z+3*s+23)/92, 0 ],
    [ 0, 0, (s*Z^2+69*Z^2+10*s*Z-46*Z+7*s-69)/92 ] ]*one
];
Add(FakeProjectivePlaneGroups, rec(
  name := "Q(sqrt(-23)), p=2, T1={23}",
  fieldGens:=[[s,Z],["ER(-23)","Z"]],
  csName := "(a=23,p=2,\\{23\\})",
  k := "Q", ell := "Q(sqrt(-23))", p := 2, T1 := "{23}",
  N := 1, numberOfFakePlanes := 1,
  presentation := G, matrix := mats, field := F, form := form, conj := conj,
  fakePlanes := [
    rec(name := "(a=23,p=2,\\{23\\})",
        generators := List([a, b], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 1, abInv := [ 3, 7 ]) ] ));
end, []);

#############################################################################
##  k = Q(sqrt(5)),  ell = Q(sqrt(5))(sqrt(-3)),  p = 2
##  Field generators: g^2 = g+1; zeta^6 = -zeta^3-1
##  (conj: g -> g, zeta -> zeta^8)
CallFuncList(function()
local x, F, t, tbar, conj, form, f, G, mats, H, subgens, one, g, zeta, a, b, z;
x := Indeterminate(Rationals, "x");
F := FieldExtension(Rationals, x^12+4*x^9+17*x^6-4*x^3+1);
one := One(F);
t := RootOfDefiningPolynomial(F);   # t = g*zeta
g := (1/34*t^9-21/34)*one;
zeta := (1/34*t^10-55/34*t)*one;
tbar := (-13/34*t^11-3/2*t^8-13/2*t^5+26/17*t^2)*one;   # image of t under conj
conj := e -> ValuePol(ExtRepOfObj(e), tbar);
form := [ [ -2*g*zeta^5+2*zeta^5-2*zeta^4-2*g*zeta^2+4*zeta^2+2*g*zeta-4*zeta-4*g+6, 0, 0 ],
          [ 0, 2*g*zeta^5-4*zeta^5+2*g*zeta^4-2*zeta^4-2*zeta^2+2*zeta-4*g+6, 0 ],
          [ 0, 0, 2*zeta^5-2*g*zeta^4+4*zeta^4+2*g*zeta^2-2*zeta^2-2*g*zeta+2*zeta-4*g+6 ] ]*one;

# C2, p=2, T1={}   [(C2,p=2,\emptyset)]
f := FreeGroup("a", "b", "z");
a := f.1;
b := f.2;
z := f.3;
G := f / [
  z^3,
  (z^-1*b*a^-1)^3,
  b*a^-2*z^-1*b^2*z*a,
  a^-1*b^-1*z*a*b^-2*a^-1*z^-1,
  a^-1*z^-1*b*a^-2*z*b^-1*z^-1*b^-1*z*a*z^-1*b*z,
  a^-1*z^-1*a^-1*z^-1*b^-1*z^-1*a*z^-1*b^-1*z^-1*b^-1*z^-1,
  b^-1*z*a*z*a*z*a*z^-1*b^-1*z^-1*a*z*a*z^-1*b^-1*z^-1,
  b^-1*z*b^-1*z*a^-1*z^-1*b*z^-1*a*z^-1*b*z*a*z*a*z^-1,
  z^-1*b*z^-1*b*z*b^-1*z*a*z^-1*b*z^-1*b*a*z^-1*b^-1*z*a*z^-1*b
];
mats := [
  # a  (AA in the source file)
  [ [ (g*zeta^4+zeta^4+g*zeta^3+zeta^3-g*zeta^2+1)/3, (-g*zeta^5-g*zeta^3+zeta^2-1)/3, (g*zeta^5-3*g*zeta^4-g*zeta^3+2*zeta^3-zeta^2-2*g*zeta-zeta+3)/3 ],
    [ (g*zeta^5+zeta^5+2*g*zeta^4+2*zeta^4+2*g*zeta^3+zeta^2+2*g*zeta+2)/3, (g*zeta^5-g*zeta^4-zeta^4+g*zeta^3+zeta^3+g*zeta^2-g*zeta-zeta+1)/3, (-zeta^5-g*zeta^3-g*zeta^2-zeta^2-1)/3 ],
    [ (zeta^5-g*zeta^3+zeta^3-g*zeta^2+1)/3, (-zeta^5-2*zeta^4+2*g*zeta^3+g*zeta^2-2*g*zeta-2*zeta+2)/3, (-g*zeta^5+g*zeta^3+zeta^3+g*zeta+zeta+1)/3 ] ]*one,
  # b  (BB in the source file)
  [ [ (g*zeta^5-zeta^5+g*zeta^4+zeta^4-g*zeta^3+zeta^3-zeta^2+zeta+1)/3, (zeta^3-g*zeta^2+zeta-g)/3, (-g*zeta^4+zeta^4+zeta^3+2*g*zeta^2-g*zeta+g+3)/3 ],
    [ (-g*zeta^5-zeta^5+zeta^4+3*g*zeta^3+zeta^2+g*zeta+g+1)/3, (zeta^5-g*zeta^4-g*zeta^3+zeta^3+g*zeta^2-g*zeta-zeta+1)/3, (g*zeta^5+zeta^4+zeta^3+g*zeta^2-g)/3 ],
    [ (zeta^5-g*zeta^4-2*g*zeta^3-zeta^3+g*zeta^2+2*zeta^2+g*zeta-zeta-3*g)/6, (-zeta^5+g*zeta^4-zeta^4+3*g*zeta^3-g*zeta^2-2*zeta^2-zeta+g+1)/3, (-g*zeta^5-zeta^4-g*zeta^3+zeta^3-g*zeta^2+zeta^2+g*zeta+1)/3 ] ]*one,
  # z  (ZZ in the source file)
  [ [ zeta, 0, 0 ],
    [ 0, zeta^4, 0 ],
    [ 0, 0, -zeta^4-zeta ] ]*one
];
Add(FakeProjectivePlaneGroups, rec(
  name := "C2, p=2, T1={}",
 # fieldGens:=[[-g,zeta],["EB(5)","Z"]],
  fieldGens:=[[1/17*t^9-38/17,4/17*t^9+t^6+4*t^3-16/17,
    21/34*t^11+1/34*t^10+5/2*t^8+21/2*t^5-42/17*t^2-55/34*t],
    ["ER(5)","E(3)","EY(9)"]],
  csName := "(C2,p=2,\\emptyset)",
  k := "Q(sqrt(5))", ell := "Q(sqrt(5))(sqrt(-3))", p := 2, T1 := "{}",
  N := 9, numberOfFakePlanes := 6,
  presentation := G, matrix := mats, field := F, form := form, conj := conj,
  fakePlanes := [
    rec(name := "(C2,p=2,\\emptyset,d_3 D_3)",
        generators := List([b*a*b^-1, z*a*z^-1, b*z^-1*b*z*b], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 9, abInv := [ 2, 7 ]),
    rec(name := "(C2,p=2,\\emptyset,D_3 X_3)",
        generators := List([z*a*z, z^-1*a*z^-1, b*z^-1*a*z^-1*b^-1], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 9, abInv := [ 2, 7, 9 ]),
    rec(name := "(C2,p=2,\\emptyset,(dD)_3 X_3)",
        generators := List([a, b*a*b^-1, (b*z^-1)^2], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 9, abInv := [ 2, 9 ]),
    rec(name := "(C2,p=2,\\emptyset,(d^2D)_3 X_3)",
        generators := List([b*a*b^-1, z^-1*a*z^-1*b, (z*b)^2], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 9, abInv := [ 2, 9 ]),
    rec(name := "(C2,p=2,\\emptyset,d_3 X'_3)",
        generators := List([b, z*a*z^-1], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 9, abInv := [ 2, 3, 3 ]),
    rec(name := "(C2,p=2,\\emptyset,X_9)",
        generators := List([b, z*a*z*a*z*a*z*a^-1*z^-1*a^-1*z^-1, z*a*z*a*z^-1*b*z^-1*a^-1*z^-1*a^-1*z^-1], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 9, abInv := [ 2, 3, 3 ]) ] ));

# C2, p=2, T1={3}   [(C2,p=2,\{3\})]
f := FreeGroup("a", "b", "z");
a := f.1;
b := f.2;
z := f.3;
G := f / [
  z^3,
  (b*z)^3,
  a*z*b*z^-1*a^-1*z^-1*a^-1*z*b^-1,
  a^-1*b^-1*z^-1*a^-1*z*b^-1*z*a^-1*b^-1*z^-1,
  b^-1*z*a^-1*b^-1*z*b*z^-1*a*b^-1*z^-1*b^-1,
  b*z^-1*a*z^-1*b^-1*a*b^-1*z*a*z*b,
  a^-2*z^-1*a^-1*z^-1*b^-1*z*a^-2*b*z,
  (a^-1*z^-1*a^-1*b)^3,
  b^-1*z*b^-1*a*z^-1*a^-2*b*z^-1*a^-1*b*z*a^-1,
  z*a^-1*b*z*b^-1*z*a^-1*z*b^2*a*z^-1*b,
  z^-1*a^-1*z*a^-1*z^-1*a^-1*b*a*z^-1*b^-1*a*z^-1*a^-2,
  a^-1*b^-1*z^-1*a^-1*z^-1*a*z*a^2*z*a*z*a*z^-1*b,
  a^-1*b*z^-1*b*a*b^-1*z*a^-1*b^-2*z*a^-2*b*z^-1,
  b^-1*a*b^-1*z*b^-1*a*z^-1*b^-1*z^-2*a^-1*b^-2*z*a^-1*z,
  a*z^-1*b^2*z^-1*a^-2*b*z*a^-1*z*b*a*z*b^-1*z^-1,
  b^-2*a^2*z^-1*b^2*a*z*b^-1*z^-1*a*b^-1*z*a^-1*b^-1,
  a^-1*b*z^-1*b*a*z*a^-1*b*z*a^-1*b^-1*z^-1*a^-1*z*b*a*z^-1*b*a^-1*b^-1,
  z*a^-1*b*z^-1*a*b*z*b*a^-1*b*z*b*a*z*b^-1*z^-1*a*b*z*b*a^-1
];
mats := [
  # a  (AD in the source file)
  [ [ (g*zeta^3-g*zeta^2-g*zeta-zeta+g+1)/3, (-2*g*zeta^5-3*zeta^5+2*g*zeta^4+2*zeta^4-2*g*zeta^3+zeta^3-3*g*zeta^2-zeta^2+2*g*zeta+2*zeta-3*g-1)/3, (-2*g*zeta^5-zeta^5+g*zeta^4+2*zeta^4-g*zeta^3-g*zeta^2-zeta^2+2*g*zeta+zeta-2*g-1)/3 ],
    [ (-g*zeta^5-zeta^5-2*g*zeta^4-zeta^4-2*g*zeta^3-zeta^3-2*g*zeta^2-zeta^2-g*zeta-2*zeta-g)/3, (g*zeta^5-g*zeta^4-zeta^4+g*zeta^3+g*zeta^2+g+1)/3, (3*g*zeta^5+zeta^5-2*g*zeta^3+zeta^3+g*zeta^2-2*zeta^2-2*g*zeta-2*zeta-3*g-1)/3 ],
    [ (3*g*zeta^5+2*zeta^5+g*zeta^4-3*g*zeta^3-zeta^3+g*zeta^2+3*zeta^2+3*g*zeta+zeta-2*g+1)/3, (2*g*zeta^5+zeta^5+g*zeta^4-zeta^4-2*g*zeta^3-zeta^3+g*zeta^2+2*g*zeta+zeta-g)/3, (-g*zeta^5+g*zeta^4+zeta^4+g*zeta^3+g*zeta+zeta+g+1)/3 ] ]*one,
  # b  (BD in the source file)
  [ [ (-g*zeta^4+zeta^3-g*zeta-zeta-g)/3, (-zeta^5+zeta^4-2*g*zeta^3+g*zeta^2+zeta^2-g*zeta+zeta-g+1)/3, (g*zeta^5+zeta^5-2*zeta^4+g*zeta^3+zeta^3+g*zeta^2+2*zeta^2-2*zeta+3*g)/3 ],
    [ (2*g*zeta^4-zeta^4+g*zeta^3+3*zeta^3+2*g*zeta^2+g*zeta+1)/3, (-zeta^4+zeta^3+g*zeta-g)/3, (-g*zeta^5-zeta^5-g*zeta^4-2*g*zeta^3-g*zeta^2-2*zeta^2-zeta-g+1)/3 ],
    [ (2*g*zeta^4+g*zeta^3-zeta^3-4*g*zeta^2+2*g*zeta-2*zeta+2*g+3)/6, (-2*g*zeta^5-g*zeta^4+zeta^4+g*zeta^3+3*zeta^3-2*g*zeta^2-2*g*zeta+zeta+1)/3, (g*zeta^4+zeta^4+zeta^3+zeta-g)/3 ] ]*one,
  # z  (ZD in the source file)
  [ [ zeta, 0, 0 ],
    [ 0, zeta^4, 0 ],
    [ 0, 0, -zeta^4-zeta ] ]*one
];
Add(FakeProjectivePlaneGroups, rec(
  name := "C2, p=2, T1={3}",
  fieldGens:=[[1/17*t^9-38/17,4/17*t^9+t^6+4*t^3-16/17,
    21/34*t^11+1/34*t^10+5/2*t^8+21/2*t^5-42/17*t^2-55/34*t],
    ["ER(5)","E(3)","EY(9)"]],
  csName := "(C2,p=2,\\{3\\})",
  k := "Q(sqrt(5))", ell := "Q(sqrt(5))(sqrt(-3))", p := 2, T1 := "{3}",
  N := 9, numberOfFakePlanes := 1,
  presentation := G, matrix := mats, field := F, form := form, conj := conj,
  fakePlanes := [
    rec(name := "(C2,p=2,\\{3\\},d_3 D_3)",
        generators := List([a, z*a*z^-1, z^-1*a*z], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 9, abInv := [ 7 ]) ] ));
end, []);

#############################################################################
##  k = Q(sqrt(2)),  ell = Q(sqrt(2))(sqrt(-5+2*sqrt(2))),  p = 2
##  Field generators: h^2 = 2; U^2 = (1+h)*U-2; W^3 = 3*W-1
##  (conj: h -> h, U -> 1+h-U, W -> W)
CallFuncList(function()
local x, F, t, tbar, conj, form, f, G, mats, H, subgens, one, h, U, W, a, b, c;
x := Indeterminate(Rationals, "x");
F := FieldExtension(Rationals, x^12-6*x^11+27*x^10-102*x^9+306*x^8-432*x^7+783*x^6-756*x^5+324*x^4+432*x^3+2592*x^2+5184);
one := One(F);
t := RootOfDefiningPolynomial(F);   # t = U*W+U
h := (11/290016*t^11-91/145008*t^10+2839/870048*t^9-35/2544*t^8+785/16112*t^7-2245/18126*t^6+15103/96672*t^5-1117/4028*t^4+398/3021*t^3+385/1007*t^2-423/2014*t-557/1007)*one;
U := (-76951/273920112*t^11+180503/136960056*t^10-211489/43250544*t^9+252463/15217784*t^8-621149/15217784*t^7-251425/17120007*t^6-20431/1722768*t^5+98561/3804446*t^4+171700/5706669*t^3+370550/1902223*t^2-2077533/1902223*t+146112/1902223)*one;
W := (-1477/91306704*t^11-187427/821760336*t^10+99307/91306704*t^9-122207/30435568*t^8+81536/5706669*t^7-620687/15217784*t^6-945969/30435568*t^5-1323/1601872*t^4+189387/7608892*t^3+211761/7608892*t^2+351969/1902223*t-3474352/1902223)*one;
tbar := (-14039/45653352*t^11+251585/136960056*t^10-1166789/136960056*t^9+1478477/45653352*t^8-3352763/34240014*t^7+1112699/7608892*t^6-4245855/15217784*t^5+9300499/45653352*t^4-382891/3804446*t^3-419025/3804446*t^2-2937829/3804446*t+326850/1902223)*one;   # image of t under conj
conj := e -> ValuePol(ExtRepOfObj(e), tbar);
form := [ [ W^2-h*W+W-h, 0, 0 ],
          [ 0, h*W^2-W^2+h*W-3*h+4, 0 ],
          [ 0, 0, -h*W^2-W+h+2 ] ]*one;

# C10, p=2, T1={}   [(C10,p=2,\emptyset)]
f := FreeGroup("a", "b", "c");
a := f.1;
b := f.2;
c := f.3;
G := f / [
  b^3,
  (b*a^-1)^3,
  c^-1*a*b*c^-2*a^3*c*a^-1*b^-1,
  a*c*b^-1*c*a^-1*b^-1*a^-1*c^-1*b*a*c^-1*b,
  c^-1*b*a^-1*b^-1*c^-1*a*b^-1*a*c^-1*a^-2*b*c^-1,
  c^-1*b*a^-1*b^-1*a*b*a*c^-1*a^-1*c^2*b^-1*a^-1,
  a^-1*b*a*b^-1*c*a^-1*b^-1*c*a*c*a^-1*b^-1*c*b^-1,
  c^2*b^-1*a^-1*c^-1*a^3*c*b^-1*c^2*b^-1*a^-1,
  c*b^-1*c*a^-1*b^-1*c^-1*a*c*a^-1*b^-1*c^-1*a^-2*c,
  c*b^-1*a^-1*c*b^-1*a^-1*b*a^2*c*a^-1*b^-1*c*b^-1*a^-1,
  c*b^-1*a^-1*c^-1*b*a*c*b^-1*a^3*b*c^-2*a*c,
  a^2*c*b*a*c^-1*a*c*a^-1*b^-1*c^-2*b*a*c*b^-1
];
mats := [
  # a  (AA in the source file)
  [ [ (-2*h*U*W^2-2*U*W^2+2*h*W^2+3*W^2-h*U*W-U*W+h*W+7*h*U+7*U-7*h-12)/9, (4*h*U*W^2+3*U*W^2-3*h*W^2-11*W^2+5*h*U*W+6*U*W-9*h*W-10*W-5*h*U+10)/9, (U*W^2+2*h*W^2+W^2-U*W+h*W+5*W-3*h*U-5*U+2*h+1)/9 ],
    [ (-2*h*U*W^2-h*W^2-h*U*W+3*U*W-2*h*W+h*U+5*h+6)/9, (h*U*W^2+U*W^2-h*W^2-h*U*W-U*W+h*W+3*W+h*U+U-h-6)/9, (-5*h*U*W^2-6*U*W^2+9*h*W^2+10*W^2-h*U*W-3*U*W+6*h*W-W+13*h*U+18*U-24*h-32)/9 ],
    [ (3*h*U*W^2-2*U*W^2-3*h*W^2-2*W^2-4*U*W+3*h*W+8*W-6*h*U+7*U-2)/9, (h*U*W^2-3*U*W^2+2*h*W^2-h*U*W-3*U*W+h*W-5*h*U+6*U-h+6)/9, (h*U*W^2+U*W^2-h*W^2-3*W^2+2*h*U*W+2*U*W-2*h*W-3*W+h*U+U-h)/9 ] ]*one,
  # b  (BB in the source file)
  [ [ (-h*U*W^2-2*U*W^2-2*W^2-2*h*U*W-4*U*W+3*h*W+2*W+2*h*U+4*U+4)/9, (-h*U*W^2+3*U*W^2-2*h*W^2-2*W^2+h*U*W-4*h*W-W+2*h*U-6*U+4*h-2)/9, (2*h*W^2+2*W^2+h*W+4*W-h-4)/9 ],
    [ (-2*h*U*W^2-U*W^2-h*U*W+U*W+4*h*U+5*U)/9, (2*h*U*W^2+4*U*W^2-3*h*W^2-2*W^2+h*U*W+2*U*W-3*h*W-4*W-4*h*U-8*U+6*h+4)/9, (-h*U*W^2+4*h*W^2+W^2-2*h*U*W+3*U*W+2*h*W-W+2*h*U-8*h-8)/9 ],
    [ (2*h*U*W^2-6*U*W^2+6*h*W^2-8*W^2+h*U*W+6*h*W-4*W-10*h*U+12*U-12*h+16)/18, (h*U*W^2-U*W^2-h*U*W-2*U*W-2*h*U+5*U)/9, (-h*U*W^2-2*U*W^2+3*h*W^2+4*W^2+h*U*W+2*U*W+2*W+2*h*U+4*U-6*h-8)/9 ] ]*one,
  # c  (CC in the source file)
  [ [ (-3*h*U*W^2-4*U*W^2+3*h*W^2+3*W^2-3*h*U*W-5*U*W+3*h*W+3*W+9*h*U+11*U-9*h-9)/9, (3*h*U*W^2+4*U*W^2-h*W^2-4*W^2+6*h*U*W+5*U*W-2*h*W-5*W-3*h*U+U-4*h+5)/9, (4*h*U*W^2+5*U*W^2-8*h*W^2-9*W^2+2*h*U*W+4*U*W-4*h*W-12*W-8*h*U-13*U+13*h+21)/9 ],
    [ (2*h*U*W^2-2*U*W^2+4*h*W^2+4*W^2+4*h*U*W-U*W-h*W-4*W-4*h*U-2*U-5*h-8)/9, (3*h*U*W^2+5*U*W^2-3*h*W^2-3*W^2+U*W-3*h*U-7*U+3*h+3)/9, (-6*h*U*W^2-5*U*W^2+2*h*W^2+5*W^2-3*h*U*W-U*W+h*W+W+15*h*U+19*U-10*h-13)/9 ],
    [ (3*h*U*W^2+3*U*W^2-h*W^2-6*W^2-3*h*U*W-6*U*W+4*h*W+6*W-7*h+6)/9, (-4*h*U*W^2+U*W^2+h*W^2+4*W^2-2*h*U*W-U*W+5*h*W+8*W+8*h*U-8*U+h-8)/9, (-U*W^2+3*h*U*W+4*U*W-3*h*W-3*W+3*h*U+5*U-3*h-3)/9 ] ]*one
];
Add(FakeProjectivePlaneGroups, rec(
  name := "C10, p=2, T1={}",
  csName := "(C10,p=2,\\emptyset)",
  k := "Q(sqrt(2))", ell := "Q(sqrt(2))(sqrt(-5+2*sqrt(2)))", p := 2, T1 := "{}",
  N := 3, numberOfFakePlanes := 1,
  presentation := G, matrix := mats, field := F, form := form, conj := conj,
  fakePlanes := [
    rec(name := "(C10,p=2,\\emptyset,D_3)",
        generators := List([a, c, b^-1*c*b], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 3, abInv := [ 2, 7 ]) ] ));

# C10, p=2, T1={17-}   [(C10,p=2,\{17-\})]
f := FreeGroup("a", "b", "c");
a := f.1;
b := f.2;
c := f.3;
G := f / [
  (b*a^-1)^3,
  (b*c^-1)^3,
  c^-1*b*a^-2*b*c*b^-1*a^2*b^-1,
  b*a*b^-1*c*b^-1*a^-2*b^2*c^-1*b^2*c^-1,
  a^-1*b*a^-2*b*a^-2*c*a^3*b^-1*c*b^-1,
  a*b^2*a^3*b^-1*c^2*b^-1*c^-1*b*c^-1*b^-1*c,
  b^-1*a^2*b^-2*a^2*b^-1*c*b^-1*a^2*b^-1*c^4,
  b*a*c^-1*b*c^-1*b^-1*c*a*b*a^-1*b*c*b^-1*c*a^-3*b*c^-1,
  a*b*a*b^-1*c*b^-2*a*b*a*c^-1*b*c^-1*b^-1*a*b*a*c^-1*b*c^-1*b^-1,
  a*b^-1*c*a^2*b^-2*a^-1*b*a^-2*c*a*b^3*a^-2*c*b^-1*a
];
mats := [
  # a  (AD in the source file)
  [ [ (24*h*U*W^2+26*U*W^2-59*h*W^2-71*W^2-30*h*U*W-41*U*W+44*h*W+59*W-99*h*U-103*U+169*h+193)/153, (26*h*U*W^2+31*U*W^2-37*h*W^2-33*W^2+58*h*U*W+77*U*W-59*h*W-105*W-31*h*U-35*U+50*h+57)/153, (-15*h*U*W^2-63*U*W^2+73*h*W^2+21*W^2-42*h*U*W-3*U*W-37*h*W+69*W+60*h*U+99*U-122*h-237)/153 ],
    [ (9*h*U*W^2+82*U*W^2-3*h*W^2-84*W^2-27*h*U*W+77*U*W+60*h*W-54*W-99*h*U-137*U+33*h+108)/153, (30*h*U*W^2+41*U*W^2-44*h*W^2-59*W^2+54*h*U*W+67*U*W-103*h*W-130*W-111*h*U-133*U+139*h+169)/153, (-58*h*U*W^2-77*U*W^2+59*h*W^2+105*W^2-32*h*U*W-46*U*W+22*h*W+72*W+137*h*U+181*U-142*h-219)/153 ],
    [ (19*h*U*W^2+56*U*W^2-46*h*W^2-64*W^2-25*h*U*W-20*U*W+31*h*W+52*W-8*h*U-88*U+65*h+86)/153, (27*h*U*W^2-77*U*W^2-60*h*W^2+54*W^2+36*h*U*W+5*U*W-63*h*W-30*W-135*h*U+181*U+147*h-168)/153, (-54*h*U*W^2-67*U*W^2+103*h*W^2+130*W^2-24*h*U*W-26*U*W+59*h*W+71*W+57*h*U+83*U-155*h-209)/153 ] ]*one,
  # b  (BD in the source file)
  [ [ (-21*h*U*W^2-61*U*W^2+24*h*W^2+26*W^2-12*h*U*W-47*U*W+21*h*W+10*W+93*h*U+173*U-99*h-154)/153, (41*h*U*W^2+60*U*W^2-59*h*W^2-3*W^2+64*h*U*W+126*U*W-61*h*W-144*W+8*h*U-48*U+37*h-69)/153, (11*h*U*W^2+2*U*W^2+19*h*W^2-12*W^2+7*h*U*W+43*U*W-25*h*W-3*W+41*h*U+26*U-59*h-54)/153 ],
    [ (-27*h*U*W^2-25*U*W^2+43*h*W^2+14*W^2-21*h*U*W+7*U*W+41*h*W-8*W+93*h*U+122*U-116*h-154)/153, (12*h*U*W^2+47*U*W^2-21*h*W^2-10*W^2-9*h*U*W-14*U*W+3*h*W+16*W+27*h*U-43*U-9*h-82)/153, (-64*h*U*W^2-126*U*W^2+61*h*W^2+144*W^2-23*h*U*W-66*U*W+2*h*W+141*W+218*h*U+324*U-203*h-363)/153 ],
    [ (-29*h*U*W^2+174*U*W^2-132*h*W^2-92*W^2-139*h*U*W-84*U*W+120*h*W+164*W+235*h*U-186*U+120*h-176)/306, (21*h*U*W^2-7*U*W^2-41*h*W^2+8*W^2-6*h*U*W-32*U*W+2*h*W+22*W-3*h*U+86*U+52*h-142)/153, (9*h*U*W^2+14*U*W^2-3*h*W^2-16*W^2+21*h*U*W+61*U*W-24*h*W-26*W+33*h*U+23*U-45*h-70)/153 ] ]*one,
  # c  (CD in the source file)
  [ [ (5*h*U*W^2+4*U*W^2+21*h*W^2+44*W^2-2*h*U*W-22*U*W+12*h*W-38*W+41*h*U+94*U-144*h-241)/153, (72*h*U*W^2+61*U*W^2-58*h*W^2-111*W^2+90*h*U*W+89*U*W-98*h*W-177*W-78*h*U+43*U-25*h+99)/153, (-h*U*W^2+6*U*W^2+23*h*W^2+32*W^2+55*h*U*W+78*U*W-41*h*W-128*W+89*h*U+129*U-211*h-247)/153 ],
    [ (-30*h*U*W^2-92*U*W^2+78*h*W^2+110*W^2-12*h*U*W-64*U*W+72*h*W+112*W+126*h*U+247*U-297*h-394)/153, (2*h*U*W^2+22*U*W^2-12*h*W^2+38*W^2+7*h*U*W+26*U*W+9*h*W+82*W+47*h*U+58*U-78*h-229)/153, (-90*h*U*W^2-89*U*W^2+98*h*W^2+177*W^2-18*h*U*W-28*U*W+40*h*W+66*W+246*h*U+343*U-337*h-477)/153 ],
    [ (-h*U*W^2+6*U*W^2-28*h*W^2-36*W^2-47*h*U*W-75*U*W+61*h*W+144*W+89*h*U+78*U-109*h-60)/153, (12*h*U*W^2+64*U*W^2-72*h*W^2-112*W^2-18*h*U*W-28*U*W+6*h*W-2*W+42*h*U-65*U+3*h+50)/153, (-7*h*U*W^2-26*U*W^2-9*h*W^2-82*W^2-5*h*U*W-4*U*W-21*h*W-44*W+65*h*U+154*U-84*h+11)/153 ] ]*one
];
Add(FakeProjectivePlaneGroups, rec(
  name := "C10, p=2, T1={17-}",
  csName := "(C10,p=2,\\{17-\\})",
  k := "Q(sqrt(2))", ell := "Q(sqrt(2))(sqrt(-5+2*sqrt(2)))", p := 2, T1 := "{17-}",
  N := 3, numberOfFakePlanes := 1,
  presentation := G, matrix := mats, field := F, form := form, conj := conj,
  fakePlanes := [
    rec(name := "(C10,p=2,\\{17-\\},D_3)",
        generators := List([a, b*a*b^-1, b*c*b^-1], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 3, abInv := [ 7 ]) ] ));
end, []);

#############################################################################
##  k = Q(sqrt(6)),  ell = Q(sqrt(6))(sqrt(-3)),  p = 3
##  Field generators: h^2 = 6; zeta^6 = -zeta^3-1
##  (conj: h -> h, zeta -> zeta^8)
CallFuncList(function()
local x, F, t, tbar, conj, form, f, G, mats, H, subgens, one, h, zeta, a, b, c, z;
x := Indeterminate(Rationals, "x");
F := FieldExtension(Rationals, x^12+216*x^6+46656);
one := One(F);
t := RootOfDefiningPolynomial(F);   # t = h*zeta
h := (1/1296*t^9)*one;
zeta := (1/7776*t^10)*one;
tbar := (-1/7776*t^11-1/36*t^5)*one;   # image of t under conj
conj := e -> ValuePol(ExtRepOfObj(e), tbar);
form := [ [ -h*zeta^5-h*zeta^4-h+3, 0, 0 ],
          [ 0, h*zeta^4-h*zeta^2+h*zeta-h+3, 0 ],
          [ 0, 0, h*zeta^5+h*zeta^2-h*zeta-h+3 ] ]*one;

# C18, p=3, T1={}   [(C18,p=3,\emptyset)]
f := FreeGroup("a", "b", "z");
a := f.1;
b := f.2;
z := f.3;
G := f / [
  z^3,
  (b*z)^3,
  a^2*z*b*z^-1*a*z^-1*a^3*b^-1*a*z,
  a^-1*z^-1*b*z*a^-1*z^-1*b*z*a^-1*b,
  b*a^-1*b*a^-2*z*b^-2*z*a*z^-1*a*z^-1,
  z*a*z*a^2*b^-1*a*z*a^-1*z*a^-1*z^-1*b,
  b*z*a^-1*b^-1*z*a^-1*z*b^-1*z*a^-1*z^-1*b,
  b^-1*a^-1*b*a^-2*b*z^-1*a*z^-1*a*z^-1*b^-1,
  z^-1*a^-1*b*a^-2*z^-1*b^-2*z*a^-1*b^-1*z*a*b^-1,
  b*a^-1*z^-1*b*a*z^-1*b^-1*z*a^-1*b*z^-1*a*z^-1*b*a^-1,
  b^-1*z*a^-1*z*b^-1*z*a*z^-1*b^-2*z*a^2*z^-1*b^-2*z*a
];
mats := [
  # a  (AA in the source file)
  [ [ (-h*zeta^5-h*zeta^4+2*h*zeta^3+3*zeta^3+h*zeta^2+3*zeta^2+h*zeta+3*zeta+h)/9, (3*h*zeta^5+9*zeta^5-h*zeta^4-12*zeta^4+4*h*zeta^3+6*zeta^3+3*h*zeta^2-2*h*zeta-12*zeta+5*h+9)/9, (-2*h*zeta^5-6*zeta^5+5*h*zeta^4+12*zeta^4-4*h*zeta^3-9*zeta^3+2*h*zeta^2+3*zeta^2+h*zeta-2*h-6)/9 ],
    [ (-h*zeta^5-3*zeta^5-2*h*zeta^4-4*zeta^4-h*zeta^3-3*zeta^3-h*zeta^2-3*zeta^2-h*zeta-2*zeta)/3, (-h*zeta^5-3*zeta^5+2*h*zeta^4+3*zeta^4+2*h*zeta^3+3*zeta^3-2*h*zeta^2-3*zeta^2+h*zeta+h)/9, (-3*h*zeta^5-h*zeta^4+4*h*zeta^3+6*zeta^3+9*zeta^2+h*zeta+12*zeta+5*h+9)/9 ],
    [ (-5*h*zeta^5-3*zeta^5+4*h*zeta^4+4*h*zeta^3+12*zeta^3-4*h*zeta^2-3*zeta^2-h*zeta-6*zeta+2*h+9)/9, (h*zeta^5+3*zeta^5+h*zeta^4+2*zeta^4-h*zeta^3-3*zeta^3+2*h*zeta+4*zeta)/3, (2*h*zeta^5+3*zeta^5-h*zeta^4-3*zeta^4+2*h*zeta^3+3*zeta^3+h*zeta^2-2*h*zeta-3*zeta+h)/9 ] ]*one,
  # b  (BB in the source file)
  [ [ (2*h*zeta^4+3*zeta^4+h*zeta^3+3*zeta^3+h*zeta+3*zeta-h)/9, (-2*h*zeta^5-6*zeta^5+h*zeta^4+9*zeta^4-2*h*zeta^3-3*zeta^3-h*zeta^2-h*zeta+3*zeta-h-3)/9, (h*zeta^5+9*zeta^5-5*h*zeta^4-3*zeta^4+h*zeta^3+9*zeta^3-h*zeta^2+6*zeta^2-4*h*zeta+2*h+6)/9 ],
    [ (-h*zeta^5+6*zeta^5+4*h*zeta^4+3*zeta^4+4*h*zeta^3+3*zeta^3+h*zeta^2+9*zeta^2+2*h*zeta+9*zeta+2*h)/9, (-h*zeta^4+h*zeta^3+3*zeta^3-2*h*zeta-3*zeta-h)/9, (h*zeta^5-2*h*zeta^4-6*zeta^4-2*h*zeta^3-3*zeta^3-h*zeta^2-6*zeta^2-h*zeta-9*zeta-h-3)/9 ],
    [ (3*h*zeta^5+4*zeta^5+7*zeta^4-h*zeta^3-5*zeta^3+2*h*zeta^2+2*zeta^2+2*h*zeta+8*zeta-1)/9, (-h*zeta^5-9*zeta^5-2*h*zeta^4+6*zeta^4+4*h*zeta^3+3*zeta^3-2*h*zeta^2-3*zeta^2-4*h*zeta-3*zeta+2*h)/9, (-h*zeta^4-3*zeta^4+h*zeta^3+3*zeta^3+h*zeta-h)/9 ] ]*one,
  # z  (ZZ in the source file)
  [ [ zeta, 0, 0 ],
    [ 0, zeta^4, 0 ],
    [ 0, 0, -zeta^4-zeta ] ]*one
];
Add(FakeProjectivePlaneGroups, rec(
  name := "C18, p=3, T1={}",
  csName := "(C18,p=3,\\emptyset)",
  k := "Q(sqrt(6))", ell := "Q(sqrt(6))(sqrt(-3))", p := 3, T1 := "{}",
  N := 9, numberOfFakePlanes := 1,
  presentation := G, matrix := mats, field := F, form := form, conj := conj,
  fakePlanes := [
    rec(name := "(C18,p=3,\\emptyset,d_3 D_3)",
        generators := List([a, z*a*z^-1, b*z*a*z^-1*b^-1], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 9, abInv := [ 2, 2, 13 ]) ] ));

# C18, p=3, T1={2I}   [(C18,p=3,\{2I\})]
# the subgroup of the group above generated by b*z*a^-1*b^-1, z*b*z^-1, b^-1*z*b^-1
subgens := List([b*z*a^-1*b^-1, z*b*z^-1, b^-1*z*b^-1], w -> MappedWord(w, GeneratorsOfGroup(f), mats));
H := CallFuncList(function()
  local fs, s1, s2, s3;
  fs := FreeGroup("s1", "s2", "s3");
  s1 := fs.1;
  s2 := fs.2;
  s3 := fs.3;
  return fs / [
    s3*s1^-1*s3^-1*s1^2*s3^-1*s2*s3*s1^-1*s3*s1^-3*s2*s1^-1,
    s2*s3*s1^-1*s3^-1*s2^-1*s3*s1*s3^-1*s2^-1*s1^2*s3^-1*s1^3*s3^-1,
    s2^-3*s3*s1*s3^-1*s2^-3*s3*s1*s3^-1*s2^-1*s1*s3^-1*s1^2*s3^-1,
    s1^-1*s2*s3*s1^-1*s3^-1*s2^2*s3*s1^-3*s2*s3^2*s1^-3*s2*s1^2*s3^-1*s2*s3,
    s2*s3*s1^-1*s3^-1*s2^4*s3*s1^-2*s3*s1^-3*s2*s3*s1^-3*s2*s3^-1*s2^-1*s1^3*s3^-2,
    s1^3*s3^-1*s2^-2*s3*s1*s3^-1*s2^-1*s3^-1*s2*s3^2*s1^-3*s2*s3*s2^-1*s1^3*s3^-1*s1^-1*s3*s1^-1*s3^-1*s1^2*s3^-1,
    s1*s3^-1*s1*s3^-1*s1^-1*s3*s1^-2*s2*s3*s1^-3*s2*s3*s1^-3*s2*s3^-1*s1^2*s3^-1*s2*s3*s2^-1*s1^3*s3^-1*s1^-1*s3,
    s1^2*s3^-1*s2*s3*s1^-1*s3^-1*s2*s3*s1^-3*s3*s1^-2*s2^-2*s3*s1*s3^-1*s2^-1*s1^-1*s2*s3*s1^-3*s2*s3^-1*s2^-1*s3*s1^-2*s3^2*s1^-3*s2*s1^2*s3^-1*s2*s3,
    s1*s3^-1*s2*s3*s1^-1*s3^-1*s2*s1^2*s3^-1*s1^3*s3^-1*s2^2*s3*s1^-1*s3^-1*s2^-1*s3*s1^-2*s2*s3*s1^-3*s2*s1^2*s3^-1*s2*s3*s1^-1*s3^-1*s2*s3^2*s1^-3*s2*s1^-1*s3,
    s2^-2*s3*s1*s3^-1*s2^-2*s1^2*s3^-1*s2^4*s3*s1^-2*s3*s1^-1*s3^-1*s2*s3*s1^-3*s2*s3*s1*s3^-1*s1*s2^-1*s1*s2*s3*s1^-1*s3^-1*s2^2*s1^2*s3^-1*s1^3*s3^-1,
    s1*s2^-1*s3*s1^-2*s2^-1*s1^3*s3^-1*s2^-1*s1^2*s3^-1*s2^4*s3*s1^-2*s3*s1^-1*s3^-1*s2^-1*s3*s2*s3*s1^-1*s3^-1*s2^2*s3^-1*s1^2*s3^-1*s1^3*s3^-1*s2^-2*s3*s1*s3^-1*s2^-1*s3^-1,
    s3^-1*s1^2*s3^-1*s2*s3*s1*s3^-1*s2^-4*s3*s1*s3^-1*s2^-1*s3*s2^-2*s3*s1*s3^-1*s2^-1*s3^-1*s2*s3^2*s1^-3*s3*s1^-2*s2^-1*s1^3*s3^-1*s2^-2*s3*s1*s3^-1*s2^-1*s3*s1^-2,
    s2^-1*s1^2*s3^-1*s2*s3*s1*s3^-1*s2^-4*s3*s1*s3^-1*s2^-1*s3*s1^-3*s2*s1^2*s3^-1*s1^3*s3^-2*s2^-1*s3*s1^-2*s2*s3*s1^-3*s2*s3^-1*s2^-1*s1^3*s3^-1*s2^-1*s1^3*s3^-1,
    s2^-1*s3*s1*s3^-1*s1^2*s3^-1*s2^-4*s3*s1^-2*s2^-1*s3*s1*s3^-1*s2^-1*s3*s1^-1*s3^-1*s1*s3*s1^-3*s2*s3^-1*s2^-1*s3*s1^-2*s3*s1^2*s3^-1*s1^2*s3^-1*s1*s2^-1*s3*s1^-2*s2^-1*s1^3*s3^-1,
    s3^-1*s2*s1^2*s3^-1*s2*s3^2*s1^-3*s2*s1^2*s3^-1*s2*s1*s2^-1*s1^2*s3^-1*s2^4*s3*s1^-2*s3*s1^-1*s3^-1*s2^-1*s3*s1*s3^-1*s2^-1*s3*s1^-2*s3^-1*s1^2*s3^-1*s2*s3*s2^-1*s1^3*s3^-1*s1^-1*s3*s1*s3^-1,
    s3*s1^-2*s3*s1^-2*s2*s1*s3^-1*s2^-1*s3*s1^-2*s3*s1^-2*s2*s1^-1*s2^-1*s3*s1^-2*s3*s1^-1*s2*s1^2*s3^-1*s2^-4*s3*s1*s3^-1*s2^-1*s3*s1*s3^-1*s1*s3*s1^-3*s2*s3^-1*s2^-1*s1^2*s3^-1*s1^2*s3^-1*s2^-1,
    s3^-1*s1^3*s3^-1*s2^-2*s3*s1*s3^-1*s2^-1*s3*s1^-1*s3^-1*s2^-4*s3*s1*s3^-1*s2^-2*s3*s1*s3^-1*s2^-1*s3*s1^-2*s2^-1*s1^3*s3^-1*s1*s3^-1*s1*s2^-1*s1^2*s3^-1*s1*s2^-1*s3*s1^-2*s2^-1*s1^2*s3^-1*s2^4*s3*s1^-2*s3*s1^-1,
    s1^-1*s3*s1*s3^-1*s1*s3^-1*s1^2*s3^-1*s2^-4*s3*s1^-2*s2*s3^-1*s2^-1*s1^3*s3^-1*s1*s3^-1*s1*s3*s1^-3*s2^2*s3*s1^-1*s3^-1*s2^2*s3*s1^-3*s3*s1^-2*s2^-1*s3*s1*s3^-1*s2^-1*s3*s1^-2*s3*s1^-1*s3^-1*s2^4*s3*s1^-2*s2^-1*s3*s1^-3*s3*s1^-1*s3^-1,
    s2^-1*s1*s3*s1^-1*s2*s3*s1^-1*s3^-1*s2^2*s1^-1*s2*s3*s1^2*s3^-1*s2*s3*s1^-1*s3^-1*s2*s1^2*s3^-1*s2*s3*s1*s3^-1*s2^-4*s3*s1*s3^-1*s2^-1*s3*s1^-1*s3^-1*s2^4*s3*s1^-2*s3*s1^-1*s3^-1*s2*s3*s1^2*s3^-1*s1^2*s3^-1*s2^-1*s3*s1^-2*s3*s1^-2*s2*s3*s1^-3*s2*s3^-1*s2^-1*s3*s1^-2,
    s1*s3^-1*s2^-4*s3*s1*s3^-1*s2^-2*s3*s1*s3^-1*s1^-1*s3*s1^-2*s2*s1^-1*s3*s1^-2*s3*s1^-1*s3^-1*s1^2*s3^-1*s2^-3*s3*s1^-2*s2*s3*s2^-2*s3*s1*s3^-1*s2^-1*s3^-1*s2^2*s3*s1^-1*s3^-1*s2^4*s3*s1*s3^-1*s2*s3*s1^-1*s3^-1*s2*s1^2*s3^-1*s1^3*s3^-1*s2^-2*s3*s1*s3^-1*s2^-1*s3^-1*s2,
    s2*s3*s1^-1*s3^-1*s2^2*s3^-1*s2^-1*s1*s3*s1*s3^-1*s1^3*s3^-1*s2*s1^2*s3^-1*s2^-4*s3*s1*s3^-2*s2^-1*s3*s1^-1*s3^-1*s1^2*s3^-1*s2^-3*s3*s1^-2*s3*s1^-2*s2^-2*s3*s1*s3^-1*s2^-1*s1^-1*s2*s3*s1^-3*s2*s1*s3^-1*s2^-4*s3*s1*s3^-1*s2^-2*s3*s2*s3*s1^-1*s3^-1*s2^2*s3^-1*s2^-1*s3,
    s1*s3^-1*s2^-4*s3*s1^-2*s2*s1^2*s3^-1*s2*s3*s2^-1*s1^3*s3^-1*s2^-1*s1^3*s3^-1*s1*s2^-1*s1^5*s3^-1*s2*s3*s1^-1*s3^-1*s2*s3*s1*s3^-1*s1*s3*s1^-3*s2*s3^-1*s2^-1*s1^3*s3^-1*s1^-1*s3^-1*s2^4*s3*s1^-2*s2^-1*s1*s3^-1*s1^-1*s3*s1^-2*s3*s1^-2*s2^-1*s1^3*s3^-1*s1^-1*s3*s1^-3*s2,
    s2*s3*s1^-1*s3^-1*s2^2*s3*s1^-1*s3^-1*s2^-1*s3*s1^-2*s2*s3*s1^-3*s2*s1^2*s3^-1*s2*s3*s1^-3*s2*s1*s3^-1*s2^-4*s3*s1^-2*s2*s1^2*s3^-1*s2*s1*s3^-1*s2*s3*s1^-2*s3*s1^-1*s3*s1^-3*s2*s3^2*s1^-1*s3^-1*s2^4*s3*s1^-2*s3*s1^-1*s3^-1*s1^3*s3^-2*s2^-1*s1^3*s3^-1*s2*s3*s1^-1*s3^-1*s2^3,
    s1^2*s3^-1*s1*s3*s1^-1*s3^-1*s2*s3^2*s1^-3*s2*s3*s1^-1*s2^-1*s3*s1^-2*s2^-1*s1^3*s3^-2*s2^-1*s3*s1^-2*s2^-1*s3*s2*s3*s1^-1*s3^-1*s2^2*s3^-1*s2^-1*s3*s1^2*s3^-1*s1^3*s3^-1*s2*s1^2*s3^-1*s2^-4*s3*s1*s3^-1*s1^2*s3^-1*s2*s3*s1^-1*s3^-1*s2^2*s3*s1^-1*s3^-1*s2^7*s3*s1^-2*s3*s1^-1*s2^-2*s3*s1*s3^-1*s2^-1*s1*s3^-1*s2^-1,
    s2^2*s3*s1^-2*s2^-4*s3*s1*s3^-1*s2^-2*s3*s2*s3*s1^-1*s3^-1*s2^2*s3*s1^-3*s2*s1^2*s3^-1*s2*s3*s2^-1*s1^3*s3^-1*s2^-1*s3*s1^-2*s2^-1*s3*s1*s3^-1*s1^2*s3^-1*s2^-4*s3*s1^-2*s2*s1^2*s3^-1*s2*s1*s3^-1*s2^-1*s3*s1*s3^-1*s2^-1*s1^3*s3^-1*s1^-1*s3*s1^-1*s3^-1*s2*s3*s1^-3*s2*s1^2*s3^-1*s2*s1^-1*s3*s1^-2*s2*s1*s3^-1*s2*s3*s1^-1*s2^-1*s1^2*s3^-1*s1^2*s3^-1,
    s3^-1*s2^-1*s3*s1^-2*s3*s1^-2*s2*s3*s1^-3*s2*s3*s1^-3*s2*s1^2*s3^-1*s1^2*s3^-1*s1*s3*s1^-1*s3^-1*s2*s1^2*s3^-1*s1^3*s3^-1*s2^-2*s3*s1*s3^-1*s2^-1*s3^-1*s1^2*s3^-1*s2*s3*s1^-2*s3*s1^-1*s3^-1*s2*s3*s1^-3*s2*s1^2*s3^-1*s2*s1^-1*s3*s1^-2*s2*s1*s3^-1*s2*s3*s1*s3^-1*s2*s3*s1^-1*s3^-1*s2^2*s3*s1^-1*s3^-1*s2^4*s3*s1^-1*s3*s1^-2*s3^-1*s2^-1*s1^3*s3^-2*s2^-1*s1*s3*s1^-1*s2*s3*s1^-1*s3^-1*s2^2*s1^2*s3^-1*s2*s1,
    s1^-1*s2^-1*s3*s1*s3^-1*s2^-1*s1*s3^-1*s1^-1*s3*s1*s3^-1*s1^2*s3^-1*s2^-4*s3*s1*s3^-1*s2^-1*s3*s1*s3^-1*s1^2*s3^-1*s2^-2*s3*s1^-2*s3*s1^-2*s3^-1*s2^-1*s3*s1*s3^-1*s1^2*s3^-1*s2^-4*s3*s1*s3^-1*s2^-1*s3*s1*s3^-1*s1*s3*s1^-3*s2*s3^-1*s2^-1*s1*s2^-2*s3*s1*s3^-1*s2^-1*s1*s3^-1*s1^-1*s2*s1^2*s3^-1*s2*s1^-1*s3*s1^-2*s3*s1^-2*s3*s1^-3*s2*s1^2*s3^-1*s2*s1^-1*s3*s1^-2*s2*s1*s3^-1*s2^-1*s3*s1^-2*s2^-1*s3*s1*s3^-1*s2^-1*s1*s3^-1*s1^-1*s3*s1^-2*s2*s1*s3^-1*s2^-4*s3*s1^-1,
    s3^-1*s2^-1*s3*s1^-2*s3*s2*s3*s1^-1*s3^-1*s2^2*s3*s1^-3*s3*s1^-2*s2^-1*s3*s1*s3^-1*s1^2*s3^-1*s1*s3^-1*s1^2*s3^-1*s2^-4*s1^3*s3^-1*s2^-2*s3*s1*s3^-1*s2^-1*s3^-1*s2*s3*s1^-2*s2^-1*s1^3*s3^-2*s1^2*s3^-1*s2^-4*s3*s1^-2*s2*s3^-1*s2^-1*s1^3*s3^-1*s1*s3^-1*s1*s3*s1^-3*s2*s3*s1^-3*s2*s3*s1*s3^-1*s1^2*s3^-1*s2^2*s3*s1^-2*s3*s1^-1*s3*s1^-3*s2*s3^2*s1^-1*s3^-1*s2^4*s3*s1^-1*s2^-1*s1^2*s2*s3*s1^-1*s3^-1*s2^2*s1*s3^-1*s1^2,
    s1^2*s3^-1*s2^-4*s3*s1^-2*s2*s3^-1*s2^-1*s1^3*s3^-1*s1*s3^-1*s1*s3*s1^-3*s2*s1^-1*s2*s3*s1^-3*s2*s3^-1*s2^-1*s3*s1^-2*s2^-1*s3*s1^-2*s2*s3*s1^-3*s2*s3^-1*s2^-1*s1^3*s3^-1*s1*s3^-1*s1^2*s3^-1*s2^-1*s3*s1^-2*s3*s2*s3*s1^-1*s3^-1*s2^2*s3*s1^-3*s3*s1^-2*s2^-1*s3*s2*s3*s1^-1*s3^-1*s2*s3*s1*s3^-1*s1^2*s3^-1*s2^-4*s3*s1^-2*s2^-1*s3*s1*s3^-1*s2^-1*s1*s3^-1*s1^-1*s3*s2*s3*s1^-1*s3^-1*s2^2*s3*s1^-3*s3*s1^-2*s2^-1*s3*s2*s3*s1^-1*s3^-1*s2^2*s3^-1*s1^2*s3^-1*s1^3*s3^-1*s1*s3^-1*s1^2*s3^-1*s2^-3,
    s3^-1*s2*s3*s1^-1*s3^-1*s2^4*s3*s1^-2*s3*s1^-1*s3^-1*s1*s3*s1^-1*s2*s3*s1^-1*s3^-1*s2*s1^2*s3^-1*s2^3*s3*s1^-2*s3*s1*s3^-1*s1*s3^-1*s2^-1*s1^3*s3^-2*s2^-1*s1*s3*s1^-1*s2*s3*s1^-1*s3^-1*s2*s1^3*s3^-1*s1^-1*s3*s1^-3*s2*s3*s1^-3*s2*s3^-1*s2^-1*s3*s1^-2*s2^-1*s1*s3*s1^-1*s2*s3*s1^-1*s3^-1*s2^2*s1^-1*s2*s3*s2^-1*s1^3*s3^-1*s1^-1*s3*s1^-1*s3^-1*s2*s3*s1^-1*s3^-1*s2^4*s3*s1^-2*s3*s1^-1*s3^-1*s2*s3*s1*s2*s3*s1^-1*s3^-1*s2^2*s1^2*s3^-1*s1^3*s3^-1*s2^-1*s3*s1*s3^-1*s2^-1*s3*s1^-1*s3^-1*s1*s2^-1*s1^3*s3^-2*s2^-1*s3*s2*s3*s1^-1*s3^-1*s2^2*s1*s3^-1*s2^-4*s3*s1*s3^-1*s2^-1,
    s1*s3^-1*s2^2*s3*s1^-2*s2^-4*s3*s1*s3^-1*s2^-2*s3*s1*s3^-1*s1*s3^-1*s2^2*s3*s1^-2*s3*s1*s3^-2*s2^-1*s3*s1*s3^-1*s1^2*s3^-1*s2^-4*s3*s1*s3^-1*s2^-1*s3*s1*s3^-1*s1*s3*s1^-3*s2*s3^-1*s2^-1*s1^3*s3^-1*s1*s3^-1*s1^2*s3^-1*s2*s1*s3*s1^-3*s2*s1^-1*s3^-1*s2^-1*s3*s1*s3^-1*s1^2*s3^-1*s2^-4*s3*s1*s3^-1*s2^-1*s3*s1*s3^-1*s1*s3*s1^-3*s2*s3^-1*s2^-1*s1*s2^-2*s3*s1*s3^-1*s2^-1*s1*s3^-1*s1^-1*s2^-1*s3*s1*s3^-1*s2^-1*s1*s3^-1*s1^-1*s3*s2*s3*s1^-1*s3^-1*s2^2*s3*s1^-3*s3*s1^-2*s2^-1*s3*s2*s3*s1^-1*s3^-1*s2^2*s3^-1*s1^2*s3^-1*s1^3*s3^-1*s2^-2*s3*s1*s3^-1*s2^-1*s1^-2*s2,
    s1*s3^-1*s1*s3^-1*s1^2*s3^-1*s2*s3*s1^-1*s3^-1*s2*s3*s1^-1*s3^-1*s2^4*s3*s1^-1*s3^-1*s2^-1*s3*s1^-2*s3*s2^-1*s1^3*s3^-1*s1^-1*s3*s1^-1*s3*s1^-3*s2*s3*s2^-1*s1^3*s3^-1*s2^-1*s1^2*s3^-1*s2*s3*s2*s3*s1^-1*s3^-1*s2^4*s3*s1^-1*s3^-1*s2^2*s3*s1^-1*s3^-1*s2^4*s3*s1^-1*s3*s1^-1*s3^-1*s1*s3*s1^-1*s3^-1*s2^2*s3*s1^-1*s3^-1*s2^4*s3*s1^-1*s2^-1*s3*s2*s3*s1^-1*s3^-1*s2^4*s3*s1^-1*s3^-1*s2^-1*s3^2*s1^-2*s2*s3*s1^-1*s3^-1*s2^2*s1^2*s3^-1*s1^3*s3^-1*s2^-2*s3*s1*s3^-1*s2^-1*s3^-1*s1^2*s3^-1*s2*s3^2*s1^-3*s2*s1^2*s3^-1*s1*s3^-1*s1^-1*s3*s1^-2*s3*s1^-3*s3*s1^-1*s3^-1*s2^-1*s3*s1^-2*s2^-1*s1^3*s3^-1*s2^-1*s1^2*s3^-1*s2^4*s3*s1^-2*s3*s1^-1*s3^-1*s2*s3*s1^-1*s3^-1*s2^4*s3,
    s2*s1*s3^-1*s2^-1*s3*s1^-2*s3*s1^-2*s2*s3*s1^-3*s2*s3*s1^-3*s3*s2*s3*s1^-1*s3^-1*s2^2*s3*s1^-3*s3*s1^-2*s2*s3^-1*s2^-1*s3*s1^-2*s2*s3*s1^-1*s3^-1*s2^4*s3*s1^-1*s3^-1*s2*s3*s1^-2*s3*s1^-1*s3^-1*s2^-1*s1^3*s3^-2*s2^-1*s3*s1*s3^-1*s1^2*s3^-1*s2^-4*s3*s1*s3*s1^-3*s2*s3*s2^-1*s1^3*s3^-1*s1^-1*s3*s1^-1*s3^-1*s2*s1*s3^-1*s2^-4*s3*s1*s3^-1*s2^-2*s3^2*s1^-3*s2*s3*s1^-3*s2*s1^-1*s2*s3*s1^-1*s3^-1*s2^2*s3^-1*s1^2*s3^-1*s1^3*s3^-1*s2^-2*s3*s1*s3^-1*s2^-1*s3^-1*s1^2*s3^-1*s2*s3*s1^-1*s2^-1*s3*s1^-2*s2*s3*s1^-1*s3^-1*s2^3*s3^-1*s2^-1*s3*s1^-2*s2*s3*s1^-3*s2*s3^-1*s2^-1*s1^3*s3^-1*s1*s3^-1*s1*s3*s1^-3*s2*s3^-1*s2^-1*s1^2*s3^-1*s2^3*s3*s1^-2*s3*s1*s3^-1,
    s3^-1*s2*s3^2*s1^-3*s2*s3*s2^-1*s1^3*s3^-1*s2^-1*s1*s2^-2*s3*s1*s3^-1*s2^-1*s1*s3^-1*s1^-1*s2^-1*s3*s1*s3^-1*s2^-1*s1*s3^-1*s1^-1*s3*s1^-2*s2*s1*s3^-1*s2^-1*s3*s1^-2*s3*s2*s3*s1^-1*s3^-1*s2^2*s3*s1^-3*s3*s1^-2*s2^-1*s3*s1*s3^-1*s1*s3^-1*s2*s3*s1*s3^-1*s2*s3*s1^-1*s3^-1*s2^2*s3*s1^-1*s3^-1*s2^4*s3*s1^-1*s3*s1^-2*s3^-1*s2^-1*s1^3*s3^-2*s2^-1*s1^2*s3^-1*s2^3*s3*s1^-2*s3*s1*s3^-1*s2*s1*s3^-1*s2^2*s3*s1^-2*s3*s1^-1*s2^-1*s1^2*s3^-1*s2^3*s3*s1^-2*s3*s1*s3^-2*s1^2*s3^-1*s1^3*s3^-1*s1*s3^-1*s1^2*s3^-1*s2^-4*s1^3*s3^-1*s2^-2*s3*s1*s3^-1*s2^-1*s3^-1*s2*s3*s1*s2^-1*s1^3*s3^-1*s1^-1*s3*s1^-1*s3*s1^-3*s2*s3*s2^-1*s1^3*s3^-1*s2^-1*s1^2*s3^-1*s2*s1^2*s3^-1*s2*s1^-1*s3*s1*s3^-1*s2*s3*s1^-1*s3^-1*s2^2*s3*s1^-1*s3^-1*s2*s3*s1^-1*s3*s1^-1,
    s2*s3*s1^-2*s3*s1^-1*s3*s1^-3*s2*s3^2*s1^-1*s3^-1*s2^4*s3*s1^-2*s3*s1^-1*s3^-1*s2*s1^2*s3^-1*s2*s3*s1^-3*s2*s3^-1*s1^2*s3^-1*s2^-4*s3*s1^-2*s2*s3^-1*s2^-1*s3*s1^-1*s3^-1*s1^2*s3^-1*s2^-3*s3*s1^-2*s3*s1^-2*s2^-1*s3*s1*s3^-1*s2^-1*s3*s1^-1*s3^-1*s1^2*s3^-1*s2^-2*s3*s1^-2*s3*s1*s3^-1*s2*s3*s1^-1*s3^-1*s2*s1^2*s3^-1*s1*s3*s1^-1*s2*s3*s1^-1*s3^-1*s2^2*s1^2*s3^-1*s2*s3^2*s1^-1*s3^-1*s2^4*s3*s1^-2*s3*s1^-1*s3^-1*s2*s1^2*s3^-1*s2*s3*s1^-3*s2*s1*s3^-1*s2^-4*s3*s1*s3^-1*s2^-1*s3*s2^-2*s3*s1*s3^-1*s2^-1*s3*s1^-2*s2*s3*s1^-1*s3^-1*s2^2*s1^2*s3^-1*s1^3*s3^-1*s2^-2*s3*s1*s3^-1*s2^-1*s3^-1*s2^-1*s1^2*s3^-1*s2^3*s3*s1^-2*s3*s1*s3^-1*s1^2*s3^-1*s1^2*s3^-1*s2^-2*s3*s1^-2*s2^-1*s3*s1*s3^-1*s2^-1*s1*s3^-1*s1^-1*s3*s1^-2*s2*s3*s1^-3*s2*s3*s1^-1*s3^-1*s2^3,
    s1^-1*s3*s1*s3^-1*s1*s3^-1*s1^2*s3^-1*s2^-4*s3*s1^-2*s2*s3^-1*s2^-1*s3*s1^-1*s3^-1*s1^2*s3^-1*s2^-3*s3*s1^-2*s3*s1^-2*s2^-1*s3*s1*s3^-1*s2^-1*s3*s1^-1*s3^-1*s1^2*s3^-1*s2^-1*s3*s1^-2*s2^-1*s3*s1*s3^-1*s2^-1*s1*s3^-1*s1*s3^-1*s2^-1*s3*s1*s3^-1*s2^-2*s3*s1*s3^-1*s2^-1*s3*s1^-1*s3^-1*s1*s2^-1*s3*s1^-2*s2^-1*s1*s3*s1^-1*s2*s3*s1^-1*s3^-1*s2^2*s1^-1*s2*s3*s2^-1*s1^3*s3^-1*s1^-1*s3*s1^-1*s3^-1*s2*s3*s1^-1*s3^-1*s2^4*s3*s1^-2*s3*s1^-1*s3^-1*s2*s3*s1^2*s3^-1*s1*s2^-1*s1^2*s3^-1*s1*s3*s1^-1*s2*s3*s1^-1*s3^-1*s2*s1*s3*s1*s3^-1*s1^3*s3^-1*s2*s1^2*s3^-1*s2^-4*s3*s1*s3^-2*s2^-1*s3*s1^-2*s2^-2*s3*s1*s3^-1*s2^-1*s1*s3^-1*s1^-1*s3*s1^-2*s2^-1*s3*s1*s3^-1*s2^-1*s3*s1^-3*s3^-1*s2^-1*s3*s1^-2*s2*s3*s1^-3*s2*s3^-1*s2^-1*s1^3*s3^-1*s1*s3^-1*s1*s3*s1^-3*s2*s3^-1*s2^-1*s1*s2^-2*s3*s1*s3^-1*s2^-1*s1*s3^-1*s1^-1*s2^-1*s3*s1*s3^-1*s2^-1*s1*s3^-1*s1^-1*s3*s1^-2*s2*s3*s1^-3*s2*s3^-1*s2^-1*s3*s1^-2*s2*s3*s1^-1*s3^-1*s2^4*s3*s1^-3*s3*s1^-1*s3^-1*s2^-1*s1^3*s3^-2*s2^-1*s3*s1^-2*s2*s3*s1^-3*s2*s3^-1*s2^-1*s3*s1^-2*s2*s3*s1^-1*s3^-1*s2^4*s3*s1^-1*s3^-1*s2^-1*s3*s1^-2*s2*s3*s2^-2*s3*s1*s3^-1*s2^-1*s3^-1*s2^2*s3*s1^-1*s3^-1*s2^4*s3*s1^-2*s2*s1^-1*s3*s1^-1*s3^-1*s2^-1*s1^3*s3^-1*s1^-3*s2*s1^2*s3^-1*s2 ];
end, []);
Add(FakeProjectivePlaneGroups, rec(
  name := "C18, p=3, T1={2I}",
  csName := "(C18,p=3,\\{2I\\})",
  k := "Q(sqrt(6))", ell := "Q(sqrt(6))(sqrt(-3))", p := 3, T1 := "{2I}",
  N := 1, numberOfFakePlanes := 1,
  presentation := H, matrix := subgens, field := F, form := form, conj := conj,
  fakePlanes := [ rec(name := "(C18,p=3,\\{2I\\})", generators := GeneratorsOfGroup(H), index := 1, abInv := [ 2, 3, 3 ]) ] ));

# C18, p=3, T1={2}   [(C18,p=3,\{2\})]
f := FreeGroup("a", "b", "c");
a := f.1;
b := f.2;
c := f.3;
G := f / [
  (a^-1*c^-1)^3,
  (a^-1*b^-1*c*a^-1*b)^3,
  (b^-1*a^-1*c*a^-1*b^-1)^3,
  c^-1*b*a*b*c*a^-1,
  a^-1*b^-1*a*b^2*a*c^-1*a*b*a^-1*b*c^-1*a^-1*c^-1*b,
  a^-1*c*b*c*a^-2*c*a*c*b^-1*a*c^-1*b*a*b^-1,
  a*c^-1*b*a*c^-1*a*b^2*c*a^-2*b*c^-1*a^-1*c^-1,
  a*c^-1*b*a*c^-2*a^-1*b^-1*c*a^-1*b^-1*c*a^-1*c*a*b^-1,
  b^-1*a^-1*c*b^-1*a^2*c^-1*b^-1*a*c^-1*a*b^3*c^-2,
  b^2*c^-1*a^-1*c^-1*b*a^-1*b^-2*c*a^-1*c^-1*a^-1*b^-1*a*c^-1,
  b^-2*a^-1*b^-1*a^-1*b^-1*a^2*c^-1*a*c^-1*a*b^2*a*c^-1,
  b^-1*c^2*b^-3*a^-1*c^2*b^-1*c*b^-1*c*a^-1*b*a^-1*b^-1,
  c^-1*a*c^-1*b*a*b^-1*a^-1*c*a^-1*b^-1*c*a^-1*c^-1*b^-1*a^-1*c*a^-1,
  b^-3*a^-1*c*a^-1*b^-1*a*c^-1*b^-1*c^2*b^-3*a^-1*c*a^-1,
  c^-1*a^-1*b^-1*a^2*c^-1*b*c^-2*a^-1*b^-1*c^2*a^-2*c^-1*a^-1*b^-1,
  b*c*a^-2*c^-1*a^-1*b^-1*c*b^-1*a^-1*b*c^-2*b^-1*a^-2*b^-1*c,
  b*c*a^-2*b*a^-1*c^-2*a^-1*b^-1*c*b^-1*a^-1*b*c^-1*a^-1*c^-1*b*c^2,
  b*c^-2*a^-1*b^-1*c*b^-1*a^-1*b*a*b^-1*a^-1*c^-1*b^-1*c*a*c*b^-1*a*b,
  a^2*c^-1*b^-1*c^-1*a^2*c^-1*b*c^-1*a^2*c^-1*b^-1*a*c^-1*b^-2*a^-1*b^-1,
  b^-1*c^-1*b*c*a^-1*b^-1*a^-1*b*a*c*b^-1*a^-1*c^-2*a*b^3*a*c,
  a*b*a^-1*b^-1*a*b*a*c^-1*b^-1*c^2*b^-2*a^-1*b*a*c*a*b*c,
  c^-1*a*b*c^-1*b*a*c^2*b^-1*a*c^-1*b^-1*c^2*a*b^-1*a^-1*c^-1*a^-1*b^-1*a,
  a^-1*b^-1*c*a^-1*b*c^-2*b^-1*a^-1*c^-1*b^-1*a^-1*c^-1*b^-1*a^-1*c^-1*a^-1*b^-2*c*b
];
mats := [
  # a  (AD in the source file)
  [ [ (h*zeta^5+3*zeta^5-h*zeta^3-h*zeta^2-2*h-3)/9, (h*zeta^5+h*zeta^4+h*zeta^3-3*zeta^3+2*h*zeta^2+3*zeta^2-h*zeta-6*zeta+2*h+6)/9, (-2*h*zeta^5-6*zeta^5+h*zeta^4+9*zeta^4-5*h*zeta^3-3*zeta^3-h*zeta^2+3*zeta^2-h*zeta+6*zeta-4*h)/9 ],
    [ (-2*h*zeta^5-3*zeta^5-h*zeta^4-9*zeta^4-2*h*zeta^3-9*zeta^3-4*h*zeta^2-3*zeta^2-2*h*zeta-3*zeta+2*h-6)/9, (h*zeta^5-h*zeta^3+2*h*zeta^2+3*zeta^2-2*h-3)/9, (-2*h*zeta^5-3*zeta^5-2*h*zeta^4-6*zeta^4+h*zeta^3-3*zeta^3-h*zeta^2-3*zeta^2-h*zeta+2*h+6)/9 ],
    [ (zeta^5+3*h*zeta^4+4*zeta^4+7*zeta^3-h*zeta^2-4*zeta^2+2*h*zeta+2*zeta+2*h+8)/9, (4*h*zeta^5+3*zeta^5-h*zeta^4+6*zeta^4-2*h*zeta^3-9*zeta^3+2*h*zeta^2+h*zeta+9*zeta+2*h-6)/9, (-2*h*zeta^5-3*zeta^5-h*zeta^3-h*zeta^2-3*zeta^2-2*h-3)/9 ] ]*one,
  # b  (BD in the source file)
  [ [ (-2*h*zeta^5+h*zeta^4+4*h*zeta^3+6*zeta^3-h*zeta^2+6*zeta^2+2*h*zeta+6*zeta+2*h)/18, (3*h*zeta^5+6*zeta^5-2*h*zeta^4+6*zeta^4-h*zeta^3+12*zeta^3+12*zeta^2-7*h*zeta+4*h+18)/18, (3*h*zeta^5+6*zeta^5-h*zeta^4-12*zeta^4+5*h*zeta^3+6*zeta^3+3*h*zeta^2-6*zeta^2+h*zeta-12*zeta+4*h+6)/18 ],
    [ (h*zeta^5+4*zeta^4+h*zeta^3+4*zeta^3+2*h*zeta^2+h*zeta+2*zeta+2)/6, (h*zeta^5-6*zeta^5+h*zeta^4+6*zeta^4+4*h*zeta^3+6*zeta^3-h*zeta^2-6*zeta^2-h*zeta+2*h)/18, (-12*zeta^5-5*h*zeta^4-6*zeta^4-h*zeta^3+12*zeta^3+3*h*zeta^2-6*zeta^2+2*h*zeta-6*zeta+4*h+18)/18 ],
    [ (h*zeta^5-12*zeta^5+h*zeta^4+18*zeta^4+7*h*zeta^3+6*zeta^3-h*zeta^2-12*zeta^2-h*zeta+12*zeta+8*h+6)/18, (-2*h*zeta^5+h*zeta^4-2*zeta^4+h*zeta^3+4*zeta^3-h*zeta^2-4*zeta+2)/6, (h*zeta^5+6*zeta^5-2*h*zeta^4-6*zeta^4+4*h*zeta^3+6*zeta^3+2*h*zeta^2-h*zeta-6*zeta+2*h)/18 ] ]*one,
  # c  (CD in the source file)
  [ [ (-h*zeta^5-2*zeta^5-2*zeta^3-h*zeta^2-4*zeta^2+h*zeta+2)/6, (4*h*zeta^5+18*zeta^5-5*h*zeta^4-6*zeta^4+4*h*zeta^3+12*zeta^3-h*zeta^2+6*zeta^2-h*zeta-6*zeta+5*h+12)/18, (3*h*zeta^5+12*zeta^5-5*h*zeta^4-12*zeta^4+2*h*zeta^3+6*h*zeta^2+6*zeta^2-4*h*zeta-18*zeta+7*h+12)/18 ],
    [ (-2*h*zeta^5-6*zeta^5+h*zeta^4+12*zeta^4+4*h*zeta^3+12*zeta^3+5*h*zeta^2+5*h*zeta+18*zeta+5*h+18)/18, (h*zeta^5+4*zeta^5+h*zeta^4-2*zeta^3+2*zeta^2+2)/6, (h*zeta^5-6*zeta^5+4*h*zeta^4+4*h*zeta^3+12*zeta^3+5*h*zeta^2+12*zeta^2+5*h*zeta+6*zeta+5*h+12)/18 ],
    [ (-5*h*zeta^5-18*zeta^5-h*zeta^4+6*h*zeta^3+12*zeta^3-4*h*zeta^2-6*zeta^2-2*h*zeta-12*zeta+3*h+6)/18, (-5*h*zeta^5+4*h*zeta^4+6*zeta^4+4*h*zeta^3+12*zeta^3-7*h*zeta^2-6*zeta^2-h*zeta-12*zeta+5*h+18)/18, (-2*zeta^5-h*zeta^4-2*zeta^3+h*zeta^2+2*zeta^2-h*zeta+2)/6 ] ]*one
];
Add(FakeProjectivePlaneGroups, rec(
  name := "C18, p=3, T1={2}",
  csName := "(C18,p=3,\\{2\\})",
  k := "Q(sqrt(6))", ell := "Q(sqrt(6))(sqrt(-3))", p := 3, T1 := "{2}",
  N := 3, numberOfFakePlanes := 3,
  presentation := G, matrix := mats, field := F, form := form, conj := conj,
  fakePlanes := [
    rec(name := "(C18,p=3,\\{2\\},D_3)",
        generators := List([b, c*a^-1, a*c*a], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 3, abInv := [ 2, 3, 13 ]),
    rec(name := "(C18,p=3,\\{2\\},(dD)_3)",
        generators := List([a, b, c^-1*b*c], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 3, abInv := [ 2, 3 ]),
    rec(name := "(C18,p=3,\\{2\\},(d^2D)_3)",
        generators := List([c, a*b*a^-1, a*c*a^-1], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 3, abInv := [ 2, 3 ]) ] ));
end, []);

#############################################################################
##  k = Q(sqrt(7)),  ell = Q(sqrt(7))(sqrt(-1)),  p = 2
##  Field generators: h^2 = 7; i^2 = -1; zeta^3 = (h*i-1)*zeta^2*1/2+(h*i+1)*zeta*1/2+1
##  (conj: h -> h, i -> -i, zeta -> zeta^6)
CallFuncList(function()
local x, F, t, tbar, conj, form, f, G, mats, H, subgens, one, h, i, zeta, a, b, c, z;
x := Indeterminate(Rationals, "x");
F := FieldExtension(Rationals, x^12-x^10+x^8-x^6+x^4-x^2+1);
one := One(F);
t := RootOfDefiningPolynomial(F);   # t = i*zeta
h := (2*t^11-2*t^9+t^7-2*t)*one;
i := (-t^7)*one;
zeta := (t^8)*one;
tbar := (-t^11+t^9-t^7+t^5-t^3+t)*one;   # image of t under conj
conj := e -> ValuePol(ExtRepOfObj(e), tbar);
form := [ [ (i*zeta^2-h*zeta^2+2*zeta^2-h*i*zeta+3*i*zeta-h*zeta+3*zeta-h*i+3*i-h+3)/2, 0, 0 ],
          [ 0, (-h*i*zeta^2+2*i*zeta^2+zeta^2-i*zeta+h*zeta-2*zeta-i-h+2)/2, 0 ],
          [ 0, 0, (h*i*zeta^2-3*i*zeta^2+h*zeta^2-3*zeta^2+h*i*zeta-2*i*zeta-zeta+h*i-2*i-2*h+5)/2 ] ]*one;

# C20, p=2, T1={}   [(C20,p=2,\emptyset)]
f := FreeGroup("b", "z");
b := f.1;
z := f.2;
G := f / [
  b^3,
  z^7,
  (b*z^3*b*z^-1)^3,
  (b*z^3*b*z^-2)^3,
  b*z^-3*b*z^-3*b*z^-1*b^-1*z^-3*b^-1*z*b*z^3*b*z^3,
  b*z^3*b*z*b^-1*z^-3*b^-1*z^3*b^-1*z^3*b^-1*z^3*b^-1*z^3
];
mats := [
  # b  (BB in the source file)
  [ [ (7*i*zeta^2+5*h*zeta^2+14*zeta^2-3*h*i*zeta-7*i*zeta+h*zeta+7*zeta-4*h*i-7*i+h)/14, (-h*zeta^2-h*i*zeta+h*zeta+h*i)/7, (7*i*zeta^2-3*h*zeta^2+h*i*zeta+14*i*zeta+7*zeta-h*i+7*i+3*h-7)/14 ],
    [ (5*h*i*zeta^2+21*i*zeta^2+h*zeta^2+7*zeta^2+8*h*zeta-5*h*i-7*i+5*h-7)/28, (-3*h*i*zeta^2-14*i*zeta^2-4*h*zeta^2-7*zeta^2-7*i*zeta-5*h*zeta-14*zeta+3*h*i+7*i-5*h-7)/14, (-2*h*i*zeta^2+4*h*zeta^2+2*h*zeta+2*h*i-7*i+h)/14 ],
    [ (3*h*i*zeta^2-7*i*zeta^2-3*h*zeta^2-7*zeta^2+3*h*i*zeta-14*i*zeta-6*h*zeta-7*zeta+8*h*i+7*i-5*h)/28, (-5*h*i*zeta^2-21*i*zeta^2+7*h*zeta^2-7*zeta^2-5*h*i*zeta-21*i*zeta-h*zeta-7*zeta-4*h*i-14*i-6*h-28)/28, (3*h*i*zeta^2+7*i*zeta^2-h*zeta^2-7*zeta^2+3*h*i*zeta+14*i*zeta+4*h*zeta+7*zeta+h*i+4*h+7)/14 ] ]*one,
  # z  (ZZ in the source file)
  [ [ zeta, 0, 0 ],
    [ 0, zeta^2, 0 ],
    [ 0, 0, (-2*zeta^2-2*zeta+h*i-1)/2 ] ]*one
];
Add(FakeProjectivePlaneGroups, rec(
  name := "C20, p=2, T1={}",
  csName := "(C20,p=2,\\emptyset)",
  k := "Q(sqrt(7))", ell := "Q(sqrt(7))(sqrt(-1))", p := 2, T1 := "{}",
  N := 21, numberOfFakePlanes := 1,
  presentation := G, matrix := mats, field := F, form := form, conj := conj,
  fakePlanes := [
    rec(name := "(C20,p=2,\\emptyset,D_3 2_7)",
        generators := List([z*b*z^3*b^-1, b^-1*z^2*b*z^-1, z^-1*b^-1*z^2*b, z^-2*b*z*b^-1, b*z^3*b^-1*z, b*z^-2*b*z*b], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 21, abInv := [ 2, 2, 2, 2, 2, 2 ]) ] ));

# C20, p=2, T1={3+}   [(C20,p=2,\{3+\})]
f := FreeGroup("a", "b", "c");
a := f.1;
b := f.2;
c := f.3;
G := f / [
  b^3,
  a^-2*b*c^2*b*c^2*a*c^-1*b,
  c*a*b*a^-1*b^-1*a^-1*b^-1*a^-1*b^-1*a^-1*c^-1*b^-1*a^-1,
  a^-1*c*a*c^2*a*c^-1*a*b*c*a^-1*c^-2*b^-1,
  c^-1*a*b*c*a^-1*c^-1*a*c*a^-1*c^-2*b^-1*a^2,
  a*b^-1*c^2*a^-1*c^-2*b^-1*a^3*b*a*b,
  b*c^2*a*c^-3*b^-1*a^2*c^2*a*c^-1,
  (b*c^3*a^-1)^3,
  c^-1*a*c^-1*b*a^-2*c*a^-1*c^-2*a^-1*c^-3*b^-1*a,
  a^-1*c*a^-1*c^-2*b*a^-1*c*a^-1*c^-3*b^-1*a^-1*c*a^-1,
  a^-1*c^-1*a*b*c^-1*b^-1*a^-1*c*a^-1*b*c*b*a^-1*b*c*a^-1*c^-1,
  b*c^-1*b^-1*a^-1*c*a^-1*b*c*a^-1*c^-1*b^-1*a^-1*c^-1*b^-1*a^-1*c*a^-1*b*c^2,
  a^-1*c*a^-2*c^-2*b^-1*a^2*c*a*b*a^-2*c*a^-1*c^-2*a^-2,
  (b*a^-1*b^-1*a^-2*b*c)^3,
  c^-1*b^-1*a^-1*c^-2*b^-1*a^2*c*a*c^-1*b^-1*a*b^-1*a^-1*c^-1*b^-1*a^-1*b^-1*a^-1*c*a,
  b*a^-1*c^-1*a*c^-1*b*a^-1*b*a*b*c*a^-1*c^-1*a*b*c^-1*b^-1*a^-1*b^-1*a^-1*c*a*c
];
mats := [
  # a  (AA in the source file)
  [ [ (-2*h*i*zeta^2+28*i*zeta^2+6*h*zeta^2-h*i*zeta-7*i*zeta+9*h*zeta-21*zeta+3*h*i-21*i+13*h+7)/42, (-7*h*i*zeta^2-7*i*zeta^2+h*zeta^2+7*zeta^2-8*h*i*zeta+7*i*zeta+5*h*zeta-28*zeta+8*h*i-7*i+h-14)/42, (9*h*i*zeta^2+21*i*zeta^2-9*h*zeta^2+21*zeta^2+4*h*i*zeta+28*i*zeta+4*h*zeta+28*zeta-6*h*i+42*i-2*h-14)/84 ],
    [ (-h*i*zeta^2+14*i*zeta^2+4*h*zeta^2+7*zeta^2-6*h*i*zeta+6*h*zeta-7*h*i-7*i-3*h-21)/42, (h*i*zeta^2-35*i*zeta^2+3*h*zeta^2-21*zeta^2+2*h*i*zeta-28*i*zeta-6*h*zeta+4*h*i-14*i-4*h+14)/42, (-h*i*zeta^2+14*i*zeta^2+4*h*zeta^2-35*zeta^2+7*h*i*zeta+7*i*zeta-h*zeta-7*zeta+15*h*i+4*h+7)/42 ],
    [ (26*h*i*zeta^2-28*i*zeta^2-4*h*zeta^2+14*zeta^2+19*h*i*zeta-35*i*zeta+h*zeta+49*zeta+11*h*i-7*i-11*h+49)/84, (-5*h*i*zeta^2-14*i*zeta^2+2*h*zeta^2-7*zeta^2+h*i*zeta-14*i*zeta-4*h*zeta-7*zeta-3*h*i-12*h-21)/42, (h*i*zeta^2+7*i*zeta^2-9*h*zeta^2+21*zeta^2-h*i*zeta+35*i*zeta-3*h*zeta+21*zeta-7*h*i+14*i+12*h+21)/42 ] ]*one,
  # b  (BB in the source file)
  [ [ (2*h*i*zeta^2+14*i*zeta^2-4*h*zeta^2-28*zeta^2-2*h*i*zeta-14*i*zeta-2*h*zeta-14*zeta+7*h*i+7*i-h-7)/42, (2*h*i*zeta^2-7*i*zeta^2-3*h*zeta^2-5*h*i*zeta+7*i*zeta-3*h*zeta+21*zeta-4*h*i+14*i+6*h)/42, (3*h*i*zeta^2-21*i*zeta^2+3*h*zeta^2+21*zeta^2-9*h*i*zeta+2*h*zeta-7*zeta-h*i-7*i-5*h+7)/42 ],
    [ (-32*h*i*zeta^2+28*i*zeta^2-12*h*zeta^2-15*h*i*zeta+21*i*zeta-15*h*zeta-21*zeta+5*h*i+35*i-h-49)/84, (-2*h*i*zeta^2-14*i*zeta^2+h*zeta^2+7*zeta^2-h*i*zeta-7*i*zeta+2*h*zeta+14*zeta-4*h*i-7*i-3*h)/21, (-7*h*i*zeta^2+14*i*zeta^2+21*zeta^2-2*h*i*zeta+7*i*zeta+3*h*zeta-5*h*i+7*i+11*h-7)/42 ],
    [ (-3*h*i*zeta^2+8*h*zeta^2-49*zeta^2-21*i*zeta+7*h*zeta-56*zeta+17*h*i+14*i+6*h-21)/84, (17*h*i*zeta^2-7*i*zeta^2-3*h*zeta^2-21*zeta^2+32*h*i*zeta-28*i*zeta+12*h*zeta+21*h*i-21*i-9*h+63)/84, (2*h*i*zeta^2+14*i*zeta^2+2*h*zeta^2+14*zeta^2+4*h*i*zeta+28*i*zeta-2*h*zeta-14*zeta+h*i+7*i+7*h+7)/42 ] ]*one,
  # c  (CC in the source file)
  [ [ (-3*h*i*zeta^2-8*h*zeta^2-35*zeta^2-10*h*zeta-28*zeta+17*h*i+35*i-3*h-21)/42, (2*h*i*zeta^2+14*i*zeta^2-10*h*zeta^2+14*zeta^2-8*h*i*zeta+28*i*zeta-2*h*zeta-14*zeta-h*i-7*i+5*h-7)/42, (18*h*i*zeta^2+42*i*zeta^2-18*h*zeta^2+42*zeta^2-4*h*i*zeta+56*i*zeta+16*h*zeta+28*zeta-7*h*i+35*i+9*h+21)/84 ],
    [ (-10*h*i*zeta^2+35*i*zeta^2+11*h*zeta^2+14*zeta^2-12*h*i*zeta+12*h*zeta-6*h*i-21*i+5*h-28)/42, (3*h*i*zeta^2-2*h*zeta^2+7*zeta^2+3*h*i*zeta+8*h*zeta+35*zeta+h*i+7*i+h+7)/42, (-10*h*i*zeta^2+14*i*zeta^2+8*h*zeta^2-28*zeta^2-2*h*i*zeta-14*i*zeta+10*h*zeta-14*zeta+5*h*i-49*i+3*h-21)/42 ],
    [ (19*h*i*zeta^2-35*i*zeta^2+17*h*zeta^2-7*zeta^2+29*h*i*zeta-49*i*zeta-5*h*zeta+7*zeta+8*h*i-70*i+2*h+56)/84, (-2*h*i*zeta^2-35*i*zeta^2+h*zeta^2-14*zeta^2+10*h*i*zeta-35*i*zeta-11*h*zeta-14*zeta+6*h*i-18*h)/42, (10*h*zeta^2+28*zeta^2-3*h*i*zeta+2*h*zeta-7*zeta+3*h*i+2*h-7)/42 ] ]*one
];
Add(FakeProjectivePlaneGroups, rec(
  name := "C20, p=2, T1={3+}",
  csName := "(C20,p=2,\\{3+\\})",
  k := "Q(sqrt(7))", ell := "Q(sqrt(7))(sqrt(-1))", p := 2, T1 := "{3+}",
  N := 3, numberOfFakePlanes := 2,
  presentation := G, matrix := mats, field := F, form := form, conj := conj,
  fakePlanes := [
    rec(name := "(C20,p=2,\\{3+\\},D_3)",
        generators := List([c, b^-1*a*b, b^-1*c*b], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 3, abInv := [ 4, 7 ]),
    rec(name := "(C20,p=2,\\{3+\\},(3+)_3)",
        generators := List([b*c*b, b^-1*a*b^-1, b^-1*c*b^-1], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 3, abInv := [ 2, 3, 4 ]) ] ));

# C20, p=2, T1={3-}   [(C20,p=2,\{3-\})]
f := FreeGroup("a", "b", "c");
a := f.1;
b := f.2;
c := f.3;
G := f / [
  b*a*b^-1*c^2*a^-1,
  (c*b^-1*a)^3,
  (b^-1*c*a*c^-2)^3,
  b^-1*a*b*a*b^-1*a*c*a*b^-2*c*a*c^-2*a*c*a,
  a^-1*c^2*a^-1*c^-1*b*a*c*a*c^-1*b^-1*c*b*a*b^-1*a*c,
  c^-1*a^-1*c^2*a^-2*b*a^-1*c^-1*a^-1*b*a^-1*b^-1*c^-1*b^2*a^-1,
  a*c^-1*b*a*b^-1*a*c*b^-1*c^-1*b^-1*c*a*c^-2*a*c*b^-1*c^-1,
  b^-1*c^-1*b*c*b^-1*a*c*a^-1*b^-1*c*a^-1*c^2*a*c^-2*a*c*b^-1*c^-1,
  c*b^-1*a*c^-1*b*a^-2*c^-1*a^-1*b*a^-1*b^-1*a^-1*b^-1*a^-1*b*a^-1*b^-1*c^-1*b*c,
  a^-1*c^-1*a^-1*c^2*b^-1*a*b*a*c^-1*a^-1*b*c^-1*b^-1*a*c*a^-1*b^-1*c^-1*b*a^-1,
  a*b*c^2*a^-1*c^-1*b*a*b^2*a^-1*b^-1*c^-1*b*a*b^2*a^-1*b^-1*c^-1*b,
  b*c^2*a^-1*c^-1*b*a*b*a*c^-1*a^-1*b*a^-1*b^-1*c^-1*b*c^-1*b^-1*c*b*a*b^-1*a,
  b^-1*c^-1*b*c^2*b^-1*a*c*a^-1*b^-1*c*a^-1*b^-1*c*a^-1*b^-1*a^-1*b^-1*c*a*c^-2*b^-1*c,
  b^2*a^-1*b^-1*c^-1*a^-1*b*a^-1*b^-1*c^-1*b*c*b^-1*c*b^2*a*c^-1*a^-1*b*a^-1*b^-1*c*a^-1,
  (b^-1*a*b*a*c^-1*a^-1*b*c^-1)^3,
  c^-1*a*b^-1*c*b*a*b^-1*a*c*b^-2*c*b*a*b^-1*a*b*a*c^-1*b*a*c^-1*a^-1*b*c^-1,
  c^2*b^-1*a*c*a^-1*b^-1*c*b^-2*a*c^-1*b*a*b^-1*a*c*a^-1*b^-1*a^-1*b^-2*c*a^-1*b,
  c*a^-1*c^-1*a^-1*b^-1*c*b*c^-1*a^-1*b^-1*c*a*c^-2*a*c*a*c^-1*b^-1*a*c^-1*a*c^-2*a*c*b^-1,
  c*a^-1*c^-1*a^-1*b^-1*c*b*c^-1*a^-1*c^2*b^-1*a^2*c^-2*a*c*a*c^-1*a^-1*b*a^-1*b^-1*c*a^-1*b
];
mats := [
  # a  (AA in the source file)
  [ [ (2*h*i*zeta^2+28*i*zeta^2+4*h*i*zeta+14*i*zeta+6*h*zeta+h*i-7*i+15*h+21)/42, (-2*h*i*zeta^2-7*i*zeta^2-5*h*zeta^2+14*zeta^2-14*h*i*zeta+14*i*zeta+2*h*i+7*i+5*h-14)/42, (4*h*i*zeta^2+56*i*zeta^2+8*h*zeta^2+28*zeta^2+3*h*i*zeta+21*i*zeta+15*h*zeta+63*zeta-14*h*i+14*i+26*h-14)/84 ],
    [ (4*h*i*zeta^2-7*i*zeta^2+7*h*zeta^2+14*zeta^2-5*h*i*zeta-28*i*zeta+4*h*zeta-7*zeta-6*h*i-4*h-14)/42, (2*h*i*zeta^2-14*i*zeta^2+6*h*zeta^2-2*h*i*zeta-28*i*zeta-21*i+h+14)/42, (-12*h*i*zeta^2+21*i*zeta^2+5*h*zeta^2-14*zeta^2+2*h*i*zeta+7*i*zeta+5*h*zeta-14*zeta+10*h*i-7*i+11*h-14)/42 ],
    [ (21*h*i*zeta^2-21*i*zeta^2+7*h*zeta^2-49*zeta^2+25*h*i*zeta-49*i*zeta+3*h*zeta-21*zeta+31*h*i-7*i-3*h+21)/84, (-9*h*i*zeta^2-21*i*zeta^2-3*h*zeta^2-21*zeta^2-4*h*i*zeta+7*i*zeta-7*h*zeta-14*zeta-h*i+28*i-4*h-35)/42, (-4*h*i*zeta^2-14*i*zeta^2-6*h*zeta^2-2*h*i*zeta+14*i*zeta-6*h*zeta-h*i+7*i+5*h+7)/42 ] ]*one,
  # b  (BB in the source file)
  [ [ (-h*i*zeta^2-7*i*zeta^2-3*h*zeta^2-7*zeta^2-h*i*zeta-4*h*zeta-7*zeta+2*h*i+14*i)/14, (-h*zeta^2-h*i*zeta+h*zeta+h*i)/7, (-3*h*i*zeta^2-7*i*zeta^2+h*zeta^2+7*zeta^2-7*i*zeta-h*zeta-4*h*i)/14 ],
    [ (h*i*zeta^2-7*i*zeta^2-3*h*zeta^2-21*zeta^2+h*i*zeta+7*i*zeta-5*h*zeta-21*zeta+5*h*i+21*i+h+7)/28, (7*i*zeta^2-h*zeta^2+h*i*zeta+7*i*zeta+3*h*zeta+7*zeta-h*i+7*i+5*h+7)/14, (-2*h*i*zeta^2+4*h*zeta^2+2*h*zeta+2*h*i-7*i+h)/14 ],
    [ (3*h*i*zeta^2-7*i*zeta^2-3*h*zeta^2-7*zeta^2+3*h*i*zeta-14*i*zeta-6*h*zeta-7*zeta+8*h*i+7*i-5*h)/28, (14*i*zeta^2-2*h*zeta^2-h*i*zeta+7*i*zeta+3*h*zeta+21*zeta-6*h*i+14*i+6*h+14)/28, (h*i*zeta^2+4*h*zeta^2+7*zeta^2-7*i*zeta+h*zeta-h*i+2*h+7)/14 ] ]*one,
  # c  (CC in the source file)
  [ [ (-4*h*i*zeta^2-14*i*zeta^2-8*h*zeta^2-28*zeta^2+4*h*i*zeta-7*i*zeta-h*zeta-14*zeta+7*h*i+14*i+2*h+7)/42, (-10*h*i*zeta^2-14*i*zeta^2-6*h*zeta^2+42*zeta^2-20*h*i*zeta+14*i*zeta-4*h*zeta-14*zeta-5*h*i-7*i+3*h-21)/42, (6*h*i*zeta^2+42*i*zeta^2-2*h*zeta^2+14*zeta^2+42*i*zeta+6*h*zeta+15*h*i+21*i+31*h+35)/84 ],
    [ (-4*h*i*zeta^2+7*i*zeta^2+3*h*zeta^2-4*h*i*zeta-14*i*zeta+6*h*zeta+8*h*i+7*i+5*h-14)/42, (8*h*i*zeta^2+7*i*zeta^2+7*h*zeta^2+14*zeta^2+4*h*i*zeta+14*i*zeta+8*h*zeta+28*zeta-5*h*i-7*i+13*h+35)/42, (-10*h*i*zeta^2+28*i*zeta^2+2*h*zeta^2-56*zeta^2+10*h*i*zeta+14*i*zeta+6*h*zeta-42*zeta+21*h*i-21*i+13*h-7)/42 ],
    [ (37*h*i*zeta^2-7*i*zeta^2+13*h*zeta^2-49*zeta^2+43*h*i*zeta-49*i*zeta+11*h*zeta+49*zeta+25*h*i-49*i+11*h+91)/84, (-21*i*zeta^2+3*h*zeta^2+4*h*i*zeta-7*i*zeta-3*h*zeta+10*h*i+14*i)/42, (-4*h*i*zeta^2+7*i*zeta^2+h*zeta^2+14*zeta^2-8*h*i*zeta-7*i*zeta-7*h*zeta-14*zeta-2*h*i+14*i+6*h)/42 ] ]*one
];
Add(FakeProjectivePlaneGroups, rec(
  name := "C20, p=2, T1={3-}",
  csName := "(C20,p=2,\\{3-\\})",
  k := "Q(sqrt(7))", ell := "Q(sqrt(7))(sqrt(-1))", p := 2, T1 := "{3-}",
  N := 3, numberOfFakePlanes := 2,
  presentation := G, matrix := mats, field := F, form := form, conj := conj,
  fakePlanes := [
    rec(name := "(C20,p=2,\\{3-\\},D_3)",
        generators := List([a, c], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 3, abInv := [ 4, 7 ]),
    rec(name := "(C20,p=2,\\{3-\\},(3-)_3)",
        generators := List([a, b*a*c^-1, b^2, c^2*b^-1], w -> MappedWord(w, GeneratorsOfGroup(f), GeneratorsOfGroup(G))),
        index := 3, abInv := [ 2, 3, 4 ]) ] ));
end, []);

# Sort into the order of Tables 1 and 2
FakeProjectivePlaneGroups := FakeProjectivePlaneGroups{List(
  [ "Q(sqrt(-1)), p=5, T1={}", "Q(sqrt(-1)), p=5, T1={2}", "Q(sqrt(-1)), p=5, T1={2I}",
    "Q(sqrt(-2)), p=3, T1={}", "Q(sqrt(-2)), p=3, T1={2}", "Q(sqrt(-2)), p=3, T1={2I}",
    "Q(sqrt(-7)), p=2, T1={}", "Q(sqrt(-7)), p=2, T1={7}", "Q(sqrt(-7)), p=2, T1={3}",
    "Q(sqrt(-7)), p=2, T1={3,7}", "Q(sqrt(-7)), p=2, T1={5}", "Q(sqrt(-7)), p=2, T1={5,7}",
    "Q(sqrt(-15)), p=2, T1={}", "Q(sqrt(-15)), p=2, T1={3}", "Q(sqrt(-15)), p=2, T1={5}",
    "Q(sqrt(-15)), p=2, T1={3,5}", "Q(sqrt(-23)), p=2, T1={}", "Q(sqrt(-23)), p=2, T1={23}",
    "C2, p=2, T1={}", "C2, p=2, T1={3}", "C10, p=2, T1={}", "C10, p=2, T1={17-}",
    "C18, p=3, T1={}", "C18, p=3, T1={2}", "C18, p=3, T1={2I}",
    "C20, p=2, T1={}", "C20, p=2, T1={3+}", "C20, p=2, T1={3-}" ],
  n -> PositionProperty(FakeProjectivePlaneGroups, r -> r.name = n))};

MakePlaneGroup:=function(r,nr)
local a,f,g,iso,isScalar,F,fam;
  isScalar:=m-> not IsZero(m[1][1]) and IsOne(m/m[1][1]);

  if not ForAll(RelatorsOfFpGroup(r.presentation),
    x->isScalar(MappedWord(x,FreeGeneratorsOfFpGroup(r.presentation),r.matrix)))
      then
    Error("Does not match!");
  fi;

  # set field display (for `String`)
  F:=r.field;
  fam:=FamilyObj(One(F));
  if not IsBound(fam!.nicePrintBasis) and IsBound(r.fieldGens) then
    fam!.nicePrintBasis:=NamedBasisFromElements(F,r.fieldGens[1],r.fieldGens[2]);
  fi;

  a:=r.fakePlanes[nr];
  g:=List(a.generators,x->MappedWord(x,GeneratorsOfGroup(r.presentation),r.matrix));
  g:=Group(g);
  SetName(g,Concatenation("CSM(",a.name,")"));
  f:=Subgroup(r.presentation,a.generators);
  iso:=IsomorphismFpGroup(f);
  iso:=iso*IsomorphismSimplifiedFpGroup(Range(iso));
  f:=Range(iso);
  if Length(GeneratorsOfGroup(f))<>Length(GeneratorsOfGroup(g)) 
    or not ForAll(RelatorsOfFpGroup(f),x->isScalar(
       MappedWord(x,FreeGeneratorsOfFpGroup(f),GeneratorsOfGroup(g)))) then
    Print("redo to match generators\n");
    f:=Subgroup(r.presentation,a.generators);
    iso:=IsomorphismFpGroupByGenerators(f,a.generators);
    f:=Range(iso);
    if not ForAll(RelatorsOfFpGroup(f),
      x->isScalar(MappedWord(x,FreeGeneratorsOfFpGroup(f),GeneratorsOfGroup(g))))
        then
           Error("still mismatch");
    fi;
    SetName(f,Concatenation("CSP(",a.name,")"));
  fi;
  return [f,g];
end;

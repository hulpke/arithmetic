#############################################################################
##
##  aschbacher_tests.g  --  certificate checker and examples for
##                          AschbacherClasses (read aschbacher.g first)
##
##  CheckCert(G,r) independently verifies all certificates in the result
##  r:=AschbacherClasses(G).
##
# is A a scalar multiple of B?
LetOk:=function(A,B) local i,j;
  i:=PositionProperty(B,x->not IsZero(x)); j:=PositionNonZero(B[i]);
  return A=(A[i][j]/B[i][j])*B;
end;
# independent verification of certificates
CheckCert:=function(G,r)
local F,n,gens,ok,c,g,X,pows,mb,bl,B,lam,i,x,pos,inF0,q0,bar,SW,m;
  F:=r.field; n:=r.dimension; gens:=GeneratorsOfGroup(G); ok:=true;
  for c in r.classes do
    if c="C1" then
      ok:=ok and ForAll(gens,g->RankMat(Concatenation(r.C1.submodule,r.C1.submodule*g))=Length(r.C1.submodule));
    elif c="C2" then
      bl:=Set(r.C2.blocks,b->Immutable(TriangulizedMat(b)));
      ok:=ok and RankMat(Concatenation(r.C2.blocks))=n and
          ForAll(gens,g->ForAll(bl,b->Immutable(TriangulizedMat(b*g)) in bl));
    elif c="C3" then
      X:=r.C3.fieldGenerator;
      ok:=ok and IsIrreducibleRingElement(PolynomialRing(F),MinimalPolynomial(F,X))
             and Degree(MinimalPolynomial(F,X))=r.C3.degree;
      pows:=List([0..r.C3.degree-1],i->Concatenation(X^i));
      ok:=ok and ForAll(gens,g->SolutionMat(pows,Concatenation(g^-1*X*g))<>fail);
    elif c="C4" then
      ok:=ok and ForAll(gens,g->ASCH.KroneckerFactor(r.C4.basis*g*r.C4.basis^-1,r.C4.dims[1],r.C4.dims[2])<>fail);
    elif c="C5" then
      q0:=Size(r.C5.subfield); X:=r.C5.conjugator;
      for g in gens do x:=X*g*X^-1; pos:=PositionNonZero(x[1]); x:=x[1][pos]^-1*x;
        ok:=ok and ForAll(Concatenation(x),y->y^q0=y); od;
    elif c="C6" then
      ok:=ok and IsNormal(G,r.C6.normalSubgroup) and IsPGroup(r.C6.normalSubgroup)
             and MTX.IsAbsolutelyIrreducible(GModuleByMats(GeneratorsOfGroup(r.C6.normalSubgroup),F));
    elif c="C7" then
      m:=r.C7.m; SW:=ASCH.SwapMat(m,F);
      ok:=ok and ForAll(gens,g->ASCH.KroneckerFactor(r.C7.basis*g*r.C7.basis^-1,m,m)<>fail or
                                ASCH.KroneckerFactor(r.C7.basis*g*r.C7.basis^-1*SW,m,m)<>fail);
    elif c="C8_1" then
      B:=r.C8_1.form;
      ok:=ok and RankMat(B)=n and (B=TransposedMat(B) or B=-TransposedMat(B)) and
        ForAll(gens,g->LetOk(g*B*TransposedMat(g),B));
    elif c="C8_2" then
      B:=r.C8_2.form; q0:=Size(r.C8_2.subfield); bar:=M->List(M,x->List(x,y->y^q0));
      ok:=ok and RankMat(B)=n and B=TransposedMat(bar(B)) and
        ForAll(gens,g->LetOk(g*B*TransposedMat(bar(g)),B));
    fi;
    if not ok then Print("   CERTIFICATE FAILED for ",c,"\n"); return false; fi;
  od;
  return true;
end;

Show:=function(arg)
local name,G,r,t;
  name:=arg[1]; G:=arg[2];
  t:=Runtime();
  r:=CallFuncList(AschbacherClasses,arg{[2..Length(arg)]});
  Print(String(name,-30)," ",r.classes,"  undecided: ",r.undecided,
        "  certificates ok: ",CheckCert(G,r),"  ",Runtime()-t,"ms\n");
  return r;
end;

RunAschbacherExamples:=function()
local G,R,w,g3,I3,B,T,M11,L,pm,Xm,Zm,I2;
  Show("reducible",Group([[1,1],[0,1]]*Z(5)^0));
  Show("Sp(4,3)",Sp(4,3));
  Show("Sp(4,3) over GF(9)",Sp(4,3),GF(9));
  Show("GO-(4,4)",GO(-1,4,4));
  Show("SU(4,3)",SU(4,3));
  Show("GL(2,3) wr S3",WreathProduct(GL(2,3),SymmetricGroup(3)));
  B:=Basis(AsField(GF(5),GF(125)));
  Show("GL(2,125) in GL(6,5)",Group(List(GeneratorsOfGroup(GL(2,125)),g->BlownUpMat(B,g))));
  Show("GL(2,5) (x) GL(3,5)",Group(Concatenation(
    List(GeneratorsOfGroup(GL(2,5)),g->KroneckerProduct(g,One(GL(3,5)))),
    List(GeneratorsOfGroup(GL(3,5)),g->KroneckerProduct(One(GL(2,5)),g)))));
  Show("SL(3,2) over GF(4)",SL(3,2),GF(4));
  w:=Z(7)^2;
  R:=Group([[1,0,0],[0,w,0],[0,0,w^2]]*Z(7)^0,[[0,1,0],[0,0,1],[1,0,0]]*Z(7)^0);
  Show("N_GL(3,7)(3^(1+2))",Normalizer(GL(3,7),R));
  g3:=GeneratorsOfGroup(GL(3,2)); I3:=IdentityMat(3,GF(2));
  T:=Group(Concatenation(List(g3,g->KroneckerProduct(g,I3)),[ASCH.SwapMat(3,GF(2))]));
  Show("GL(3,2) wr S2 (tensor ind.)",T);
  Show("A7 < GL(4,2)",First(MaximalSubgroupClassReps(GL(4,2)),x->Size(x)=2520));
  Show("3.A6 < SL(3,4)",First(MaximalSubgroupClassReps(SL(3,4)),x->Size(x)=1080));
end;

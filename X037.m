X37:=SmallModularCurve(37);
X,m:=SimplifiedModel(X37);
assert m(RepresentativePoint(CuspPlaces(X37,37,1)[1])) eq X![1,1,1];
assert m(RepresentativePoint(CuspPlaces(X37,37,37)[1])) eq X![1,1,0];
X;
w37:=AtkinLehnerInvolution(X37,37,37);
ptsX:=Setseq(Points(X : Bound:=1000));
J:=Jacobian(X);
inftyplus:=X![1,1,0];
inftymin:=X![1,-1,0];
ptsJ:=[pt-ptsX[1] : pt in ptsX];
P2<x,y,z>:=AmbientSpace(X);
w:=iso<X->X | [x,y,x-z],[x,y,x-z]>;
assert w eq Inverse(m)*w37*m;
C,rho:=CurveQuotient(AutomorphismGroup(X,[w]));
C;
assert MordellWeilRank(C) eq 1;
assert #TorsionSubgroup(C) eq 1;
Q1:=C![0,-1,1];
OC:=C![0,1,0];
P1div:=Pullback(rho,Divisor(Q1));  
piO:=Pullback(rho,Divisor(OC));
D1:=J!(P1div-Divisor(inftyplus)-Divisor(inftymin));
assert J!(P1div-piO) eq D1;

//We now compute J(Q)
assert #TorsionSubgroup(J) eq 3;
assert (3*(inftyplus-w(inftyplus)) eq J!0) and not (inftyplus-w(inftyplus) eq J!0);
assert RankBound(J) eq 1;
bas,M:=ReducedBasis([D1]);
assert #bas eq 1; //So D1 has infinite order and rank(J) = 1
//We now show that D1 is not divisible in J(Q) using an algorithm of Stoll
LogBound:=Height(D1)+HeightConstant(J);
AbsBound:=Ceiling(Exp(LogBound));
PtsUpToAbsBound := Points(J : Bound:=AbsBound);
assert ReducedBasis( [ pt : pt in PtsUpToAbsBound ]) eq [D1];
//This also shows that Q1-OC must generate J_C(Q)

//We check the rest of the statements made in the final section
i:=iso<X->X | [x,-y,z],[x,-y,z]>;
iw:=Expand(i*w);
E,pi:=CurveQuotient(AutomorphismGroup(X,[iw]));
E;
assert MordellWeilRank(E) eq 0;
assert #TorsionSubgroup(E) eq 3;
QE:=E![8,18,1];
assert Order(QE) eq 3;
assert J!Pullback(pi,Divisor(QE)-Divisor(Zero(E))) eq inftyplus-w(inftyplus);
pb2:=Pullback(pi,Divisor(2*QE));  
pb1:=Pullback(pi,Divisor(QE));
pb0:=Pullback(pi,Divisor(Zero(E)));
assert pb1 eq Place(inftyplus)+Place(w(inftymin));
assert pb2 eq Place(inftymin)+Place(w(inftyplus));
Q37<rt37>:=QuadraticField(37);
R:=X(Q37)![2,2*rt37,1];
assert Place(R) eq pb0;
j:=jFunction(X37,37);
Evaluate(j,Inverse(m)(R));

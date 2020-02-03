//X_0(43). 
load "ozmansiksek.m";

X,Z,phi,j,al,jd:=modeqns(43,1); //Takes a minute or 2.
X;
assert Genus(X) eq 3;

RR<[u]>:=CoordinateRing(AmbientSpace(X));
n:=Dimension(AmbientSpace(X));
M:=al[1];
row:=[&+[RowSequence(M)[i][j]*u[j] : j in [1..n+1]] : i in [1..n+1]];
w:=iso<X->X | row,row>; //The A-L involution w_{43}.

infcusp:=X![1,0,0]; 
assert 1/j(infcusp) eq 0; 
cusp2:=X![1,1,1];//
assert 1/j(cusp2) eq 0; //Indeed both are cusps.
assert cusp2 eq w(infcusp); //w acts on the cusps
Dtor:=Divisor(cusp2)-Divisor(infcusp);
assert not IsPrincipal(Dtor); //Sanity check
assert IsPrincipal(7*Dtor); //So J_0(43)(\Q)_{tor} \simeq Z/7Z.

//We now compute C and J(C)(\Q)
C,projC:=CurveQuotient(AutomorphismGroup(X,[w]));
Eprime,hprime:=EllipticCurve(C,projC(infcusp));
E,h:=SimplifiedModel(Eprime);
XtoE:=Expand(projC*hprime*h);
E;
assert Conductor(E) eq 43;
MWE,phi,tf1,tf2:=MordellWeilGroup(E);
assert tf1; assert tf2; //This shows MWE is computed provably.
assert IsIsomorphic(MWE,AbelianGroup([0])); //Shows MWE is free of rank 1
seqQE:=[QQ : QQ in [phi(MWE.1),phi(-MWE.1)] | QQ eq E![0,-1,1]];
QE:=seqQE[1]; //QE is the claimed point.

//We use this generator to find the free generator of J_0(43)(\Q)
D:=Pullback(XtoE,Place(QE));
D1:=D-1*Place(X![1,0,0])-1*Place(X![1,1,1]);
K7<r>:=QuadraticField(-7);
assert r^2 eq -7;
PP:=(X(K7)![1/8*(r+3),1/8*(-r+5),1]);
assert Place(PP) eq D; //This shows the generator is as claimed.
bp:=Pullback(XtoE,Place(E![0,1,0]));
assert bp eq Place(X![1,0,0])+Place(X![1,1,1]); //Sanity check.

//We check the exceptional quadratic points are as claimed.
K71<t>:=QuadraticField(-71);
K131<s>:=QuadraticField(-131);
assert t^2 eq -71; assert s^2 eq -131;
P0:=X(Rationals())![4/5,2/5,1];
P1:=X(K131)![1/72*(s+65),1/24*(s+17),1];
P2:=X(K131)![1/25*(-2*s+9),2/5,1];
P3:=X(K71)![1/4*(t+1),1,0];
P4:=X(K71)![1/15*(-t+8),1/30*(-t+23),1]; //No errors means they lie on the curve.
excpts:=[Place(P1),Place(P2),Place(P3),Place(P4)];
assert &and[not Pullback(w,Q) eq Q : Q in excpts]; //This shows the points are indeed exceptional.

//We now find a list of degree 2 points using the function of Siksek and Ozman
deg2,pls1,pls2,plsbig:=searchDiv2(X,10,false); //Takes a few minutes.
assert #pls1 eq 3; //It finds all three rational points
assert excpts subset pls2;
assert #{Q : Q in pls2 | not XtoE(RepresentativePoint(Q)) in E(Rationals())} eq #excpts; //The only exceptional quadratic places in pls2 are P1,P2,P3,P4.
assert not IsSingular(ChangeRing(X,GF(7))); //Sanity check to verify that X has good reduction at 7.
deg2pb:=[1*pl : pl in pls2 | XtoE(RepresentativePoint(pl)) in E(Rationals())] cat 
[1*pl1 + 1*pl2 : pl1 in pls1, pl2 in pls1 | w(RepresentativePoint(pl1)) eq RepresentativePoint(pl2)];
deg2npb:=[DD : DD in deg2 | not DD in deg2pb]; //We split deg2 into deg2 \cap XtoE*(E(\Q)) and the rest.
assert Seqset(deg2) eq Seqset(deg2pb cat deg2npb); //Sanity check.

//Finally, we do the sieve.
A:=AbelianGroup([0,7]);
divs:=[D1,Dtor];
genusC:=Genus(C);
auts:=[al[1]];
I:=2;
load "quadptssieve.m";
MWSieve(deg2,[7,5,11],X,A,divs,auts,genusC,deg2pb,deg2npb,I,bp); //Returns boolean true if we have indeed found all exc degree 2 pts.

//Do they have CM?
assert &and[not HasComplexMultiplication(EllipticCurveFromjInvariant(j(RepresentativePoint(QQ)))) : QQ in excpts]; //No.
tf,cm:=HasComplexMultiplication(EllipticCurveFromjInvariant(j(P0)));
assert cm eq -43;

//We check that the corresponding elliptic curves have a conductor different from their conjugate, hence are not \Q-curves.
Ps:=<P1,P2,P3,P4>;
c131:=hom<K131->K131 | [-s]>;
c71:=hom<K71->K71 | [-t]>;
cs:=<c131,c131,c71,c71>;
for i in [1..4] do
  Pi:=Ps[i];
  ci:=cs[i];
  Ei:=EllipticCurveFromjInvariant(j(Pi));
  assert not Conductor(EllipticCurve([ci(a) : a in aInvariants(Ei)])) eq Conductor(Ei);
end for;



//X_0(53). Load searchDiv2, reduce, modeqns
load "ozmansiksek.m";

X,Z,phi,j,al,jd:=modeqns(53,1); //Takes a minute or 2.
X;
assert Genus(X) eq 4;

RR<[u]>:=CoordinateRing(AmbientSpace(X));
n:=Dimension(AmbientSpace(X));
M:=al[1];
row:=[&+[RowSequence(M)[i][j]*u[j] : j in [1..n+1]] : i in [1..n+1]];
w:=iso<X->X | row,row>; //The A-L involution w_{53}.

infcusp:=X![1,0,0,0]; 
assert 1/j(infcusp) eq 0; 
cusp2:=X![1,1,1,1];//
assert 1/j(cusp2) eq 0; //Indeed both are cusps.
assert cusp2 eq w(infcusp); //w acts on the cusps
Dtor:=Divisor(cusp2)-Divisor(infcusp);
assert not IsPrincipal(Dtor); //Sanity check
assert IsPrincipal(13*Dtor); //So J_0(43)(\Q)_{tor} \simeq Z/13Z.

//We now compute C and J(C)(\Q)
C,projC:=CurveQuotient(AutomorphismGroup(X,[w]));
Eprime,hprime:=EllipticCurve(C,projC(infcusp));
E,h:=SimplifiedModel(Eprime);
XtoE:=Expand(projC*hprime*h);
E;
assert Conductor(E) eq 53;
MWE,phi,tf1,tf2:=MordellWeilGroup(E);
assert tf1; assert tf2; //This shows MWE is computed provably.
assert IsIsomorphic(MWE,AbelianGroup([0])); //Shows MWE is free of rank 1
seqQE:=[QQ : QQ in [phi(MWE.1),phi(-MWE.1)] | QQ eq E![0,-1,1]];
QE:=seqQE[1]; //QE is the claimed point. 

//We use this generator to find the free generator of J_0(43)(\Q)
D:=Pullback(XtoE,Place(QE));
D1:=D-1*Place(infcusp)-1*Place(cusp2);
K11<r>:=QuadraticField(-11);
assert r^2 eq -11;
PP:=(X(K11)![ 0, 1/6*(-r + 5), 1, 1 ]);
assert Place(PP) eq D; //This shows the generator is as claimed.
bp:=Pullback(XtoE,Place(E![0,1,0]));
assert bp eq Place(infcusp)+Place(cusp2); //Sanity check.

//We now find a list of degree 2 points using the function of Siksek and Ozman
deg2,pls1,pls2,plsbig:=searchDiv2(X,5,false); //Takes a few minutes.
assert #pls1 eq 2; //The cusps are the only rational points found.
assert #{Q : Q in pls2 | not XtoE(RepresentativePoint(Q)) in E(Rationals())} eq 0; //No exceptional quadratic points found.
deg2pb:=[1*pl : pl in pls2 | XtoE(RepresentativePoint(pl)) in E(Rationals())] cat 
[1*pl1 + 1*pl2 : pl1 in pls1, pl2 in pls1 | w(RepresentativePoint(pl1)) eq RepresentativePoint(pl2)];
deg2npb:=[DD : DD in deg2 | not DD in deg2pb]; //We split deg2 into deg2 \cap XtoE*(E(\Q)) and the rest.
assert Seqset(deg2) eq Seqset(deg2pb cat deg2npb); //Sanity check.

assert not IsSingular(ChangeRing(X,GF(11))); //Sanity check to verify that X has good reduction at primes we sieve with.

//Finally, we do the sieve.
A:=AbelianGroup([0,13]);
divs:=[D1,Dtor];
genusC:=Genus(C);
auts:=[al[1]];
I:=2;
load "quadptssieve.m";
MWSieve(deg2,[11,7],X,A,divs,auts,genusC,deg2pb,deg2npb,I,bp); //Returns boolean true if we have indeed found all exc degree 2 pts.







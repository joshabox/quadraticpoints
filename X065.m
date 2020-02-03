//X_0(65). Load searchDiv2, reduce, modeqns
load "ozmansiksek.m";

X,Z,phi,j,al,jd:=modeqns(65,13); //Just a few seconds.
X;
assert Genus(X) eq 5;

RR<[u]>:=CoordinateRing(AmbientSpace(X));
n:=Dimension(AmbientSpace(X));
rows:=[[&+[RowSequence(a)[i][j]*u[j] : j in [1..n+1]] : i in [1..n+1]] : a in al] ;
w5:=iso<X->X | rows[1],rows[1]>; 
w13:=iso<X->X | rows[2], rows[2]>; 
w65:=iso<X->X | rows[3] , rows[3]>; //These are the Atkin-Lehner involutions.
assert w65 eq w5*w13; //Sanity check

cusps:=[X![1,0,0,0,0],X![1,1,1,1,1],X![1/3,2/3,2/3,2/3,1],X![1/2,1/2,1/2,1/2,1]]; 
assert &and[1/j(cusp) eq 0 : cusp in cusps]; //We have found the four cusps.
assert {w(cusps[1]) : w in [w5*w5,w5,w13,w65]} eq Seqset(cusps);
Dtors:=[Divisor(cusps[i])-Divisor(cusps[1]) : i in [2,3,4]];
assert &and[not IsPrincipal(Dtor) : Dtor in Dtors]; //Sanity check
//To compute the rational cuspidal subgroup, we embed the torsion subgroup into J_X(\F_7)
X7:=ChangeRing(X,GF(7));
C,phi,psi:=ClassGroup(X7);
Z:=FreeAbelianGroup(1);
degr:=hom<C->Z | [ Degree(phi(a))*Z.1 : a in OrderedGenerators(C)]>;
JF7:=Kernel(degr); // This is isomorphic to J_X(\F_7).
redDtors:=[JF7!psi(reduce(X,X7,DD)) : DD in Dtors];
A:=sub<JF7 | redDtors>; //This is isomorphic to J_X(\Q)_{tors}.
B:=AbelianGroup([2,84]);
tf,isomm:=IsIsomorphic(A,B);
assert tf; 
assert &and[isomm(A.i) eq B.i : i in [1,2]]; //So A = Z/2Z x Z/84Z with A.1, A.2 being the generators
Z3:=FreeAbelianGroup(3);
hh:=hom<Z3-> A | redDtors>;
assert hh(-9*Z3.1+2*Z3.2) eq A.1;
assert Order(hh(17*Z3.1+13*Z3.2)) eq 84 and not 42*hh(17*Z3.1+13*Z3.2) eq hh(-9*Z3.1+2*Z3.2); //This shows that the generators of J_X(\Q)_{tors} are as claimed.


//We now compute C and J(C)(\Q)
C,projC:=CurveQuotient(AutomorphismGroup(X,[w65]));
Eprime,hprime:=EllipticCurve(C,projC(cusps[1]));
E,h:=SimplifiedModel(Eprime);
XtoE:=Expand(projC*hprime*h);
E;
assert Conductor(E) eq 65;
MWE,phi,tf1,tf2:=MordellWeilGroup(E);
assert tf1; assert tf2; //This shows MWE is computed provably.
assert IsIsomorphic(MWE,AbelianGroup([2,0])); //Shows MWE is Z/2Z x Z as abstract group.
assert 2*MWE.1 eq Zero(MWE); //So MWE.1 is the generator of order 2.
DD:=Pullback(XtoE,Place(phi(MWE.1)));
assert DD eq Place(cusps[3])+Place(cusps[4]); //The pullback of the divisor phi(MWE.1)-Zero(E) to X is already torsion.
seqQE:=[QQ : QQ in [phi(MWE.2),phi(-MWE.2)] | QQ eq E![1,0,1]];
QE:=seqQE[1]; //QE is the claimed point.

//We use this generator to find the free generator of J_0(43)(\Q)
D:=Pullback(XtoE,Place(QE));
bp:=Pullback(XtoE,Place(Zero(E)));
assert bp eq Place(cusps[1]) + Pullback(w65,Place(cusps[1])); //Sanity check
D1:=D-bp;
K1<r>:=QuadraticField(-1);
assert r^2 eq -1;
PP:=(X(K1)![0,1,1/2*(1+r),1,1]);
assert 1*Place(PP) eq D; //This shows the generator is as claimed.

//Searching for degree 2 points on X directly takes a while. Since we conjecture that all quadratic points are pullbacks, we might as well work via E.
ptsX:=PointSearch(X,1000);
deg2:=Setseq({Pullback(XtoE,Place(phi(k*MWE.2+ep*MWE.1))) : k in {-10..10}, ep in {0,1}} join {Place(pt1) + Place(pt2) : pt1 in ptsX, pt2 in ptsX});
deg2npb:=[Place(pt1) + Place(pt2) : pt1 in ptsX, pt2 in ptsX | not w65(pt1) eq pt2];
deg2pb:=[DD : DD in deg2 | not DD in deg2npb]; //We split into pullbacks and non-pullbacks.

//Finally, we do the sieve.
assert &and[not IsSingular(ChangeRing(X,GF(p))) : p in [17]]; //Sanity check to verify that X has good reduction at primes used in the sieve.
A:=AbelianGroup([0,2,84]);
divs:=[D1,-9*Dtors[1]+2*Dtors[2],17*Dtors[1]+13*Dtors[2]];
genusC:=Genus(C);
auts:=[al[3]];
I:=2;
load "quadptssieve.m";

MWSieve(deg2,[17,23],X,A,divs,auts,genusC,deg2pb,deg2npb,I,bp); //Returns true if we have found all deg 2 points.







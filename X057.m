//X_0(57). 
load "ozmansiksek.m";

X,Z,phi,j,al,jd:=modeqns(57,19); //Just a few seconds.
X;
assert Genus(X) eq 5;

RR<[u]>:=CoordinateRing(AmbientSpace(X));
n:=Dimension(AmbientSpace(X));
rows:=[[&+[RowSequence(a)[i][j]*u[j] : j in [1..n+1]] : i in [1..n+1]] : a in al] ;
w3:=iso<X->X | rows[1],rows[1]>; 
w19:=iso<X->X | rows[2], rows[2]>; 
w57:=iso<X->X | rows[3] , rows[3]>; //These are the Atkin-Lehner involutions.
assert w57 eq w3*w19; //Sanity check

cusps:=[X![1,0,0,0,0],X![1,1,0,1,0],X![3,3,1,2,1],X![3,9/2,-1/2,7/2,1]]; 
assert &and[1/j(cusp) eq 0 : cusp in cusps]; //We have found the four cusps.
assert {w(cusps[1]) : w in [w3*w3,w3,w19,w57]} eq Seqset(cusps);
Dtors:=[Divisor(cusps[i])-Divisor(cusps[1]) : i in [2,3,4]];
assert &and[not IsPrincipal(Dtor) : Dtor in Dtors]; //Sanity check
assert &and[IsPrincipal(6*Dtors[1]), not IsPrincipal(3*Dtors[1]), not IsPrincipal(2*Dtors[1])]; //Dtors[1] has order 6
assert &and([IsPrincipal(30*Dtors[2])] cat [not IsPrincipal(m*Dtors[2]) : m in Divisors(30) | not m eq 30]); //Dtors[2] has order 30
assert IsPrincipal(Dtors[1]+11*Dtors[2]-Dtors[3]); //Dtors[3] is in <Dtors[1],Dtors[2]>;
assert &and([not IsPrincipal(Dtors[1]-k*Dtors[2]) : k in [5,25]] cat [not IsPrincipal(2*Dtors[1]-k*Dtors[2]) : k in [10,20]] cat [not IsPrincipal(3*Dtors[1] - 15*Dtors[2])]);
//The latter shows that <Dtors[1]> and <Dtors[2]> have intersection {0} so J_0(57)(\Q)_{tors} \simeq Z/6Z x Z/30Z.


/*N=57 is the only case where the quotient C of X_0(N) such that rk(J(C)(\Q)) = rk (J_0(N)(\Q))  has degree 4. We now compute C and J(C)(\Q). */
C,projC:=CurveQuotient(AutomorphismGroup(X,[w3,w19]));
Eprime,hprime:=EllipticCurve(C,projC(cusps[1]));
E,h:=SimplifiedModel(Eprime);
XtoE:=Expand(projC*hprime*h);
E;
assert Conductor(E) eq 57;
MWE,phi,tf1,tf2:=MordellWeilGroup(E);
assert tf1; assert tf2; //This shows MWE is computed provably.
assert IsIsomorphic(MWE,AbelianGroup([0])); //Shows MWE is free of rank 1
for QQ in [phi(MWE.1),phi(-MWE.1)] do
    if QQ eq E![2,-2,1] then QE:=QQ; //QE is the claimed point.
    end if;
end for;



//We use this generator to find the free generator of J_0(43)(\Q)
assert Pullback(XtoE,Place(Zero(E))) eq &+[Place(cusp) : cusp in cusps]; //Sanity check.
D:=Pullback(XtoE,Place(QE));
bbp:=Pullback(XtoE,Place(Zero(E)));
D1:=D-bbp;
RR<z>:=PolynomialRing(Rationals());
K<r>:=NumberField(z^4-z^2+1);
PP:=(X(K)![1/13*(-9*r^3 - 2*r^2 - 3*r + 34),
    1/13*(15*r^3 + 12*r^2 - 21*r + 30),
    1/13*(-5*r^3 - 4*r^2 + 7*r + 3),
    1/13*(8*r^3 + 9*r^2 - 19*r + 29),1]);
assert 1*Place(PP) eq D; //This shows the generator is as claimed.
assert bbp eq &+[Place(cusp) : cusp in cusps]; //Sanity check.

//We check the claimed quadratic points indeed lie on the curve.
Km23<rtm23>:=QuadraticField(-23);
Km3<rtm3>:=QuadraticField(-3);
Km2<rtm2>:=QuadraticField(-2);
K13<rt13>:=QuadraticField(13);
P1:=X(Km23)![ 1/32*(-11*rtm23 + 47), 1/16*(-7*rtm23 + 43), 1/8*(rtm23 - 5), 1/4*(-rtm23 + 9), 1 ];
P2:=X(Km23)![ 1/2*(rtm23 - 3), 1/2*(rtm23 + 3), 1, 1, 0 ];
P3:=X(Km23)![ 1/2*(-rtm23 + 3), -rtm23 + 2, -1, 1/2*(-rtm23 + 1), 1 ];
P4:=X(Km23)![ 1/8*(rtm23 - 1), 1/8*(rtm23 + 11), 1/4*(-rtm23 - 1), 1/8*(rtm23 + 15), 1 ];
tf,isom:=IsIsomorphic(Parent(j(P2)),Km23);
PP23:=[P1,P2,P3,P4];
P5:=X(Km3)![ 2, 1/2*(-rtm3 + 7), 0, 1/2*(-rtm3 + 5), 1 ];
P6:=X(Km3)![ -rtm3, -rtm3 + 3, 1/2*(rtm3 - 1), -rtm3 + 2, 1 ];
P7:=X(Km3)![ 1/2*(-rtm3 + 3), 1/2*(-rtm3 + 3), 1/2*(rtm3 - 1), 2, 1 ];
P8:=X(Km3)![ 1/2*(-5*rtm3 + 1), 1/2*(-5*rtm3+ 1), 1/2*(rtm3 - 3), -rtm3 + 1, 1 ];
PP3:=[P5,P6,P7,P8];
P9:=X(Km2)![ 1/3*(rtm2 + 4), 1/3*(4*rtm2 + 7), 1/3*(-rtm2 - 1), 1/3*(2*rtm2 + 5), 1 ];
P10:=X(Km2)![ 1/2*(-rtm2+ 2), 3, 1/2*rtm2, 1/2*(-rtm2 + 6), 1 ];
PP2:=[P9,P10];
P11:=X(K13)![ 1/3*(2*rt13 + 14), 1/3*(2*rt13 + 14), 1/6*(-rt13 - 1), 1/6*(5*rt13 + 29), 1 ];
P12:=X(K13)![ 1/2*(5*rt13 + 23), 1/2*(-3*rt13 - 3), 1/2*(rt13 + 3), 1/2*(-rt13 + 3), 1 ];  //No errors means they lie on the curve.
PP13:=[P11,P12];
allquadpts:=[Place(P1),Place(P2),Place(P3),Place(P4),Place(P5),Place(P6),Place(P7),Place(P8),Place(P9),Place(P10),Place(P11),Place(P12)];

//We check which ones have CM or are a Q-curve
E23:=[EllipticCurveFromjInvariant(j(P1)),EllipticCurveFromjInvariant(isom(j(P2))),EllipticCurveFromjInvariant(j(P3)),EllipticCurveFromjInvariant(j(P4))];
E3:=[EllipticCurveFromjInvariant(j(Q)) : Q in PP3];
E2:=[EllipticCurveFromjInvariant(j(Q)) : Q in PP2];
E13:=[EllipticCurveFromjInvariant(j(Q)) :Q in PP13];
assert &and[not HasComplexMultiplication(E23[i]) : i in [1..4]];
CMs:=[-27,-3,-12,-3];
for i in [1..4] do
    tf,cm:=HasComplexMultiplication(E3[i]);
    assert cm eq CMs[i];
end for;
tf1,cm1:=HasComplexMultiplication(E2[1]);
assert cm1 eq -8;
tf2,cm2:=HasComplexMultiplication(E2[2]);
assert cm2 eq -8;
assert &and[not HasComplexMultiplication(E13[i]) : i in [1,2]];
c23:=hom<Km23->Km23 | [-rtm23]>;
E23c:=[EllipticCurve([c23(a) : a in aInvariants(EE)]) : EE in E23];
assert &and[not Conductor(E23[i]) eq Conductor(E23c[i]) : i in [1..4]]; //These are not Q-curves
c3:=hom<Km3->Km3 | [-rtm3]>;
PP3c:=[X(Km3)![c3(a) : a in Eltseq(Q)] : Q in PP3];
assert &and[w19(PP3[i]) eq PP3c[i] : i in [1..4]]; //P5,...,P8 are \Q-curves via w_{19}.
assert &and[w57(PP3[i]) eq PP3c[i] : i in [3,4]];
c2:=hom<Km2 -> Km2 | [-rtm2]>;
PP2c:=[X(Km2)![c2(a) : a in Eltseq(Q)] : Q in PP2];
assert &and[w57(PP2[i]) eq PP2c[i] : i in [1,2]];
c13:=hom<K13 -> K13 | [-rt13]>;
PP13c:=[X(K13)![c13(a) : a in Eltseq(Q)] : Q in PP13];
assert &and[w3(PP13[i]) eq PP13c[i] : i in [1,2]];

//Finally, we do the sieve.
deg2:=[1*pl : pl in allquadpts] cat [1*Place(pt1) + 1*Place(pt2) : pt1 in cusps, pt2 in cusps];
deg2pb:=[];
deg2npb:=deg2; //Just to synchronise with other X_0(N) and make sure the sieve gives no errors.
assert &and[not IsSingular(ChangeRing(X,GF(p))) : p in [11,13]]; //Sanity check to verify that X has good reduction.
A:=AbelianGroup([0,6,30]);
divs:=[D1,Dtors[1],Dtors[2]];
genusC:=Genus(C);
bp:=2*Place(cusps[1]);
auts:=[al[1],al[2]];
I:=4;
load "quadptssieve.m";

MWSieve(deg2,[11,13],X,A,divs,auts,genusC,deg2pb,deg2npb,I,bp); //Returns true if we have found all deg 2 points





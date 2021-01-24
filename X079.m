load "ozmansiksek.m";

ModCrvQuot:=function(N,wlist,remwlist)
C:=CuspForms(N);
ws:=[AtkinLehnerOperator(C,n) : n in wlist];
remws:=[AtkinLehnerOperator(C,n) : n in remwlist];
W:=AtkinLehnerOperator(C,N);
NN:=&meet([Nullspace(Matrix(w-1)) : w in ws] cat [Nullspace(1-W^2)]);
dim:=Dimension(NN);
seqs:=[[Coordinates(NN,Basis(NN)[i]*Matrix(w)) : i in [1..dim]] : w in remws];
BB:=[&+[(Integers()!(2*Eltseq(Basis(NN)[i])[j]))*C.j : j in [1..Dimension(C)]] : i in [1..dim]];
prec:=500;
L<q>:=LaurentSeriesRing(Rationals(),prec);
R<[x]>:=PolynomialRing(Rationals(),dim);
Bexp:=[L!qExpansion(BB[i],prec) : i in [1..dim]];
eqns:=[R | ];
	d:=1;
	tf:=false;
	while tf eq false do
		d:=d+1;
		mons:=MonomialsOfDegree(R,d);
		monsq:=[Evaluate(mon,Bexp) : mon in mons];
		V:=VectorSpace(Rationals(),#mons);
		W:=VectorSpace(Rationals(),prec-10);
		h:=hom<V->W | [W![Coefficient(monsq[i],j) : j in [1..(prec-10)]] : i in [1..#mons]]>;
		K:=Kernel(h);
		eqns:=eqns cat [ &+[Eltseq(V!k)[j]*mons[j] : j in [1..#mons] ] : k in Basis(K)  ];
        I:=Radical(ideal<R | eqns>);
		X:=Scheme(ProjectiveSpace(R),I);
		if Dimension(X) eq 1 then
			if IsSingular(X) eq false then
				X:=Curve(ProjectiveSpace(R),eqns);
				if Genus(X) eq dim then
					tf:=true;
				end if;
			end if;
		end if;
	end while;
	eqns:=GroebnerBasis(ideal<R | eqns>); // Simplifying the equations.
	tf:=true;
	repeat
		t:=#eqns;
		tf:=(eqns[t] in ideal<R | eqns[1..(t-1)]>);
		if tf then 
			Exclude(~eqns,eqns[t]);
		end if;
	until tf eq false;
	t:=0;
	repeat
		t:=t+1;
		tf:=(eqns[t] in ideal<R | Exclude(eqns,eqns[t])>);	
		if tf then
			Exclude(~eqns,eqns[t]);
			t:=0;
		end if;
	until tf eq false and t eq #eqns;
	X:=Curve(ProjectiveSpace(R),eqns); // Our model for X_0(N) discovered via the canonical embedding.
	assert Genus(X) eq dim;
	assert IsSingular(X) eq false;
    indexGam:=N*&*[Rationals() | 1+1/p : p in PrimeDivisors(N)];	
	indexGam:=Integers()!indexGam; // Index of Gamma_0(N) in SL_2(Z)
	for eqn in eqns do
		eqnScaled:=LCM([Denominator(c) : c in Coefficients(eqn)])*eqn;
		wt:=2*Degree(eqn); // Weight of eqn as a cuspform.
		hecke:=Ceiling(indexGam*wt/12);  // Hecke=Sturm bound.
										// See Stein's book, Thm 9.18.
		Bexp1:=[qExpansion(BB[i],hecke+10) : i in [1..dim]]; // q-expansions
                        // of basis for S 
                        // up to precision hecke+10.
		assert Valuation(Evaluate(eqnScaled,Bexp1)) gt hecke+1;
	end for; // We have now checked the correctness of the equations for X. 
seqlist:=[[&+[seq[i][j]*x[j] : j in [1..dim]] : i in [1..dim]] : seq in seqs];
wmaplist:=[iso<X->X | seq,seq> : seq in seqlist];
return X,wmaplist,seqs;
end function;


X,ws:=ModCrvQuot(79,[],[79]); //Just a few seconds.
w:=ws[1];
assert Genus(X) eq 6;

//This function computes J_X(F_p).
JacobianFp:=function(X)
CC,phii,psii:=ClassGroup(X); //Algorithm of Hess
Z:=FreeAbelianGroup(1);
degr:=hom<CC->Z | [ Degree(phii(a))*Z.1 : a in OrderedGenerators(CC)]>;
JFp:=Kernel(degr); // This is isomorphic to J_X(\F_p).
return JFp,phii,psii;
end function;

cusps:=PointSearch(X,500);
Dtors:=[Place(cusps[1])-Place(cusps[2])];
//To compute the rational cuspidal subgroup, we embed the torsion subgroup into J_X(\F_7)
X7:=ChangeRing(X,GF(7));
JF7:=JacobianFp(X7);
redDtors:=[JF7!psi(reduce(X,X7,DD)) : DD in Dtors];
A:=sub<JF7 | redDtors>; //This is isomorphic to J_X(\Q)_{tors}.
assert IsIsomorphic(A,AbelianGroup([13]));

//Computing JF3 and JF5 shows that <Dtors>=J_X(Q)_{tors}.
X3:=ChangeRing(X,GF(3));
X5:=ChangeRing(X,GF(5));
JacobianFp(X3);
JacobianFp(X5);

//We now compute C and J(C)(\Q)
C,projC:=CurveQuotient(AutomorphismGroup(X,[w]));
Eprime,hprime:=EllipticCurve(C,projC(cusps[1]));
E,h:=SimplifiedModel(Eprime);
XtoE:=Expand(projC*hprime*h);
E;
assert Conductor(E) eq 79;
MWE,phi,tf1,tf2:=MordellWeilGroup(E);
assert tf1; assert tf2; //This shows MWE is computed provably.
assert IsIsomorphic(MWE,AbelianGroup([0])); //Shows MWE is Z/2Z x Z as abstract group.
D:=Pullback(XtoE,Place(phi(MWE.1)));
bp:=Pullback(XtoE,Place(Zero(E)));

D1:=D-bp;
divs:=[D1,Dtors[1]];
genusC:=1;
I:=2;
A:=AbelianGroup([0,13]);
deg2:=[2*Place(cusps[1]),2*Place(cusps[2])];

//This function verifies the conditions of Theorem 2.1
//Input: degree 2 divisor QQ and prime p of good reduction
IsLonely:=function(QQ,p,X)
if p eq 2 then return false; end if; //Part of first condition in Theorem
ptlist:=[];
d:=2; //Just there to emphasize that we work on X^{(d)} for d=2.
//We now distinguish between a pair of rational points and a quadratic point
if #Decomposition(QQ) eq 1 then //Quadratic point or double rational point case
Q:=Decomposition(QQ)[1][1];
if not IsIsomorphic(ResidueClassField(Q),Rationals()) then //Quadratic point case
dd:=[1,1]; //This encodes that QQ=Q_1+Q_2 with Q_1 and Q_2 distinct
disc:=discQuadPlace(Q);
K:=QuadraticField(disc); //The quadratic field over which QQ is defined
F:=ResidueClassField(Q);
tf,ii:=IsIsomorphic(F,K);
assert tf; //Sanity check
Q:=[ii(x) : x in Eltseq(RepresentativePoint(Q))]; 
conjQ:=[Conjugate(x) : x in Q];
Append(~ptlist,Q);
Append(~ptlist,conjQ);
else dd:=[2]; //Double rational point case
K:=RationalsAsNumberField();
Q:=[K!a : a in Eltseq(RepresentativePoint(Q))];
Append(~ptlist,Q);
end if;
else dd:=[1,1]; //Two distinct rational points case
K:=RationalsAsNumberField();
ptlist:=[Eltseq(RepresentativePoint(Decomposition(QQ)[1][1])),Eltseq(RepresentativePoint(Decomposition(QQ)[2][1]))];
ptlist:=[[K!a : a in pt] : pt in ptlist];
end if;
OK:=RingOfIntegers(K); //K is the number field over which Q_1, Q_2 are defined
dec:=Factorization(p*OK);
pp:=dec[1][1]; //A prime of K above p
f:=InertiaDegree(pp);
if p eq 3 and f eq 1 then return false; end if; //Condition in theorem
Fp,pi:=ResidueClassField(pp);
Xp:=ChangeRing(X,Fp);
Rp<[u]>:=CoordinateRing(AmbientSpace(Xp));
ws:=[map<Xp->Xp | [Evaluate(eqn,u) : eqn in DefiningEquations(w)]>];
V,phi:=SpaceOfDifferentialsFirstKind(Xp);
ts:=[hom<V->V | [ (Pullback(wp,phi(V.i)))@@phi -V.i  : i in [1..Genus(X)] ]> : wp in ws];
T:=&+[Image(t): t in ts]; //The space of vanishing differentials
if not p eq 2 then assert Dimension(T) eq Genus(X) - genusC; end if; //cf Remark 3.7.
omegas:=[phi(T.i) : i in [1..Dimension(T)]]; //A basis of vanishing differentials
unif:=UniformizingElement(pp);
matrixseq:=[];
for pt in ptlist do //We now construct the matrix Atilde.
m:=Minimum([Valuation(a,pp) : a in pt | not a eq 0]);
Qred:=[unif^(-m)*a : a in pt]; 
Qtilde:=Xp![Evaluate(a,Place(pp)) : a in Qred]; //The mod p reduction of Q
tQtilde:=UniformizingParameter(Qtilde);
if dd eq [1,1] then
Append(~matrixseq,[(omega/Differential(tQtilde))(Qtilde) : omega in omegas]);
else 
Append(~matrixseq,[(omega/Differential(tQtilde))(Qtilde) : omega in omegas]);
Append(~matrixseq,[((omega/Differential(tQtilde)-(omega/Differential(tQtilde))(Qtilde))/tQtilde)(Qtilde) : omega in omegas]); 
end if;
end for;
Atilde:=Matrix(matrixseq);
if Rank(Atilde) eq d then return true;
else return false;
end if;
end function;


ChabautyInfo:=function(X,w5,p,A,divs,I,bp,B,iA,W,deg2)
//I must satisfy I*J_X(\Q) \subset G.
Fp:=GF(p);
Xp:=ChangeRing(X,Fp);
assert not IsSingular(Xp);
JFp,phi,psi:=JacobianFp(Xp);
divsp:=[reduce(X,Xp,divi) : divi in divs];
bpp:=reduce(X,Xp,bp); //We reduce the divisors and the basepoint
h:=hom<A -> JFp | [(JFp!psi(divp)) : divp in divsp]>; //The map A--> J_X(\F_p).
deg2p:=[1*reduce(X,Xp,DDD) : DDD in deg2];
deg2p2:=[psi(DD-bpp) : DD in deg2p];

//We now split our cosets in W into smaller cosets on which h takes a single value.
Bp,iAp:=sub<A | Kernel(h)>;
newB,newiA:=sub<A | iA(B) meet iAp(Bp)>; 
AmodnewB,pi1:=quo< A | newiA(newB)>;
AmodB,pi2:=quo<AmodnewB | pi1(iA(B))>;
W:=[(x+w)@@pi1 : x in Kernel(pi2), w in pi1(W)]; 
B:=newB; iA:=newiA;
mI:=hom<JFp -> JFp | [I*g : g in OrderedGenerators(JFp)]>;
imW:={h(x) : x in W | h(x) in Image(mI)}; 
K:=Kernel(mI);
jposP:=[];

for x in imW do //For each z such that I*z = x, we check whether z can come from a rational point. If yes for some z, we keep x. 
    z:=x@@mI;
    if &or[Dimension(phi(z+k)+bpp) gt 0 and (not z+k in deg2p2
            or not IsLonely(deg2[Index(deg2p2,z+k)],p,X)) : k in K] 
    then Append(~jposP,x);
    end if;
end for;

print "The nr of jposP is"; #jposP;
W:=[x : x in W | h(x) in jposP]; //Representatives for the B-cosets of A corresponding to jposP.
return W,B,iA; 
end function;



MWSieve:=function(X,w5,primes,A,divs,I,bp,B0,iA0,W0,deg2)
B:=B0;
iA:=iA0;
W:=W0;
// Together, B+W \subset A consists of the possible images of unknown (rational)
// points in A. The map X(\Q) \to A is composition of X(\Q) \to J(X)(\Q) and
// multiplication by integer I such that I*J(X)(\Q) \subset A.
for p in primes do
p;
W,B,iA:=ChabautyInfo(X,w5,p,A,divs,I,bp,B,iA,W,deg2);
// Whatever Chabauty method we use, it should output a subgroup iAp: Bp \to A and
// a set Wp of Bp-cosets containing the hypothetical unknown points.
if W eq [] then return true; end if;
print "The number of possible cosets unknown points can land is"; #W;
end for;
return B,iA,W;
end function;

primes:=[3,5,7,11,13,17,19,23];
B0,iA0:=sub<A | A.1>;
W0:={a*A.2 : a in [1..12]};
MWSieve(X,w,primes,A,divs,I,bp,B0,iA0,W0,deg2);

//It follows that if there is an exceptional eff deg 2 divisor Q, then 2[Q-bp] is fixed by w.
//This implies that [Q-bp] is fixed by w (there is no 2-torsion).
//Then Q ~ w^*Q, which implies that Q=w^*Q because X is not hyperelliptic.
//Then either Q is a pullback, or it is fixed by w pointwise.
//We check that no quadratic point is fixed by w.

A:=Matrix(seqs[1]);
I:=IdentityMatrix(Rationals(),6);
v:=Basis(Kernel(A-I))[1];
CR<[x]>:=CoordinateRing(AmbientSpace(X));
I:=ideal<CR | &+[v[i]*x[i] : i in [1..6]]>;
Z:=Scheme(X,I);
pts:=PointsOverSplittingField(Z);
pts; //All of degree 5 

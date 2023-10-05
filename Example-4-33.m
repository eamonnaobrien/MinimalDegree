// Example 4.33: construct minimal degree representation for G(4, 28)

load "setup-permrep.m";

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

SetEchoInput (true);

p := 7;

w := PrimitiveRoot(p);

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, b1, b2, b3> := FreeGroup (8);
Alpha := [a1, a2, a3, a4, a5];
Beta := [b1, b2, b3];

// common relations, typically commutators
Comms := [
(a2, a3) = 1, (a2, a4)= 1, (a3, a4) = 1,
(a4, a5) = a2, (a3, a5) = a1, (a2, a5) = 1, a1 = b1,
a2 = b2] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..5]]: i in [1..3]])
cat &cat([[(Beta[i], Beta[j]) = Id(F) : j in [i + 1..3]]: i in [1..3]]);

G := quo <F | Comms, a3^p =  b1^p = b2^p = b3^p = 1,
a4^p = b1, a5^p = b3>;

Q, phi := pQuotient(G, p, 10);

// subgroup R 
PR := sub<G | G.3, G.4, G.2, (G.5^p)>;  
PR := phi (PR);
// kernel of non-linear irr char. from R
PN := sub<G | G.3, G.4, (G.5^p)>;  
PN := phi (PN);

// subgroup S
PS := sub<G | G.3, G.4, G.2, (G.5^p)>; 
PS := phi (PS);
//  kernel of non-linear irr char. from S
PM := sub<G | G.3, G.2, (G.5^p)>;  
PM := phi (PM);

// subgroup T 
PT := sub<G | G.1, G.3, G.4, G.2, G.5, G.6, G.7, G.8>; 
PT := phi (PT);
// kernel of non-linear irr char. from T
PL := sub<G | G.3, G.1, G.2, G.4>;
PL := phi (PL);

Int := Core(Q, PN) meet Core(Q, PM) meet Core(Q, PL);
assert #Int eq 1;

phiN := CosetAction (Q, PN);
phiM := CosetAction (Q, PM);
phiL := CosetAction (Q, PL);
pi := PermutationRepresentationSumH (Q, [phiN, phiM, phiL]);
J := Image (pi);
assert #J eq #Q;
assert IsIsomorphic (J, Q);

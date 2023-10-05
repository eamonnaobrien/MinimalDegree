//Example 4.32: construct minimal degree representation for G(3, 24r) 

load "setup-permrep.m";

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

SetEchoInput (true);

p := 7;

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, b1, b2, b3> := FreeGroup (7);
Alpha := [a1, a2, a3, a4];
Beta := [b1, b2, b3];

// common relations, typically commutators
Comms := [
(a2, a3) = 1, (a2, a4)= a1, (a3, a4) = a2, a1 = b1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..4]]: i in [1..3]])
cat &cat([[(Beta[i], Beta[j]) = Id(F) : j in [i + 1..3]]: i in [1..3]]);

// G3, 24r

for r in [1,nu] do
   "\n r is ", r;
   G := quo <F | Comms, a2^p =  b1^p = b2^p = b3^p = 1,  
                        a3^p = b1^r, a4^p = b2>;
   
   Q, phi := pQuotient (G, p, 10);
   "Q is ", Q;

   H := sub<G | G.1, G.2, G.3, G.4, G.5, G.6>;
   PH := phi (H);
   R := sub<G | (G.3), (G.4^p), (G.2)>;
   PR := phi (R);
   N := sub<G | (G.4^p), (G.2)>;
   PN := phi (N);
   S := sub<G | (G.1), (G.3), (G.4), (G.2), (G.5), (G.6)>;
   PS := phi (S);
   M := sub<G  | (G.3), (G.1), (G.2)>;
   PM := phi (M);
   
   Int := Core(PH, PN) meet Core(PH, PM);
   assert #Int eq 1;
   // printf "%o  %o\n", i, #Int;
   
   // setup perm rep for H 
   phiN := CosetAction (PH, PN);
   phiM := CosetAction (PH, PM);
   pi := PermutationRepresentationSumH (PH, [phiN, phiM]);
   J := Image (pi);
   assert #J eq #PH;
   
   // setup perm rep for G
   I, IS := DetermineMinRep (G, Q, PH, [PN, PM], phi);
   assert #&meet[Core (Q, s): s in IS] eq 1;
   assert #I eq #Q;
   "Permutation rep is", I;
end for;


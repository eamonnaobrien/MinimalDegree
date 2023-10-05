// Example 3.2: construct minimal degree representation for G(3,3)

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

F<a1, a2, a3, a4, b1> := FreeGroup (5);
Alpha := [a1, a2, a3, a4];

// common relations, typically commutators
Comms := [
(a2, a3) = 1, (a2, a4)= a1, (a3, a4) = a2, a1 = b1^(p^2)]
cat
[(b1, Alpha[j]) = Id(F) : j in [1..4]];

G := quo <F | Comms, a2^p = a3^p =  b1^(p^3) = 1, a4^p = b1>;
Q, phi := pQuotient (G, p, 10);
S := sub < G | [G.2, G.3]>; 
S := phi (S);
J := CosetImage (Q, S);
assert #J eq #Q;
assert IsIsomorphic (Q, J);



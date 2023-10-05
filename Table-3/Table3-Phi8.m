load "../setup-permrep.m";

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

// Groups G are listed in the list L.
// d(Z(L[1])) = 1 to p.
// d(Z(L[2])) = p+1 to #L.

// G8 with centre cyclic of order p^2

My8A := function(p)

F<a1, a2, a3, a4, a5, b1> := FreeGroup (6);
Alpha := [a1, a2, a3, a4, a5];

// common relations, typically commutators
Comms := [
(a2, a3) = 1, (a2, a4)= 1, (a3, a4) = a1,
(a4, a5) = a2, (a3, a5) = 1, (a2, a5) = a1, a1 = b1^p,
a3^-1 = a5^p]
cat
[(b1, Alpha[j]) = Id(F) : j in [1..5]];

L := [];

// G8, 2r

for r in [0..(p-2)] do
G := quo <F | Comms,  a5^(p^2) = b1^(p^2) = 1,
a4^p*a2^-1 = b1^r>;
Append (~L, G);
end for;

// G8, 4

G := quo <F | Comms,   b1^(p^2) = 1,
a4^p = a2, a5^(p^2) = b1>;
Append (~L, G);

return L;
end function;

//List for Phi8 with center Cp X Cp

My8B := function(p)

F<a1, a2, a3, a4, a5, b1, b2> := FreeGroup (7);
Alpha := [a1, a2, a3, a4, a5];
Beta := [b1, b2];

// common relations, typically commutators
Comms := [
(a2, a3) = 1, (a2, a4)= 1, (a3, a4) = a1,
(a4, a5) = a2, (a3, a5) = 1, (a2, a5) = a1, a1 = b1, 
(b1, b2) = 1, a3^-1 = a5^p] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..5]]: i in [1..2]]);

L := [];

// G8, 6

G := quo <F | Comms,  a5^(p^2) =  b1^p = b2^p = 1,
a4^p*a2^-1 = b2>;
Append (~L, G);

return L;
end function;

TablePhi8 := function(p)
    return My8A(p) cat My8B(p);
end function;

// Checking of column "H"

Check8ACol3 := function (L, p)

Z := Integers ();
    nu := Z ! (NonQuadraticResidue (p)); // nu

count := 0;
H := [];
MinDeg1 := [];

// G8, 2r

for r in [0..(p-2)] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6];
Append (~H, sub< F | Alpha[5]>);
Append (~MinDeg1, p^4);
end for;

// G8, 4

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6];
Append (~H, sub< F | (Alpha[5]^p)*Alpha[4]^(-1)>);
Append (~MinDeg1, p^4);

return H, MinDeg1;
end function;


Check8BCol3 := function (L, p)

Z := Integers ();
    nu := Z ! (NonQuadraticResidue (p)); // nu

count := p;
H1 := [];
H2 := [];
MinDeg2 := [];

// following setup is done just to ensure that
// |L[i]: H1[i]| + |L[i]: H2[i]| = MinDeg[i].

for r in [1..p] do
F := L[p+1]; // no particular reason of choosing 5 here
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H1, sub<F | Beta[2]^p>); // trivial subgroup
Append (~H2, sub<F | Beta[2]^p>); // trivial subgroup
end for;

// G8, 6

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H1, sub<F | Alpha[3], Alpha[5], Beta[2]>);
Append (~H2, sub<F | Alpha[3], Alpha[4]>);
Append (~MinDeg2, p^3 + p^2);

return H1, H2, MinDeg2;
end function;

MAX := 7^6;

for p in PrimesInInterval (5, 11) do 
   "\n process prime ", p;
   L := TablePhi8(p);
   H, MinDeg1 := Check8ACol3(L, p);
   H1, H2, MinDeg2 := Check8BCol3(L, p);
   MinDeg := MinDeg1 cat MinDeg2;

   for i in [1..p] do
     G := L[i];
     Q, phi := pQuotient(G, p, 10);
     A := phi (H[i]);
     m := Index(Q, A);
     C := Core(Q, A);
     assert #C eq 1;
     phiA := CosetAction (Q, A);
     J := Image (phiA);
     // assert IsIsomorphic (J, PF);
     assert #J eq #Q;
     assert Degree (J) eq m;
     assert Degree (J) eq MinDeg[i];
  end for;

  for i in [p+1] do
     G := L[i];
     Q, phi := pQuotient(G, p, 10);
     A := phi (H1[i]);
     B := phi (H2[i]);
     m1 := Index(Q, A);
     m2 := Index(Q, B);
     m := m1 + m2;
     C1 := Core(Q, A);
     C2 := Core(Q, B);
     C := C1 meet C2;
     assert #C eq 1;
     phiA := CosetAction (Q, A);
     phiB := CosetAction (Q, B);
     pi := PermutationRepresentationSumH (Q, [phiA, phiB]);
     J := Image (pi);
     assert #J eq #Q;
     if #J le MAX then assert IsIsomorphic (J, Q); end if;
     assert Degree (J) eq m;
     assert Degree (J) eq MinDeg[i];
  end for;
end for;

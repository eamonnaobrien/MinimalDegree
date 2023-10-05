load "../setup-permrep.m";

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

// Groups G are listed in the list L.
// d(Z(L[i])) = 1 for i = 1 to 5. 
// d(Z(L[i])) = 2 for i = 6 to #L.

// G7 with centre cyclic of order p^2

My7A := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, b1> := FreeGroup (6);
Alpha := [a1, a2, a3, a4, a5];

// common relations, typically commutators
Comms := [
(a2, a3) = 1, (a2, a4)= 1, (a3, a4) = a1,
(a4, a5) = a2, (a3, a5) = 1, (a2, a5) = a1, a1 = b1^p]
cat
[(b1, Alpha[j]) = Id(F) : j in [1..5]];

L := [];

// G7, 1

G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p = b1^(p^2) = 1>;
Append (~L, G);

// G7, 2

G := quo <F | Comms, a2^p = a3^p = a4^p = b1^(p^2) = 1,
a5^p = b1>;
Append (~L, G);

// G7, 3r

for r in [1,nu] do
G := quo <F | Comms, a2^p = a3^p = a5^p = b1^(p^2) = 1,
a4^p = b1^r>;
Append (~L, G);
end for;

// G7, 4

G := quo <F | Comms, a2^p = a4^p = a5^p = b1^(p^2) = 1,
a3^p = b1>;
Append (~L, G);

return L;
end function;

//List for Phi7 with center Cp X Cp

My7B := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, b1, b2> := FreeGroup (7);
Alpha := [a1, a2, a3, a4, a5];
Beta := [b1, b2];

// common relations, typically commutators
Comms := [
(a2, a3) = 1, (a2, a4)= 1, (a3, a4) = a1,
(a4, a5) = a2, (a3, a5) = 1, (a2, a5) = a1, a1 = b1, 
(b1, b2) = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..5]]: i in [1..2]]);

L := [];

// G7, 7

G := quo <F | Comms, a2^p = a3^p = a4^p =  b1^p = b2^p = 1,
a5^p = b2>;
Append (~L, G);

// G7, 9

G := quo <F | Comms, a2^p = a3^p = a5^p = b1^p = b2^p = 1,
a4^p = b2>;
Append (~L, G);

// G7, 11

G := quo <F | Comms, a2^p = a4^p = a5^p = b1^p = b2^p = 1,
a3^p = b2>;
Append (~L, G);

// G7, 12r

for r in [1,nu] do
G := quo <F | Comms, a2^p = a3^p =  b1^p = b2^p = 1,
a4^p = b1^r, a5^p = b2>;
Append (~L, G);
end for;

// G7, 13

G := quo <F | Comms, a2^p = a3^p =  b1^p = b2^p = 1,
a4^p = b2, a5^p = b1>;
Append (~L, G);

// G7, 15

G := quo <F | Comms, a2^p = a4^p =  b1^p = b2^p = 1,
a3^p = b2, a5^p = b1>;
Append (~L, G);

// G7, 16

G := quo <F | Comms, a2^p = a5^p =  b1^p = b2^p = 1,
a3^p = b1, a4^p = b2>;
Append (~L, G);

// G7, 17r

for r in [1,nu] do
G := quo <F | Comms, a2^p = a5^p =  b1^p = b2^p = 1,
a3^p = b2, a4^p = b1^r>;
Append (~L, G);
end for;

return L;
end function;

TablePhi7 := function(p)
   return My7A(p) cat My7B(p);
end function;

// Checking of column "H"

Check7ACol3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 0;
H := [];
MinDeg1 := [];

// G7, 1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6];
Append (~H, sub< F | Alpha[2], Alpha[4]>);
Append (~MinDeg1, p^4);

// G7, 2

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6];
Append (~H, sub< F | Alpha[2], Alpha[4]>);
Append (~MinDeg1, p^4);

// G7, 3r

for r in [1,nu] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6];
Append (~H, sub< F | Alpha[3], Alpha[5]>);
Append (~MinDeg1, p^4);
end for;

// G7, 4

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6];
Append (~H, sub< F | Alpha[2], Alpha[4]>);
Append (~MinDeg1, p^4);

return H, MinDeg1;
end function;

Check7BCol3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 5;
H1 := [];
H2 := [];
MinDeg2 := [];

// following setup is done just to ensure that
// |L[i]: H1[i]| + |L[i]: H2[i]| = MinDeg[i].

for r in [1..5] do
F := L[6]; // no particular reason of choosing 5 here
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H1, sub<F | Beta[2]^p>); // trivial subgroup
Append (~H2, sub<F | Beta[2]^p>); // trivial subgroup
end for;

// G7, 7

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H1, sub<F | Alpha[3], Alpha[5]>);
Append (~H2, sub<F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg2, p^3 + p^2);

// G7, 9

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H1, sub<F | Alpha[3], Alpha[4]^p, Alpha[5]>);
Append (~H2, sub<F | Alpha[1], Alpha[2], 
Alpha[3], Alpha[5]>);
Append (~MinDeg2, p^3 + p^2);

// G7, 11

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H1, sub<F | Alpha[2], Alpha[3]^p, Alpha[4]>);
Append (~H2, sub<F | Alpha[2], Alpha[4], Alpha[5]>);
Append (~MinDeg2, p^3 + p^2);

// G7, 12r

for r in [1,nu] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H1, sub<F | Alpha[2], Alpha[3], Alpha[5]^p>);
Append (~H2, sub<F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg2, p^3 + p^2);
end for;

// G7, 13

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H1, sub<F | Alpha[2], Alpha[3], Alpha[5]>);
Append (~H2, sub<F | Alpha[2], Alpha[3], Alpha[4]^p>);
Append (~MinDeg2, p^3 + p^2);

// G7, 15

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H1, sub<F | Alpha[2], Alpha[4], Alpha[5]>);
Append (~H2, sub<F | Alpha[2], Alpha[3]^p, Alpha[4]>);
Append (~MinDeg2, p^3 + p^2);

// G7, 16

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H1, sub<F | Alpha[2], Alpha[4]>);
Append (~H2, sub<F | Alpha[2], Alpha[3], Alpha[5]>);
Append (~MinDeg2, p^3 + p^2);

// G7, 17r

for r in [1,nu] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H1, sub<F | Alpha[2], Alpha[4], Alpha[5]>);
Append (~H2, sub<F | Alpha[2], Alpha[3]>);
Append (~MinDeg2, p^3 + p^2);
end for;

return H1, H2, MinDeg2;
end function;

MAX := 7^6;

for p in PrimesInInterval (5, 11) do 
   "\n process prime ", p;
   L := TablePhi7(p);
   H, MinDeg1 := Check7ACol3(L, p);
   H1, H2, MinDeg2 := Check7BCol3(L, p);
   MinDeg := MinDeg1 cat MinDeg2;

   for i in [1..5] do
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
     assert Degree (J) eq MinDeg[i];
     assert Degree (J) eq m;
  end for;

  for i in [6..#L] do
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

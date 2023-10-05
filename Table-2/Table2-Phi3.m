load "../setup-permrep.m";

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

// Subgroup H is listed in the list H.
// Z(H[i]) is cyclic for i = 1 to 12.
// d(Z(H[i])) = 2 for i = 13 to 15.

// Phi3, G with centre of type Cp^2 x Cp

My3A := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, b1, b2> := FreeGroup (6);
Alpha := [a1, a2, a3, a4];
Beta := [b1, b2];

// common relations, typically commutators
Comms := [
(a2, a3) = 1, (a2, a4)= a1, (a3, a4) = a2, a1 = b1^p,
(b1, b2) = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..4]]: i in [1..2]]);

L := [];

// G3, 4

G := quo <F | Comms, a2^p = a3^p = a4^p = b1^(p^2) = b2^p = 1>;
Append (~L, G);

// G3, 5r

for r in [1,nu] do
G := quo <F | Comms, a2^p =  a4^p = b1^(p^2) = b2^p = 1,
a3^p = b1^r>;
Append (~L, G);
end for;

// G3, 7

G := quo <F | Comms, a2^p = a3^p = b1^(p^2) = b2^p = 1,
a4^p = b1>;
Append (~L, G);

return L;
end function;

// Phi3, G with centre of type Cp^2 x Cp, case 2

My3B := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, b1, b2> := FreeGroup (6);
Alpha := [a1, a2, a3, a4];
Beta := [b1, b2];

// common relations, typically commutators
Comms := [
(a2, a3) = 1, (a2, a4)= a1, (a3, a4) = a2, a1 = b2,
(b1, b2) = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..4]]: i in [1..2]]);

L := [];

// G3, 11

G := quo <F | Comms, a2^p = a3^p = a4^p = b1^(p^2) = b2^p = 1>;
Append (~L, G);

// G3, 13r

for r in [1,nu] do
G := quo <F | Comms, a2^p = a4^p = b1^(p^2) = b2^p = 1,
a3^p = b2^r>;
Append (~L, G);
end for;

// G3, 15

G := quo <F | Comms, a2^p = a3^p = b1^(p^2) = b2^p = 1,
a4^p = b2>;
Append (~L, G);

return L;
end function;

// Phi3, G with centre of type Cp x Cp X Cp

My3C := function(p)

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

L := [];

// G3, 18

G := quo <F | Comms, a2^p = a3^p = a4^p = b1^p = b2^p = b3^p = 1>;
Append (~L, G);

// G3, 19r

for r in [1,nu] do
G := quo <F | Comms, a2^p = a4^p = b1^p = b2^p = b3^p = 1,
a3^p = b1^r>;
Append (~L, G);
end for;

// G3, 21

G := quo <F | Comms, a2^p = a3^p = b1^p = b2^p = b3^p = 1,
a4^p = b1>;
Append (~L, G);

// G3, 20

G := quo <F | Comms, a2^p = a4^p = b1^p = b2^p = b3^p = 1,
a3^p = b2>;
Append (~L, G);

// G3, 22

G := quo <F | Comms, a2^p = a3^p = b1^p = b2^p = b3^p = 1,
a4^p = b2>;
Append (~L, G);

// G3, 23

G := quo <F | Comms, a2^p =  b1^p = b2^p = b3^p = 1,
a3^p = b2, a4^p = b1>;
Append (~L, G);

return L;
end function;

Table2Phi3 := function(p)
  return My3A(p) cat My3B(p) cat My3C(p);
end function;

// Checking of column "H"

Check3ACol3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 0;
H1 := [];
S1 := [];
MinDeg1 := [];
GMinDeg1 := [];

// G3, 4

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4]; Beta := [F.5, F.6];
Append (~H1, sub< F | Alpha[1], Alpha[2],
Alpha[3], Alpha[4], Beta[1]>);
Append (~S1, sub< F | Alpha[2], Alpha[3]>);
Append (~MinDeg1, p^3);
Append (~GMinDeg1, p^3 + p);

// G3, 5r

for r in [1,nu] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4]; Beta := [F.5, F.6];
Append (~H1, sub< F | Alpha[1], Alpha[2],
Alpha[3], Alpha[4], Beta[1]>);
Append (~S1, sub< F | Alpha[2]>);
Append (~MinDeg1, p^4);
Append (~GMinDeg1, p^4 + p);
end for;

// G3, 7

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4]; Beta := [F.5, F.6];
Append (~H1, sub< F | Alpha[1], Alpha[2],
Alpha[3], Alpha[4], Beta[1]>);
Append (~S1, sub< F | Alpha[2], Alpha[3]>);
Append (~MinDeg1, p^3);
Append (~GMinDeg1, p^3 + p);

return H1, S1, MinDeg1, GMinDeg1;
end function;

Check3BCol3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 4;
H2 := [];
S2 := [];
MinDeg2 := [];
GMinDeg2 := [];

// G3, 11

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4]; Beta := [F.5, F.6];
Append (~H2, sub< F | Alpha[1], Alpha[2],
Alpha[3], Alpha[4], Beta[2]>);
Append (~S2, sub< F | Alpha[2], Alpha[3]>);
Append (~MinDeg2, p^2);
Append (~GMinDeg2, 2 * p^2);

// G3, 13r

for r in [1,nu] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4]; Beta := [F.5, F.6];
Append (~H2, sub< F | Alpha[1], Alpha[2],
Alpha[3], Alpha[4], Beta[2]>);
Append (~S2, sub< F | Alpha[2]>);
Append (~MinDeg2, p^3);
Append (~GMinDeg2, p^3 + p^2);
end for;

// G3, 15

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4]; Beta := [F.5, F.6];
Append (~H2, sub< F | Alpha[1], Alpha[2],
Alpha[3], Alpha[4], Beta[2]>);
Append (~S2, sub< F | Alpha[2], Alpha[3]>);
Append (~MinDeg2, p^2);
Append (~GMinDeg2, 2*p^2);

return H2, S2, MinDeg2, GMinDeg2;
end function;

Check3CCol3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 8;
H3 := [];
S3 := [];
MinDeg3 := [];
GMinDeg3 := [];

// G3, 18

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4]; Beta := [F.5, F.6, F.7];
Append (~H3, sub< F | Alpha[1], Alpha[2],
Alpha[3], Alpha[4], Beta[1]>);
Append (~S3, sub<F | Alpha[2], Alpha[3]>);
Append (~MinDeg3, p^2);
Append (~GMinDeg3, p^2 + 2*p);

// G3, 19r

for r in [1,nu] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4]; Beta := [F.5, F.6, F.7];
Append (~H3, sub< F | Alpha[1], Alpha[2],
Alpha[3], Alpha[4], Beta[1]>);
Append (~S3, sub<F | Alpha[2]>);
Append (~MinDeg3, p^3);
Append (~GMinDeg3, p^3 + 2*p);
end for;

// G3, 21

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4]; Beta := [F.5, F.6, F.7];
Append (~H3, sub< F | Alpha[1], Alpha[2],
Alpha[3], Alpha[4], Beta[1]>);
Append (~S3, sub<F | Alpha[2], Alpha[3]>);
Append (~MinDeg3, p^2);
Append (~GMinDeg3, p^2 + 2*p);

return H3, S3, MinDeg3, GMinDeg3;
end function;

Check3DCol3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 12;
H4 := [];
T1 := [];
T2 := [];
MinDeg4 := [];
GMinDeg4 := [];

// following setup is done just to ensure that
// |G: T1[i]| + |G: T2[i]| = MinDeg4[i].

for r in [1..12] do
F := L[13]; // no particular reason of choosing 13 here
Alpha := [F.1, F.2, F.3, F.4]; Beta := [F.5, F.6];
Append (~T1, sub<F | Beta[2]^p>); // trivial subgroup
Append (~T2, sub<F | Beta[2]^p>); // trivial subgroup
end for;

// G3, 20

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4]; Beta := [F.5, F.6, F.7];
Append (~H4, sub< F | Alpha[1], Alpha[2],
Alpha[3], Alpha[4], Beta[1], Beta[2]>);
Append (~T1, sub<F | Alpha[1], Alpha[2], Alpha[4]>);
Append (~T2, sub<F | Alpha[2], Alpha[3]>);
Append (~MinDeg4, 2*p^2);
Append (~GMinDeg4, 2*p^2 + p);

// G3, 22

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4]; Beta := [F.5, F.6, F.7];
Append (~H4, sub< F | Alpha[1], Alpha[2],
Alpha[3], Alpha[4], Beta[1], Beta[2]>);
Append (~T1, sub<F | Alpha[2], Alpha[3], Alpha[4]^p>);
Append (~T2, sub<F | Alpha[1], Alpha[2], Alpha[3]>);
Append (~MinDeg4, 2*p^2);
Append (~GMinDeg4, 2*p^2 + p);

// G3, 23

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4]; Beta := [F.5, F.6, F.7];
Append (~H4, sub< F | Alpha[1], Alpha[2],
Alpha[3], Alpha[4], Beta[1], Beta[2]>);
Append (~T1, sub<F | Alpha[2], Alpha[4]>);
Append (~T2, sub<F | Alpha[2], Alpha[3]>);
Append (~MinDeg4, 2*p^2);
Append (~GMinDeg4, 2*p^2 + p);

return H4, T1, T2, MinDeg4, GMinDeg4;
end function;

MAX := 7^6;

for p in PrimesInInterval (5, 11) do 
   "\n process prime ", p;
   L := Table2Phi3(p);

   H1, S1, MinDeg1, GMinDeg1 := Check3ACol3(L, p);
   H2, S2, MinDeg2, GMinDeg2 := Check3BCol3(L, p);
   H3, S3, MinDeg3, GMinDeg3 := Check3CCol3(L, p);
   H4, T1, T2, MinDeg4, GMinDeg4 := Check3DCol3(L, p);
   S := S1 cat S2 cat S3;
   H := H1 cat H2 cat H3 cat H4;
   MinDeg := MinDeg1 cat MinDeg2 cat MinDeg3 cat MinDeg4;
   GMinDeg := GMinDeg1 cat GMinDeg2 cat GMinDeg3 cat GMinDeg4;

   for i in [1..12] do
     G := L[i];
     Q, phi := pQuotient(G, p, 10);

     // setup perm rep for non-abelian factor H 
     R := phi (H[i]);
     A := phi (S[i]);
     m := Index(R, A);
     C := Core(R, A);
     assert #C eq 1;
     phiA := CosetAction (R, A);
     J := Image (phiA);
     assert #J eq #R;
     assert Degree (J) eq MinDeg[i];

     // setup perm rep for G 
     I, IS := DetermineMinRep (G, Q, R, [A], phi);
     assert #&meet[Core (Q, s): s in IS] eq 1;
     assert #I eq #Q;
     if #Q le MAX then assert IsIsomorphic (I, Q); end if;
     assert Degree (I) eq GMinDeg[i];
  end for;

  for i in [13..#L] do
     G := L[i];
     Q, phi := pQuotient(G, p, 10);

     // setup perm rep for non-abelian factor H 
     R := phi (H[i]);
     A := phi (T1[i]);
     B := phi (T2[i]);
     m1 := Index(R, A);
     m2 := Index(R, B);
     m := m1 + m2;
     C1 := Core(R, A);
     C2 := Core(R, B);
     C := C1 meet C2;
     assert #C eq 1;
     phiA := CosetAction (R, A);
     phiB := CosetAction (R, B);
     pi := PermutationRepresentationSumH (R, [phiA, phiB]);
     J := Image (pi);
     assert #J eq #R;
     if #J le MAX then assert IsIsomorphic (J, R); end if;
     assert Degree (J) eq m;
     assert Degree (J) eq MinDeg[i];

     // setup perm rep for G 
     I, IS := DetermineMinRep (G, Q, R, [A, B], phi);
     assert #&meet[Core (Q, s): s in IS] eq 1;
     assert #I eq #Q;
     if #Q le MAX then assert IsIsomorphic (I, Q); end if;
     assert Degree (I) eq GMinDeg[i];
   end for;
end for;

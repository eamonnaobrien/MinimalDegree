load "../setup-permrep.m";

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

// G3 with centre of order cyclic of order p^3

// Groups G are listed in the list L.
// Z(L[i]) is cyclic for i = 1 to 4. 
// d(Z(L[i])) = 2 for i = 5 to 10. 
// d(Z(L[i])) = 3 for i = 11.

My3A := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, b1> := FreeGroup (5);
Alpha := [a1, a2, a3, a4];

// common relations, typically commutators
Comms := [
(a2, a3) = 1, (a2, a4)= a1, (a3, a4) = a2,
 a1 = b1^(p^2)]
cat
[(b1, Alpha[j]) = Id(F) : j in [1..4]];

L := [];

// G3, 1

G := quo <F | Comms, a2^p = a3^p = a4^p = b1^(p^3) = 1>;
Append (~L, G);

// G3, 2r

for r in [1,nu] do
G := quo <F | Comms, a2^p = a4^p = b1^(p^3) = 1,
a3^p = b1^r>;
Append (~L, G);
end for; 

// G3, 3

G := quo <F | Comms, a2^p = a3^p =  b1^(p^3) = 1,
a4^p = b1>;
Append (~L, G);

return L;
end function;

// G3 with centre of type Cp^2 x Cp, case 1

My3B := function(p)

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

// G3, 6

G := quo <F | Comms, a2^p = a4^p = b1^(p^2) = b2^p = 1,
a3^p = b2>;
Append (~L, G);


// G3, 8

G := quo <F | Comms, a2^p = a3^p = b1^(p^2) = b2^p = 1,
a4^p = b2>;
Append (~L, G);

// G3, 9

G := quo <F | Comms, a2^p =  b1^(p^2) = b2^p = 1,
a3^p = b2, a4^p = b1>;
Append (~L, G);

return L;
end function;


// G3 with centre of type Cp^2 x Cp, case 2

My3C := function(p)

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


// G3, 12

G := quo <F | Comms, a2^p = a4^p = b1^(p^2) = b2^p = 1,
a3^p = b1>;
Append (~L, G);


// G3, 14

G := quo <F | Comms, a2^p = a3^p = b1^(p^2) = b2^p = 1,
a4^p = b1>;
Append (~L, G);


// G3, 17

G := quo <F | Comms, a2^p =  b1^(p^2) = b2^p = 1,
a3^p = b1, a4^p = b2>;
Append (~L, G);

return L;
end function;


// G3 with centre of type Cp x Cp X Cp

My3D := function(p)

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

// G3, 25

G := quo <F | Comms, a2^p =  b1^p = b2^p = b3^p = 1,
a3^p = b3, a4^p = b2>;
Append (~L, G);

return L;
end function;

MyTablePhi3 := function(p)
    return My3A(p) cat My3B(p) cat My3C(p) cat My3D(p);
end function;

// Checking of column "H"

Check3ACol3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 0;
H := [];
MinDeg1 := [];

// G3, 1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4]; Beta := F.5;
Append (~H, sub< F | Alpha[2], Alpha[3]>);
Append (~MinDeg1, p^4);

// G3, 2r

for r in [1, nu] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4]; Beta := F.5;
Append (~H, sub< F | Alpha[2]>);
Append (~MinDeg1, p^5);
end for;

// G3, 3

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4]; Beta := F.5;
Append (~H, sub< F | Alpha[2], Alpha[3]>);
Append (~MinDeg1, p^4);

return H, MinDeg1;
end function;

// H, MinDeg1 := Check3ACol3(L);

Check3BCol3 := function (L, p)

Z := Integers ();
    nu := Z ! (NonQuadraticResidue (p)); // nu

count := 4;
H11 := [];
H21 := [];
MinDeg2 := [];

// following setup is done just to ensure that
// |L[i]: H11[i]| + |L[i]: H21[i]| = MinDeg[i].

for r in [1..4] do
F := L[5]; // no particular reason of choosing 5 here
Alpha := [F.1, F.2, F.3, F.4]; Beta := [F.5, F.6];
Append (~H11, sub<F | Beta[2]^p>); // trivial subgroup
Append (~H21, sub<F | Beta[2]^p>); // trivial subgroup
end for;

// G3, 6

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4]; Beta := [F.5, F.6];
Append (~H11, sub<F | Alpha[2], Alpha[3]>);
Append (~H21, sub<F | Alpha[2], Alpha[4], Beta[1]>);
Append (~MinDeg2, p^3 + p^2);

// G3, 8

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4]; Beta := [F.5, F.6];
Append (~H11, sub<F | Alpha[2], Alpha[3], Alpha[4]^p>);
Append (~H21, sub<F | Alpha[2], Alpha[3], Beta[1]>);
Append (~MinDeg2, p^3 + p^2);

// G3, 9

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4]; Beta := [F.5, F.6];
Append (~H11, sub<F | Alpha[2], Alpha[4]>);
Append (~H21, sub<F | Alpha[2], Alpha[3]>);
Append (~MinDeg2, p^3 + p^2);

return H11, H21, MinDeg2;
end function;

// H11, H21, MinDeg2 := Check3BCol3(L);


Check3CCol3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 7;
H12 := [];
H22 := [];
MinDeg3 := [];

// G3, 12

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4]; Beta := [F.5, F.6];
Append (~H12, sub<F | Alpha[2], Alpha[3]>);
Append (~H22, sub<F | Alpha[1], Alpha[2], Alpha[4]>);
Append (~MinDeg3, p^3 + p^2);

// G3, 14

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4]; Beta := [F.5, F.6];
Append (~H12, sub<F | Alpha[2], Alpha[3], Alpha[4]^p>);
Append (~H22, sub<F | Alpha[1], Alpha[2], Alpha[3]>);
Append (~MinDeg3, p^3 + p^2);

// G3, 17

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4]; Beta := [F.5, F.6];
Append (~H12, sub<F | Alpha[2], Alpha[4]>);
Append (~H22, sub<F | Alpha[2], Alpha[3]>);
Append (~MinDeg3, p^3 + p^2);

return H12, H22, MinDeg3;
end function;

// H12, H22, MinDeg3 := Check3CCol3(L);

// H1 := H11 cat H12;
// H2 := H21 cat H22;


Check3DCol3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 10;
T1 := [];
T2 := [];
T3 := [];
MinDeg4 := [];

// following setup is done just to ensure that
// |L[i]: T1[i]| + |L[i]: T2[i]| + |L[i]: T3[i]| = MinDeg[i].

for r in [1..10] do
F := L[11]; // no particular reason of choosing L[11] here
Alpha := [F.1, F.2, F.3, F.4]; Beta := [F.5, F.6, F.7];
Append (~T1, sub<F | Beta[3]^p>); // trivial subgroup
Append (~T2, sub<F | Beta[3]^p>); // trivial subgroup
Append (~T3, sub<F | Beta[3]^p>); // trivial subgroup
end for;

// G3, 25

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4]; Beta := [F.5, F.6, F.7];
Append (~T1, sub<F | Alpha[2], Alpha[3], Alpha[4]^p>);
Append (~T2, sub<F | Alpha[1], Alpha[2], Alpha[3]>);
Append (~T3, sub<F | Alpha[1], Alpha[2], Alpha[4]>);
Append (~MinDeg4, 3*p^2);

return T1, T2, T3, MinDeg4;
end function;

MAX := 7^6;

for p in PrimesInInterval (5, 11) do 
   "\n process prime ", p;
   L := MyTablePhi3(p);
   assert #L eq 11;

   H, MinDeg1 := Check3ACol3(L, p);
   H11, H21, MinDeg2 := Check3BCol3(L, p);
   H12, H22, MinDeg3 := Check3CCol3(L, p);
   H1 := H11 cat H12;
   H2 := H21 cat H22;
   T1, T2, T3, MinDeg4 := Check3DCol3(L, p);
   MinDeg := MinDeg1 cat MinDeg2 cat MinDeg3 cat MinDeg4;

   for i in [1..4] do
     G := L[i];
     Q, phi := pQuotient(G, p, 10);
     A := phi (H[i]);
     m := Index(Q, A);
     C := Core(Q, A);
     assert #C eq 1;
     phiA := CosetAction (Q, A);
     J := Image (phiA);
     assert #J eq #Q;
     assert Degree (J) eq MinDeg[i];
  end for;

  for i in [5..10] do
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

  for i in [11] do
     G := L[i];
     Q, phi := pQuotient(G, p, 10);
     A := phi(T1[i]);
     B := phi(T2[i]);
     C := phi(T3[i]);
     m1 := Index(Q, A);
     m2 := Index(Q, B);
     m3 := Index(Q, C);
     m := m1 + m2 + m3;
     C1 := Core(Q, A);
     C2 := Core(Q, B);
     C3 := Core(Q, C);
     CI := C1 meet C2 meet C3;
     assert #CI eq 1;
     phiA := CosetAction (Q, A);
     phiB := CosetAction (Q, B);
     phiC := CosetAction (Q, C);
     pi := PermutationRepresentationSumH (Q, [phiA, phiB, phiC]);
     J := Image (pi);
     assert #J eq #Q;
     if #J le MAX then assert IsIsomorphic (J, Q); end if;
     assert Degree (J) eq m;
     assert Degree (J) eq MinDeg[i];
  end for;
end for;

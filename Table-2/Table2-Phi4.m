load "../setup-permrep.m";

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

// Subgroup H is listed in the list H.
// d(Z(H[i])) = 2 for each i.
// Lists T1 and T2 each store a subgroup of H.

// Phi4, G with centre of type Cp x Cp x Cp 

Table2Phi4 := function(p)

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

L := [];

// G4, 14

G := quo <F | Comms, a3^p = a4^p = a5^p = b1^p = b2^p = b3^p = 1>;
Append (~L, G);

// G4, 15

G := quo <F | Comms, a3^p = a4^p = b1^p = b2^p = b3^p = 1, 
a5^p = b2>;
Append (~L, G);

// G4, 16

G := quo <F | Comms, a3^p =  b1^p = b2^p = b3^p = 1, 
a4^p = b2, a5^p = b1>;
Append (~L, G);

// G4, 17

G := quo <F | Comms, a3^p = a5^p= b1^p = b2^p = b3^p = 1, 
a4^p = b2>;
Append (~L, G);

// G4, 20

G := quo <F | Comms, a5^p =  b1^p = b2^p = b3^p = 1, 
a3^p = b1, a4^p = b2>;
Append (~L, G);

// G4, 21r

for r in [1..(p-3) div 2] do
G := quo <F | Comms, a5^p =  b1^p = b2^p = b3^p = 1, 
a3^p = b1^(w^r mod p), a4^p = b2>;
Append (~L, G);
end for;

// G4, 22

G := quo <F | Comms, a5^p =  b1^p = b2^p = b3^p = 1, 
a3^p = b2, a4^p = b1>;
Append (~L, G);

return L;
end function;

// Checking of column "H"

CheckPhi4Col3 := function (L, p)

w := PrimitiveRoot(p);

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 0;
H := [];
T1 := [];
T2 := [];
MinDeg := [];
GMinDeg := [];

// G4, 14

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7, F.8];
Append (~H, sub< F | Alpha[1], Alpha[2], Alpha[3],
Alpha[4], Alpha[5], Beta[1], Beta[2]>);
Append (~T1, sub<F | Alpha[2], Alpha[4], Alpha[5]>);
Append (~T2, sub<F | Alpha[1], Alpha[3], Alpha[4]>);
Append (~MinDeg, 2*p^2);
Append (~GMinDeg, 2*p^2 + p);

// G4, 15

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7, F.8];
Append (~H, sub< F | Alpha[1], Alpha[2], Alpha[3],
Alpha[4], Alpha[5], Beta[1], Beta[2]>);
Append (~T1, sub<F | Alpha[4], Alpha[5]>);
Append (~T2, sub<F | Alpha[1], Alpha[3], Alpha[4]>);
Append (~MinDeg, 2*p^2);
Append (~GMinDeg, 2*p^2 + p);

// G4, 16

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7, F.8];
Append (~H, sub< F | Alpha[1], Alpha[2], Alpha[3],
Alpha[4], Alpha[5], Beta[1], Beta[2]>);
Append (~T1, sub<F | Alpha[3], Alpha[5]>);
Append (~T2, sub<F | Alpha[3], Alpha[4]>);
Append (~MinDeg, 2*p^2);
Append (~GMinDeg, 2*p^2 + p);

// G4, 17

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7, F.8];
Append (~H, sub< F | Alpha[1], Alpha[2], Alpha[3],
Alpha[4], Alpha[5], Beta[1], Beta[2]>);
Append (~T1, sub<F | Alpha[1], Alpha[3], Alpha[5]>);
Append (~T2, sub<F | Alpha[4], Alpha[5]>);
Append (~MinDeg, 2*p^2);
Append (~GMinDeg, 2*p^2 + p);

// G4, 20

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7, F.8];
Append (~H, sub< F | Alpha[1], Alpha[2], Alpha[3],
Alpha[4], Alpha[5], Beta[1], Beta[2]>);
Append (~T1, sub<F | Alpha[3], Alpha[5]>);
Append (~T2, sub<F | Alpha[4], Alpha[5]>);
Append (~MinDeg, 2*p^2);
Append (~GMinDeg, 2*p^2 + p);

// G4, 21r

for r in [1..(p-3) div 2] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7, F.8];
Append (~H, sub< F | Alpha[1], Alpha[2], Alpha[3],
Alpha[4], Alpha[5], Beta[1], Beta[2]>);
Append (~T1, sub<F | Alpha[3], Alpha[5]>);
Append (~T2, sub<F | Alpha[4], Alpha[5]>);
Append (~MinDeg, 2*p^2);
Append (~GMinDeg, 2*p^2 + p);
end for;

// G4, 22

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7, F.8];
Append (~H, sub< F | Alpha[1], Alpha[2], Alpha[3],
Alpha[4], Alpha[5], Beta[1], Beta[2]>);
Append (~T1, sub<F | Alpha[4]*Alpha[3], Alpha[5]>);
Append (~T2, sub<F | Alpha[4]*Alpha[3]^(-1), Alpha[5]>);
Append (~MinDeg, 2*p^2);
Append (~GMinDeg, 2*p^2 + p);

return H, T1, T2, MinDeg, GMinDeg;
end function;

MAX := 7^6;

for p in PrimesInInterval (5, 11) do 
   "\n process prime ", p;
   L := Table2Phi4(p);

   H, T1, T2, MinDeg, GMinDeg := CheckPhi4Col3(L, p);
   for i in [1..#L] do
     G := L[i];
     Q, phi := pQuotient(G, p, 10);

     // setup perm rep for H 
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
     assert Degree (I) eq GMinDeg[i];
     if #Q le MAX then assert IsIsomorphic (I, Q); end if;

   end for;
end for;


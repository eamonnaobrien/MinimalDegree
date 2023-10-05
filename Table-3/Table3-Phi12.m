load "../setup-permrep.m";

//Phi12 with center Cp X Cp

My12 := function(p)

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a3, a4, a5, a6];
Beta := [a1, a2];

// common relations, typically commutators
Comms := [
(a3, a4) = a1, (a3, a5)= 1, (a3, a6) = 1,
(a4, a5) = 1, (a4, a6)= 1, (a5, a6)= a2,  
(a1, a2) = 1, a1^p = 1, a2^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..4]]: i in [1..2]]);

L := [];

// G12, 1

G := quo <F | Comms, a3^p = a4^p = a5^p = a6^p = 1>;
Append (~L, G);

// G12, 2

G := quo <F | Comms,  a4^p = a5^p = a6^p = 1,
a3^p = a1>;
Append (~L, G);

// G12, 3

G := quo <F | Comms,  a4^p = a5^p = a6^p = 1,
a3^p = a2>;
Append (~L, G);

// G12, 4

G := quo <F | Comms,  a4^p = a5^p = a6^p = 1,
a3^p = a1*a2>;
Append (~L, G);

// G12, 5

G := quo <F | Comms, a3^p = a6^p = 1,
a4^p = a1, a5^p = a1>;
Append (~L, G);

// G12, 7

G := quo <F | Comms,  a5^p = a6^p = 1,
a3^p = a1, a4^p = a2>;
Append (~L, G);

// G12, 8

G := quo <F | Comms,  a4^p = a6^p = 1,
a3^p = a1, a5^p = a2>;
Append (~L, G);

// G12, 11

G := quo <F | Comms,  a4^p = a6^p = 1,
a3^p = a1*a2, a5^p = a2>;
Append (~L, G);

return L;
end function;

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

Check12Col3 := function (L, p)
Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 0;
H1 := [];
H2 := [];
MinDeg := [];

// G12, 1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6]; 
Append (~H1, sub<F | Alpha[1], Alpha[4], 
Alpha[3], Alpha[5]>);
Append (~H2, sub<F | Alpha[2], Alpha[4], 
Alpha[5], Alpha[6]>);
Append (~MinDeg, 2*p^2);

// G12, 2

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6]; 
Append (~H1, sub<F | Alpha[1], Alpha[3],
Alpha[4], Alpha[5]>);
Append (~H2, sub<F | Alpha[2], Alpha[4], 
Alpha[5], Alpha[6]>);
Append (~MinDeg, 2*p^2);

// G12, 3

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6]; 
Append (~H1, sub<F | Alpha[1], 
Alpha[4], Alpha[6]>);
Append (~H2, sub<F | Alpha[2], Alpha[3], 
Alpha[5], Alpha[6]>);
Append (~MinDeg, p^3 + p^2);

// G12, 4

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6]; 
Append (~H1, sub<F | Alpha[1], 
Alpha[4], Alpha[6]>);
Append (~H2, sub<F | Alpha[2], Alpha[5], 
Alpha[4], Alpha[6]>);
Append (~MinDeg, p^3 + p^2);

// G12, 5

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6]; 
Append (~H1, sub<F | Alpha[2], 
Alpha[3], Alpha[6]>);
Append (~H2, sub<F | Alpha[3], Alpha[4], 
Alpha[5]>);
Append (~MinDeg, p^3 + p^2);

// G12, 7

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6]; 
Append (~H1, sub<F | Alpha[5], Alpha[3]>);
Append (~H2, sub<F | Alpha[4], Alpha[5], 
Alpha[6]>);
Append (~MinDeg, p^3 + p^2);

// G12, 8

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6]; 
Append (~H1, sub<F | Alpha[1], Alpha[3], 
Alpha[4], Alpha[6]>);
Append (~H2, sub<F | Alpha[2], Alpha[5], 
Alpha[4], Alpha[6]>);
Append (~MinDeg, 2*p^2);

// G12, 11

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6]; 
Append (~H1, sub<F | Alpha[3], Alpha[6]>);
Append (~H2, sub<F | Alpha[4], Alpha[5], 
Alpha[6]>);
Append (~MinDeg, p^3 + p^2);

return H1, H2, MinDeg;
end function;

MAX := 7^6;

for p in PrimesInInterval (5, 11) do 
   "\n process prime ", p;
   L := My12(p);
   H1, H2, MinDeg := Check12Col3(L, p);

   for i in [1..#L] do
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

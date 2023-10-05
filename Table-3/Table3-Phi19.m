load "../setup-permrep.m";

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

//Phi19 with center Cp X Cp

My19 := function(p)

K := GF(p);

w := PrimitiveRoot(p);

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a, a1, a2, b, b1, b2> := FreeGroup (6);
Alpha := [a, a1, a2, b];
Beta := [b1, b2];

// common relations, typically commutators
Comms := [
(a, a1) = b1, (a, a2)= 1, (a, b) = 1,
(a1, a2) = b, (b, a1)= b1, (b, a2)= b2,  
(b1, b2) = 1, b1^p = 1, b2^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j
 in [1..4]]: i in [1..2]]);

L := [];

// (2211)a

G := quo <F | Comms, a^p = b^p  = 1,
a1^p = b1, a2^p = b2>;
Append (~L, G);

// (2211)b_r

for r in [1..(p-1) div 2] do
G := quo <F | Comms, a^p = b^p  = 1,
a1^p = b1, a2^p = b2^(w^r mod p)>;
Append (~L, G);
end for;

// (21^4)a

G := quo <F | Comms, a^p = b^p  = 1,
a1^p = b1, a2^p = 1>;
Append (~L, G);

return L;
end function;

Check19Col3 := function (L, p)
Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 0;
H1 := [];
H2 := [];
MinDeg := [];

// 2211, a

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6]; 
Append (~H1, sub<F | Alpha[1], Alpha[2], Alpha[4]>);
Append (~H2, sub<F | Alpha[1], Alpha[3], Alpha[4]>);
Append (~MinDeg, 2*p^2);

// 2211, b_r

for r in [1..(p-1) div 2] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6]; 
Append (~H1, sub<F | Alpha[1], Alpha[2], Alpha[4]>);
Append (~H2, sub<F | Alpha[1], Alpha[3], Alpha[4]>);
Append (~MinDeg, 2*p^2);
end for;

// 21^4, a

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6]; 
Append (~H1, sub<F | Alpha[1], Alpha[2], Alpha[4]>);
Append (~H2, sub<F | Alpha[1], Alpha[3], Alpha[4]>);
Append (~MinDeg, 2*p^2);

return H1, H2, MinDeg;
end function;

MAX := 7^6;

for p in PrimesInInterval (5, 11) do
   "\n process prime ", p;
   L := My19(p);
   H1, H2, MinDeg := Check19Col3(L, p);

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

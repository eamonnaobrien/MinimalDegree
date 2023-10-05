load "../setup-permrep.m";

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

// Groups G are listed in the list L.
// d(Z(L[i])) = 2 for i = 1 to #L.

//Phi18 with center Cp X Cp

My18 := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a3, a4, a5, a6];
Beta := [a1, a2];

// common relations, typically commutators
Comms := [
(a3, a4) = 1, (a3, a5)= 1, (a3, a6) = a1,
(a4, a5) = a1, (a4, a6)= a2, (a5, a6)= a3,  
(a1, a2) = 1, a1^p = 1, a2^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..4]]: i in [1..2]]);

L := [];

// G18, 7

G := quo <F | Comms, a3^p = a5^p = a6^p =  1,
a4^p = a2>;
Append (~L, G);

// G18, 11

G := quo <F | Comms, a3^p = a5^p =  1,
a4^p = a2, a6^p = a1>;
Append (~L, G);

// G18, 13r

for r in [1..(p-1)] do
G := quo <F | Comms, a3^p = a6^p =  1,
a4^p = a2, a5^p = a1^r>;
Append (~L, G);
end for;

return L;
end function;

Check18Col3 := function (L, p)

Z := Integers ();
    nu := Z ! (NonQuadraticResidue (p)); // nu

count := 0;
H1 := [];
H2 := [];
MinDeg := [];

// G18, 7

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6]; 
Append (~H1, sub<F | Alpha[4], Alpha[6]>);
Append (~H2, sub<F | Alpha[1], Alpha[3], 
Alpha[5], Alpha[6]>);
Append (~MinDeg, p^3 + p^2);

// G18, 11

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6]; 
Append (~H1, sub<F | Alpha[3], Alpha[5], Alpha[6]>);
Append (~H2, sub<F | Alpha[3], Alpha[4]>);
Append (~MinDeg, p^3 + p^2);

// G18, 13r

for r in [1..(p-1)] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6]; 
Append (~H1, sub<F | Alpha[3], Alpha[5], Alpha[6]>);
Append (~H2, sub<F | Alpha[3], Alpha[4]>);
Append (~MinDeg, p^3 + p^2);
end for;

return H1, H2, MinDeg;
end function;

MAX := 7^6;

for p in PrimesInInterval (5, 11) do
   "\n process prime ", p;
   L := My18(p);
   H1, H2, MinDeg := Check18Col3(L, p);

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

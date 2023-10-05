load "../setup-permrep.m";

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

// Groups G are listed in the list L.
// d(Z(L[i])) = 2 for i = 1 to #L.

//Phi20 with center Cp X Cp

My20 := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a3, a4, a5, a6];
Beta := [a1, a2];

// common relations, typically commutators
Comms := [
(a3, a4) = 1, (a3, a5)= a1, (a3, a6) = a2,
(a4, a5) = 1, (a4, a6)= a1^(-1), (a5, a6)= a3,  
(a1, a2) = 1, a1^p = 1, a2^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..4]]: i in [1..2]]);

L := [];

// G20, 14

G := quo <F | Comms, a3^p = a5^p = 1,
a4^p = a1, a6^p = a2>;
Append (~L, G);

return L;
end function;

//Phi23 with center Cp X Cp

My23 := function(p)

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a3, a4, a5, a6];
Beta := [a1, a2];

// common relations, typically commutators
Comms := [
(a3, a4) = 1, (a3, a5)= 1, (a3, a6) = a1,
(a4, a5) = a2, (a4, a6)= a3, (a5, a6)= a4,  
(a1, a2) = 1, a1^p = 1, a2^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..4]]: i in [1..2]]);

L := [];

// G23, 1

G := quo <F | Comms, a3^p = a4^p = a5^p = a6^p = 1>;
Append (~L, G);

// G23, 2

G := quo <F | Comms, a3^p = a4^p = a5^p = 1,
a6^p = a1>;
Append (~L, G);

// G23, 9r (r=0)

G := quo <F | Comms, a3^p = a4^p =  1,
a5^p = a2, a6^p = a1>;
Append (~L, G);

return L;
end function;

My20_23 := function(p)
return My20(p) cat My23(p);
end function;

Check20Col3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 0;
H11 := [];
H12 := [];
MinDeg1 := [];

// G20, 14

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6]; 
Append (~H11, sub<F | Alpha[3], Alpha[6]>);
Append (~H12, sub<F | Alpha[3], Alpha[4], Alpha[5]>);
Append (~MinDeg1, p^3 + p^2);

return H11, H12, MinDeg1;
end function;


Check23Col3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 1;
H21 := [];
H22 := [];
MinDeg2 := [];

// G23, 1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6]; 
Append (~H21, sub<F | Alpha[3], Alpha[4], Alpha[6]>);
Append (~H22, sub<F | Alpha[3], Alpha[4], Alpha[5]>);
Append (~MinDeg2, 2*p^2);

// G23, 2

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6]; 
Append (~H21, sub<F | Alpha[3], Alpha[4], Alpha[6]>);
Append (~H22, sub<F | Alpha[2], Alpha[3], 
Alpha[4], Alpha[5]>);
Append (~MinDeg2, 2*p^2);

// G23, 9r (r=0)

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6]; 
Append (~H21, sub<F | Alpha[3], Alpha[4], Alpha[6]>);
Append (~H22, sub<F | Alpha[3], Alpha[4], Alpha[5]>);
Append (~MinDeg2, 2*p^2);

return H21, H22, MinDeg2;
end function;

MAX := 7^6;

for p in PrimesInInterval (5, 11) do 
   "\n process prime ", p;
   L := My20_23(p);
   H11, H12, MinDeg1 := Check20Col3(L, p);
   H21, H22, MinDeg2 := Check23Col3(L, p);
   H1 := H11 cat H21;
   H2 := H12 cat H22;
   MinDeg := MinDeg1 cat MinDeg2;

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

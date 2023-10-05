load "../setup-permrep.m";

// Phi5 with centre of order cyclic of order p^2

My5A := function(p)

F<a1, a2, a3, a4, a5, b1> := FreeGroup (6);
Alpha := [a1, a2, a3, a4, a5];

// common relations, typically commutators
Comms := [
(a2, a3) = 1, (a2, a4)= 1, (a3, a4) = a1,
(a4, a5) = 1, (a3, a5) = 1, (a2, a5) = a1, a1 = b1^p]
cat
[(b1, Alpha[j]) = Id(F) : j in [1..5]];

L := [];

// G5, 1

G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p = b1^(p^2) = 1>;
Append (~L, G);

// G5, 2

G := quo <F | Comms, a2^p = a3^p = a4^p = b1^(p^2) = 1,
a5^p =  b1>;
Append (~L, G);

return L;
end function;

//List for Phi5 with center Cp X Cp

My5B := function(p)

F<a1, a2, a3, a4, a5, b1, b2> := FreeGroup (7);
Alpha := [a1, a2, a3, a4, a5];
Beta := [b1, b2];

// common relations, typically commutators
Comms := [
(a2, a3) = 1, (a2, a4)= 1, (a3, a4) = a1,
(a4, a5) = 1, (a3, a5) = 1, (a2, a5) = a1, a1 = b1, 
(b1, b2) = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..5]]: i in [1..2]]);

L := [];

// G5, 3

G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p = b1^p = b2^p = 1>;
Append (~L, G);

// G5, 4

G := quo <F | Comms, a2^p = a3^p = a4^p =  b1^p = b2^p = 1,
a5^p = b1>;
Append (~L, G);

// G5, 5

G := quo <F | Comms, a2^p = a3^p = a4^p =  b1^p = b2^p = 1,
a5^p = b2>;
Append (~L, G);

// G5, 6

G := quo <F | Comms, a2^p = a3^p =   b1^p = b2^p = 1,
a4^p = b2, a5^p = b1>;
Append (~L, G);

// G5, 7

G := quo <F | Comms, a3^p = a4^p =   b1^p = b2^p = 1,
a2^p = b2, a5^p = b1>;
Append (~L, G);

return L;
end function;

Table1Phi5 := function(p)
   return My5A(p) cat My5B(p);
end function;

Check5A := function (L, p)

count := 0;
H := [];
MinDeg1 := [];

// G5, 1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := F.6;
Append (~H, sub< F | Alpha[2], Alpha[3]>);
Append (~MinDeg1, p^4);

// G5, 2

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := F.6;
Append (~H, sub< F | Alpha[2], Alpha[3]>);
Append (~MinDeg1, p^4);

return H, MinDeg1;
end function;

Check5B := function (L, p)

count := 2;
H1 := [];
H2 := [];
MinDeg2 := [];

for r in [1..2] do
F := L[3]; // no particular reason of choosing 5 here
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H1, sub<F | Beta[2]^p>); // trivial subgroup
Append (~H2, sub<F | Beta[2]^p>); // trivial subgroup
end for;

// G5, 3

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H1, sub<F | Alpha[2], Alpha[3],
Alpha[4], Alpha[5], Beta[1]>);
Append (~H2, sub<F | Alpha[2], Alpha[3], Beta[2]>);
Append (~MinDeg2, p^3 + p);

// G5, 4

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H1, sub<F | Alpha[2], Alpha[3],
Alpha[4], Alpha[5], Beta[1]>);
Append (~H2, sub<F | Alpha[2], Alpha[3], Beta[2]>);
Append (~MinDeg2, p^3 + p);

// G5, 5

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H1, sub<F | Alpha[2], Alpha[3], Alpha[4], Beta[1]>);
Append (~H2, sub<F | Alpha[2], Alpha[3], Beta[2]>);
Append (~MinDeg2, p^3 + p^2);

// G5, 6

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H1, sub<F | Alpha[2], Alpha[4]>);
Append (~H2, sub<F | Alpha[2], Alpha[3], Alpha[5]>);
Append (~MinDeg2, p^3 + p^2);

// G5, 6

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H1, sub<F | Alpha[2], Alpha[3]>);
Append (~H2, sub<F | Alpha[3], Alpha[4], Alpha[5]>);
Append (~MinDeg2, p^3 + p^2);

return H1, H2, MinDeg2;
end function;

MAX := 5^6;

for p in PrimesInInterval (5, 11) do 
   "\n process prime ", p;
   L := Table1Phi5(p);
   H, MinDeg1 := Check5A(L, p);
   H1, H2, MinDeg2 := Check5B(L, p);
   MinDeg := MinDeg1 cat MinDeg2;

   for i in [1..2] do
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

   for i in [3..#L] do
     G := L[i];
     Q,phi := pQuotient(G, p, 10);
     A := phi (H1[i]);
     B := phi (H2[i]);
     m1 := Index(Q,A);
     m2 := Index(Q,B);
     m := m1 + m2;
     C1 := Core(Q,A);
     C2 := Core(Q,B);
     C := C1 meet C2;
     assert #C eq 1;
     phiA := CosetAction (Q,A);
     phiB := CosetAction (Q,B);
     pi := PermutationRepresentationSumH (Q,[phiA, phiB]);
     J := Image (pi);
     assert #J eq #Q;
     if #J le MAX then assert IsIsomorphic (J, Q); end if;
     assert Degree (J) eq m;
     assert Degree (J) eq MinDeg[i];
  end for;
end for;

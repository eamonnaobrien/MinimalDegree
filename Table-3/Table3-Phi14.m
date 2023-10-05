load "../setup-permrep.m";

//Phi14 with center Cp^2

My14 := function(p)

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a3, a4, a5, a6];
Beta := [a1, a2];

// common relations, typically commutators
Comms := [
(a3, a4) = 1, (a3, a5)= 1, (a3, a6) = a1,
(a4, a5) = a1, (a4, a6)= a2, (a5, a6)= 1,  
(a1, a2) = 1, a1^p = 1, a2^p = a1,
a4^p = a3, a6^p = a5] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..4]]: i in [1..2]]);

L := [];

// G13, 1

G := quo <F | Comms, a3^p = a5^p = 1>;
Append (~L, G);

// G13, 2

G := quo <F | Comms,  a5^p = 1, a3^p = a1>;
Append (~L, G);

// G13, 3

G := quo <F | Comms,  a5^p = 1, a3^p = a2>;
Append (~L, G);

return L;
end function;

Check14 := function(L, p)

count := 0;
H := [];
MinDeg := [];

// G14, 1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H, sub< F | Alpha[6]>);
Append (~MinDeg, p^4);


// G14, 2

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H, sub< F | Alpha[6]>);
Append (~MinDeg, p^4);

// G14, 3

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H, sub< F | Alpha[6]>);
Append (~MinDeg, p^4);

return H, MinDeg;
end function;

MAX := 7^6;

for p in PrimesInInterval (5, 11) do 
   "\n process prime ", p;
   L := My14(p);
   H, MinDeg := Check14(L, p);

   for i in [1..#L] do
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
end for;

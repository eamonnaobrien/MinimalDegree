load "../setup-permrep.m";

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

//Phi15 with center Cp X Cp

My15 := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu
num1 := Z ! (1/NonQuadraticResidue (p)); // nu

//return suitable pairs for case 5k

PairPhi15 := function(k, p)
  for x in GF(p) do
    for y in GF(p) do
      if (x^2 - nu^(-1) * y^2) eq k and x ne 0 and y ne 0 then
        return Z!x,Z!y;
      end if;
    end for;
  end for;
end function;

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a3, a4, a5, a6];
Beta := [a1, a2];

// common relations, typically commutators
Comms := [
(a3, a5) = a1, (a3, a6) = a2,
(a4, a5)= a2, (a4, a6) = a1^nu, 
(a2, a1)= 1,
(a4, a3) = 1, 
(a5, a6) = 1, a1^p = 1, a2^p = 1]
cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..4]]: i in [1..2]]);

L := [];

// G15, 1

G := quo <F | Comms, a6^p = a5^p = a3^p = a4^p = 1>;
Append (~L, G);

// G15, 2

G := quo <F | Comms, a6^p = a5^p = a4^p = 1,
a3^p =  a1>;
Append (~L, G);

// G15, 3

G := quo <F | Comms,  a6^p = a5^p = 1,
a3^p = a1, a4^p = a2>;
Append (~L, G);

// G15, 4

G := quo <F | Comms,  a6^p = a5^p = 1,
a3^p =  a1, a4^p = a2^-1>;
Append (~L, G);

// G15, 5k

for k in [2..p-1] do 
a, b := PairPhi15 (k, p);
G := quo <F | Comms,  a5^p = a6^p = 1,
a3^p =  a1^(1-a) * a2^(-num1 * b), a4^p = a1^b * a2^(1+a)>;
Append (~L, G);
end for;

// G15, 6

G := quo <F | Comms,  a3^p = a5^p = 1,
a6^p =  a2, a4^p = a1>;
Append (~L, G);

return L;
end function;

Check15 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu
num1 := Z ! (1/NonQuadraticResidue (p)); // nu

count := 0;
H1 := [];
H2 := [];
MinDeg := [];

// G15, 1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6]; 
Append (~H1, sub<F | Alpha[1], Alpha[5], Alpha[6]>);
Append (~H2, sub<F | Alpha[2], Alpha[5], Alpha[6]>);
Append (~MinDeg, 2*p^3);

// G15, 2

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6]; 
Append (~H1, sub<F | Alpha[1], Alpha[5], Alpha[6]>);
Append (~H2, sub<F | Alpha[2], Alpha[5], Alpha[6]>);
Append (~MinDeg, 2*p^3);

// G15, 3

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6]; 
Append (~H1, sub<F | Alpha[1], Alpha[5], Alpha[6]>);
Append (~H2, sub<F | Alpha[2], Alpha[5], Alpha[6]>);
Append (~MinDeg, 2*p^3);

// G15, 4

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6]; 
Append (~H1, sub<F | Alpha[1], Alpha[5], Alpha[6]>);
Append (~H2, sub<F | Alpha[2], Alpha[5], Alpha[6]>);
Append (~MinDeg, 2*p^3);

// G15, 5k

for r in [2..(p-1)] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6]; 
Append (~H1, sub<F | Alpha[1], Alpha[5], Alpha[6]>);
Append (~H2, sub<F | Alpha[2], Alpha[5], Alpha[6]>);
Append (~MinDeg, 2*p^3);
end for;

// G15, 6

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6]; 
Append (~H1, sub<F | Alpha[1], Alpha[3], Alpha[5]>);
Append (~H2, sub<F | Alpha[2], Alpha[3], Alpha[6]>);
Append (~MinDeg, 2*p^3);

return H1, H2, MinDeg;
end function;

MAX := 7^6;

for p in PrimesInInterval (5, 11) do
   "\n process prime ", p;
   L := My15(p);
   H1, H2, MinDeg := Check15(L, p);

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

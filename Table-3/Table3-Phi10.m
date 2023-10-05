load "../setup-permrep.m";

// Groups G are listed in the list L.
// d(Z(L[i])) = 1 for i = 1 to GCD(p-1, 3). 
// d(Z(L[i])) = 2 for i = GCD(p-1, 3) to #L.

// G10 with centre of order cyclic of order p^2

My10A := function(p)

F<a1, a2, a3, a4, a5, b1> := FreeGroup (6);
Alpha := [a1, a2, a3, a4, a5];

// common relations, typically commutators
Comms := [
(a2, a3) = 1, (a2, a4)= 1, (a3, a4) = a1,
(a4, a5) = a3, (a3, a5) = a2, (a2, a5) = a1, a1 = b1^p]
cat
[(b1, Alpha[j]) = Id(F) : j in [1..5]];

L := [];

// G10, 3r
w := PrimitiveRoot (p);

if p mod 3 eq 1 then add := [w^i: i in [0..2]];
else add := [1]; end if;
for r in add do
G := quo <F | Comms, a2^p = a3^p = a5^p = b1^(p^2) = 1,
               a4^p = b1^r>;
Append (~L, G);
end for;

return L;
end function;

//List for Phi10 with center Cp X Cp

My10B := function(p)

F<a1, a2, a3, a4, a5, b1, b2> := FreeGroup (7);
Alpha := [a1, a2, a3, a4, a5];
Beta := [b1, b2];

// common relations, typically commutators
Comms := [
(a2, a3) = 1, (a2, a4)= 1, (a3, a4) = a1,
(a4, a5) = a3, (a3, a5) = a2, (a2, a5) = a1, a1 = b1, 
(b1, b2) = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..5]]: i in [1..2]]);

L := [];

// G10, 8

G := quo <F | Comms, a2^p = a3^p = a5^p =  b1^p = b2^p = 1,
a4^p = b2>;
Append (~L, G);

// G10, 10r
w := PrimitiveRoot (p);

if p mod 4 eq 1 then add := [w^i: i in [0..3]];
else add := [w^i: i in [0..1]]; end if;
for r in add do
G := quo <F | Comms, a2^p = a3^p =  b1^p = b2^p = 1,
              a4^p =b2, a5^p = b1^r>;
Append (~L, G);
end for;

return L;
end function;

Table3Phi10 := function(p)
    return My10A(p) cat My10B(p);
end function;

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

// Checking of column "H"

Check10ACol3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 0;
H := [];
MinDeg1 := [];

// G10, 3r

if p mod 3 eq 1 then
for r in [1..3] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6];
Append (~H, sub< F | Alpha[2], Alpha[3]>);
Append (~MinDeg1, p^4);
end for;
else 
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6];
Append (~H, sub< F | Alpha[2], Alpha[3]>);
Append (~MinDeg1, p^4);
end if;

return H, MinDeg1;
end function;

// H, MinDeg1 := Check10ACol3(L);

Check10BCol3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

a := GCD(p-1, 3);

count := a;
H1 := [];
H2 := [];
MinDeg2 := [];

// following setup is done just to ensure that
// |L[i]: H1[i]| + |L[i]: H2[i]| = MinDeg[i].

for r in [1..a] do
F := L[a+1]; // no particular reason of choosing 5 here
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H1, sub<F | Beta[2]^p>); // trivial subgroup
Append (~H2, sub<F | Beta[2]^p>); // trivial subgroup
end for;

// G10, 8

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H1, sub<F | Alpha[2], Alpha[3], Alpha[5]>);
Append (~H2, sub<F | Alpha[2], Alpha[4]>);
Append (~MinDeg2, p^3 + p^2);

// G10, 10r

if p mod 4 eq 1 then
for r in [1..4] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H1, sub<F | Alpha[2], Alpha[3], Alpha[5]>);
Append (~H2, sub<F | Alpha[2], Alpha[4]>);
Append (~MinDeg2, p^3 + p^2);
end for;
else 
for r in [1..2] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H1, sub<F | Alpha[2], Alpha[3], Alpha[5]>);
Append (~H2, sub<F | Alpha[2], Alpha[4]>);
Append (~MinDeg2, p^3 + p^2);
end for;
end if;

return H1, H2, MinDeg2;
end function;

MAX := 7^6;

for p in PrimesInInterval (5, 11) do 
   "\n process prime ", p;
   L := Table3Phi10(p);
   H, MinDeg1 := Check10ACol3(L, p);
   H1, H2, MinDeg2 := Check10BCol3(L, p);
   MinDeg := MinDeg1 cat MinDeg2;

   a := GCD(p-1, 3);
   for i in [1..a] do
      G := L[i];
      Q, phi := pQuotient(G, p, 10);
      A := phi (H[i]);
      m := Index(Q, A);
      C := Core(Q, A);
      assert #C eq 1;
      phiA := CosetAction (Q, A);
      J := Image (phiA);
      assert #J eq #Q;
      if #J le MAX then assert IsIsomorphic (J, Q); end if;
      assert Degree (J) eq m;
      assert Degree (J) eq MinDeg[i];
   end for;

   for i in [a+1..#L] do
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

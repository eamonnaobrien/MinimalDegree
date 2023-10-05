load "../setup-permrep.m";

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

// Subgroup H is listed in the list H.
// d(Z(H[i])) is cyclic for each i.
// List S stores a subgroup of L.

//Phi7, G with center Cp x Cp

Table2Phi7 := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, b1, b2> := FreeGroup (7);
Alpha := [a1, a2, a3, a4, a5];
Beta := [b1, b2];

// common relations, typically commutators
Comms := [
(a2, a3) = 1, (a2, a4)= 1, (a3, a4) = a1,
(a4, a5) = a2, (a3, a5) = 1, (a2, a5) = a1, a1 = b1, 
(b1, b2) = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..5]]: i in [1..2]]);

L := [];

// G7, 5

G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p = b1^p = b2^p = 1>;
Append (~L, G);

// G7, 6

G := quo <F | Comms, a2^p = a3^p = a4^p =  b1^p = b2^p = 1,
a5^p = b1>;
Append (~L, G);

// G7, 8r

for r in [1,nu] do
G := quo <F | Comms, a2^p = a3^p = a5^p = b1^p = b2^p = 1,
a4^p = b1^r>;
Append (~L, G);
end for;

// G7, 10

G := quo <F | Comms, a2^p = a4^p = a5^p = b1^p = b2^p = 1,
a3^p = b1>;
Append (~L, G);

return L;
end function;

//Phi8, G with center Cp x Cp

Table2Phi8 := function(p)

F<a1, a2, a3, a4, a5, b1, b2> := FreeGroup (7);
Alpha := [a1, a2, a3, a4, a5];
Beta := [b1, b2];

// common relations, typically commutators
Comms := [
(a2, a3) = 1, (a2, a4)= 1, (a3, a4) = a1,
(a4, a5) = a2, (a3, a5) = 1, (a2, a5) = a1, a1 = b1, 
(b1, b2) = 1, a3^-1 = a5^p] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..5]]: i in [1..2]]);

L := [];

// G8, 5

G := quo <F | Comms,  a5^(p^2) =  b1^p = b2^p = 1,
a4^p = a2>;
Append (~L, G);

return L;
end function;

//Phi9, G with center Cp x Cp

Table2Phi9 := function(p)

F<a1, a2, a3, a4, a5, b1, b2> := FreeGroup (7);
Alpha := [a1, a2, a3, a4, a5];
Beta := [b1, b2];

// common relations, typically commutators
Comms := [
(a2, a3) = 1, (a2, a4)= 1, (a3, a4) = 1,
(a4, a5) = a3, (a3, a5) = a2, (a2, a5) = a1, a1 = b1, 
(b1, b2) = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..5]]: i in [1..2]]);

L := [];

// G94

G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p = b1^p = b2^p = 1>;
Append (~L, G);

// G95

G := quo <F | Comms, a5^p = b1, a2^p = a3^p = a4^p = b1^p = b2^p = 1>;
Append (~L, G);

// G9, 7r
w := PrimitiveRoot (p);

if p mod 3 eq 1 then add := [w^i: i in [0..2]]; else add := [1];
end if;
for r in add do
G := quo <F | Comms, a2^p = a3^p = a5^p = b1^p = b2^p = 1,
               a4^p = b1^r>;
Append (~L, G);
end for;

return L;
end function;

//Phi10, G with center Cp x Cp

Table2Phi10 := function(p)

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

// G10, 4

G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p = b1^p = b2^p = 1>;
Append (~L, G);

// G10, 5r
w := PrimitiveRoot (p);

if p mod 4 eq 1 then add := [w^i: i in [0..3]];
else add := [w^i: i in [0..1]]; end if;
for r in add do
G := quo <F | Comms, a2^p = a3^p = a4^p = b1^p = b2^p = 1,
               a5^p = b1^r>;
Append (~L, G);
end for;

// G10, 7r
w := PrimitiveRoot (p);

if p mod 3 eq 1 then add := [w^i: i in [0..2]];
else add := [1]; end if;
for r in add do
G := quo <F | Comms, a2^p = a3^p = a5^p = b1^p = b2^p = 1,
               a4^p = b1^r>;
Append (~L, G);
end for;

return L;
end function;

Table2Phi7to9Col2 := function(p)
   return Table2Phi7(p) cat Table2Phi8(p) cat Table2Phi9(p) cat Table2Phi10(p);
end function;

// Checking of column "H"

CheckPhi7Col3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 0;
H1 := [];
S1 := [];
MinDeg1 := [];

// G7, 5

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H1, sub< F | Alpha[1], Alpha[2], Alpha[3],
Alpha[4], Alpha[5], Beta[1]>);
Append (~S1, sub< F | Alpha[2], Alpha[4]>);
Append (~MinDeg1, p^3);

// G7, 6

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H1, sub< F | Alpha[1], Alpha[2], Alpha[3],
Alpha[4], Alpha[5], Beta[1]>);
Append (~S1, sub< F | Alpha[2], Alpha[4]>);
Append (~MinDeg1, p^3);

// G7, 8r

for r in [1, nu] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H1, sub< F | Alpha[1], Alpha[2], Alpha[3],
Alpha[4], Alpha[5], Beta[1]>);
Append (~S1, sub< F | Alpha[3], Alpha[5]>);
Append (~MinDeg1, p^3);
end for;

// G7, 10

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H1, sub< F | Alpha[1], Alpha[2], Alpha[3],
Alpha[4], Alpha[5], Beta[1]>);
Append (~S1, sub< F | Alpha[2], Alpha[4]>);
Append (~MinDeg1, p^3);

return H1, S1, MinDeg1;
end function;

CheckPhi8Col3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 5;
H2 := [];
S2 := [];
MinDeg2 := [];

// G8, 5

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H2, sub< F | Alpha[1], Alpha[2], Alpha[3],
Alpha[4], Alpha[5], Beta[1]>);
Append (~S2, sub< F | Alpha[5]>);
Append (~MinDeg2, p^3);

return H2, S2, MinDeg2;
end function;

CheckPhi9Col3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 6;
H3 := [];
S3 := [];
MinDeg3 := [];

// G9, 4

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H3, sub< F | Alpha[1], Alpha[2], Alpha[3],
Alpha[4], Alpha[5], Beta[1]>);
Append (~S3, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg3, p^2);

// G9, 5

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H3, sub< F | Alpha[1], Alpha[2], Alpha[3],
Alpha[4], Alpha[5], Beta[1]>);
Append (~S3, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg3, p^2);

// G9, 7r

if p mod 3 eq 1 then
for r in [1..3] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H3, sub< F | Alpha[1], Alpha[2], Alpha[3],
Alpha[4], Alpha[5], Beta[1]>);
Append (~S3, sub< F | Alpha[2], Alpha[3]>);
Append (~MinDeg3, p^3);
end for;
else
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H3, sub< F | Alpha[1], Alpha[2], Alpha[3],
Alpha[4], Alpha[5], Beta[1]>);
Append (~S3, sub< F | Alpha[2], Alpha[3]>);
Append (~MinDeg3, p^3);
end if;

return H3, S3, MinDeg3;
end function;

CheckPhi10Col3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 8 + GCD(p-1, 3);
H4 := [];
S4 := [];
MinDeg4 := [];

// G10, 4

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H4, sub< F | Alpha[1], Alpha[2], Alpha[3],
Alpha[4], Alpha[5], Beta[1]>);
Append (~S4, sub< F | Alpha[2], Alpha[3]>);
Append (~MinDeg4, p^3);

// G10, 5r

if p mod 4 eq 1 then
for r in [1..4] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H4, sub< F | Alpha[1], Alpha[2], Alpha[3],
Alpha[4], Alpha[5], Beta[1]>);
Append (~S4, sub< F | Alpha[2], Alpha[3]>);
Append (~MinDeg4, p^3);
end for;
else
for r in [1..2] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H4, sub< F | Alpha[1], Alpha[2], Alpha[3],
Alpha[4], Alpha[5], Beta[1]>);
Append (~S4, sub< F | Alpha[2], Alpha[3]>);
Append (~MinDeg4, p^3);
end for;
end if;

// G10, 7r

if p mod 3 eq 1 then
   for r in [1..3] do
      count := count+1;
      F := L[count];
      Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
      Append (~H4, sub< F | Alpha[1], Alpha[2], Alpha[3],
                           Alpha[4], Alpha[5], Beta[1]>);
      Append (~S4, sub< F | Alpha[2], Alpha[3]>);
      Append (~MinDeg4, p^3);
   end for;
else
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
   Append (~H4, sub< F | Alpha[1], Alpha[2], Alpha[3],
                        Alpha[4], Alpha[5], Beta[1]>);
   Append (~S4, sub< F | Alpha[2], Alpha[3]>);
   Append (~MinDeg4, p^3);
end if;

return H4, S4, MinDeg4;
end function;

MAX := 7^6;

for p in PrimesInInterval (5, 11) do 
   "\n process prime ", p;
   L := Table2Phi7to9Col2(p);

   H1, S1, MinDeg1 := CheckPhi7Col3(L, p);
   H2, S2, MinDeg2 := CheckPhi8Col3(L, p);
   H3, S3, MinDeg3 := CheckPhi9Col3(L, p);
   H4, S4, MinDeg4 := CheckPhi10Col3(L, p);

   H := H1 cat H2 cat H3 cat H4;
   S := S1 cat S2 cat S3 cat S4;
   MinDeg := MinDeg1 cat MinDeg2 cat MinDeg3 cat MinDeg4;

   for i in [1..#L] do
     G := L[i];
     Q, phi := pQuotient(G, p, 10);

     // setup perm rep for H
     R := phi (H[i]);
     A := phi (S[i]);
     m := Index(R, A);
     C := Core(R, A);
     assert #C eq 1;
     phiA := CosetAction (R, A);
     J := Image (phiA);
     assert #J eq #R;
     assert Degree (J) eq MinDeg[i];

     // setup perm rep for G
     I, IS := DetermineMinRep (G, Q, R, [A], phi);
     assert #&meet[Core (Q, s): s in IS] eq 1;
     assert #I eq #Q;
     if #Q le MAX then assert IsIsomorphic (I, Q); end if;
     assert Degree (I) eq MinDeg[i] + p;
  end for;
end for;

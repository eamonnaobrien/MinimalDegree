load "../setup-permrep.m";

// Groups G are listed in the list L.
// Z(L[i]) is cyclic for i = 1 to #L.

//Phi31 with center Cp

My31 := function(p)

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a2, a3, a4, a5, a6];
Beta := [a1];

// common relations, typically commutators
Comms := [ (a2, a3) = 1, (a2, a4) = a1, (a2, a5) = 1,
(a2, a6) = 1, (a3, a4) = 1, (a3, a5)= a1^(-1),
 (a3, a6) = 1, (a4, a5) = 1, (a4, a6)= a2, 
(a5, a6)= a3, a1^p = 1] cat
[(a1, Alpha[j]) = Id(F) : j in [1..5]];

L := [];

// G31, 1

G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p = a6^p = 1>;
Append (~L, G);

// G31, 3

G := quo <F | Comms, a2^p = a3^p = a5^p = a6^p = 1,
a4^p = a1>;
Append (~L, G);

// G31, 4

G := quo <F | Comms, a2^p = a3^p = a6^p = 1,
a4^p = a1, a5^p = a1>;
Append (~L, G);

return L;
end function;

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

//Phi32 with center Cp

My32 := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a2, a3, a4, a5, a6];
Beta := [a1];

// common relations, typically commutators
Comms := [ (a2, a3) = 1, (a2, a4) = a1, (a2, a5) = 1,
(a2, a6) = 1, (a3, a4) = 1, (a3, a5)= a1^(-nu),
 (a3, a6) = 1, (a4, a5) = 1, (a4, a6)= a2, 
(a5, a6)= a3, a1^p = 1] cat
[(a1, Alpha[j]) = Id(F) : j in [1..5]];

L := [];

// G32, 1

G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p = a6^p = 1>;
Append (~L, G);

// G32, 3

G := quo <F | Comms, a2^p = a3^p = a5^p = a6^p = 1, 
a4^p = a1>;
Append (~L, G);

return L;
end function;

//Phi33 with center Cp

My33 := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a2, a3, a4, a5, a6];
Beta := [a1];

// common relations, typically commutators
Comms := [ (a2, a3) = 1, (a2, a4) = a1, (a2, a5) = 1,
(a2, a6) = 1, (a3, a4) = 1, (a3, a5)= 1,
 (a3, a6) = a1, (a4, a5) = 1, (a4, a6)= a2, 
(a5, a6)= a3, a1^p = 1] cat
[(a1, Alpha[j]) = Id(F) : j in [1..5]];

L := [];

// G33, 1

G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p = a6^p = 1>;
Append (~L, G);

// G33, 2r

for r in [1,nu] do
G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p = 1, 
a6^p = a1^r>;
Append (~L, G);
end for;

// G33, 3

G := quo <F | Comms, a2^p = a3^p = a5^p = a6^p = 1,
a4^p = a1>;
Append (~L, G);

return L;
end function;

//Phi34 with center Cp

My34 := function(p)

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a2, a3, a4, a5, a6];
Beta := [a1];

// common relations, typically commutators
Comms := [ (a2, a3) = 1, (a2, a4) = 1, (a2, a5) = 1,
(a2, a6) = a1, (a3, a4) = 1, (a3, a5)= a1^(-1),
 (a3, a6) = 1, (a4, a5) = 1, (a4, a6)= a2, 
(a5, a6)= a3, a1^p = 1, a3^p = a1, a5^p = a2,
a6^p = a3] cat
[(a1, Alpha[j]) = Id(F) : j in [1..5]];

L := [];

// G34, 1

G := quo <F | Comms, a2^p = a4^p =  1>;
Append (~L, G);

return L;
end function;

//Phi35 with center Cp

My35 := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a2, a3, a4, a5, a6];
Beta := [a1];

// common relations, typically commutators
Comms := [ (a2, a3) = 1, (a2, a4) = 1, (a2, a5) = 1,
(a2, a6) = a1, (a3, a4) = 1, (a3, a5)= 1,
 (a3, a6) = a2, (a4, a5) = 1, (a4, a6)= a3, 
(a5, a6)= a4, a1^p = 1] cat
[(a1, Alpha[j]) = Id(F) : j in [1..5]];

L := [];

// G35, 1

G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p = a6^p = 1>;
Append (~L, G);

// G35, 2r
w := PrimitiveRoot (p);

if p mod 4 eq 1 then add := [w^i: i in [0..3]];
else add := [1,nu]; end if;
for r in add do
G := quo <F | Comms, a2^p = a3^p = a4^p = a6^p = 1,
a5^p = a1^r>;
Append (~L, G);
end for;

// G35, 3

if p eq 5 then 
   G := quo <F | Comms, a2^p = a3^p = a4^p = 1, 
   a5^p = a1^-1, 
   a6^p = a1>;
   Append (~L, G);
else
   G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p = 1,
   a6^p = a1>;
   Append (~L, G);
end if;

return L;
end function;

//Phi36 with center Cp

My36 := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a2, a3, a4, a5, a6];
Beta := [a1];

// common relations, typically commutators
Comms := [ (a2, a3) = 1, (a2, a4) = 1, (a2, a5) = 1,
(a2, a6) = a1, (a3, a4) = 1, (a3, a5)= 1,
 (a3, a6) = a2, (a4, a5) = a1, (a4, a6)= a3, 
(a5, a6)= a4, a1^p = 1] cat
[(a1, Alpha[j]) = Id(F) : j in [1..5]];

L := [];

// G36, 1

G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p = a6^p = 1>;
Append (~L, G);

// G36, 2r
w := PrimitiveRoot (p);

if p mod 4 eq 1 then add := [w^i: i in [0..3]];
else add := [1,nu]; end if;
for r in add do
G := quo <F | Comms, a2^p = a3^p = a4^p = a6^p = 1,
a5^p = a1^r>;
Append (~L, G);
end for;

// G36, 3r
w := PrimitiveRoot (p);

if p eq 5 then 
for r in [1,2] do 
  G := quo <F | Comms, a2^p = a3^p = a4^p = 1,
  a5^p = a1^-1,
  a6^p = a1^r>;
  Append (~L, G);
end for;
else 
if p mod 3 eq 1 then add := [w^i: i in [0..5]];
else add := [1,nu]; end if;
for r in add do
G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p = 1,
a6^p = a1^r>;
Append (~L, G);
end for;
end if;

return L;
end function;

Table3Cyclic_p31To36 := function(p)
   return My31(p) cat My32(p) cat My33(p) cat My34(p) cat My35(p) cat My36(p);
end function;

// Checking of column "H"

Check31Col3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 0;
H1 := [];
MinDeg1 := [];

// G31, 1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H1, sub< F | Alpha[2], Alpha[3], Alpha[6]>);
Append (~MinDeg1, p^3);

// G31, 3

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H1, sub< F | Alpha[2], Alpha[3], Alpha[6]>);
Append (~MinDeg1, p^3);

// G31, 4

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H1, sub< F | Alpha[2], Alpha[3], Alpha[6]>);
Append (~MinDeg1, p^3);

return H1, MinDeg1;
end function;

// H1, MinDeg1 := Check31Col3(L);


Check32Col3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 3;
H2 := [];
MinDeg2 := [];

// G32, 1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H2, sub< F | Alpha[2], Alpha[3], Alpha[6]>);
Append (~MinDeg2, p^3);

// G32, 3

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H2, sub< F | Alpha[2], Alpha[3], Alpha[6]>);
Append (~MinDeg2, p^3);

return H2, MinDeg2;
end function;

Check33Col3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 5;
H3 := [];
MinDeg3 := [];

// G33, 1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H3, sub< F | Alpha[2], Alpha[3], Alpha[5]>);
Append (~MinDeg3, p^3);

// G33, 2r

for r in [1, nu] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H3, sub< F | Alpha[2], Alpha[3], Alpha[5]>);
Append (~MinDeg3, p^3);
end for;

// G33, 3

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H3, sub< F | Alpha[2], Alpha[3], Alpha[5]>);
Append (~MinDeg3, p^3);

return H3, MinDeg3;
end function;

Check34Col3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 9;
H4 := [];
MinDeg4 := [];

// G34, 1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H4, sub< F | Alpha[4], Alpha[5]>);
Append (~MinDeg4, p^3);

return H4, MinDeg4;
end function;

Check35Col3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 10;
H5 := [];
MinDeg5 := [];

// G35, 1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H5, sub< F | Alpha[2], Alpha[3],
Alpha[4], Alpha[5]>);
Append (~MinDeg5, p^2);

// G35, 2r

if p mod 4 eq 1 then
for r in [1..4] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H5, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg5, p^3);
end for;
else 
for r in [1..2] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H5, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg5, p^3);
end for;
end if;

// G35, 3

if p eq 5 then 
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H5, sub< F | Alpha[2], Alpha[3],
Alpha[4]>);
Append (~MinDeg5, p^3);
else
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H5, sub< F | Alpha[2], Alpha[3],
Alpha[4], Alpha[5]>);
Append (~MinDeg5, p^2);
end if;

return H5, MinDeg5;
end function;

Check36Col3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 12 + GCD(p-1,4);
H6 := [];
MinDeg6 := [];

// G36, 1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H6, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg6, p^3);

// G36, 2r

if p mod 4 eq 1 then
for r in [1..4] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H6, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg6, p^3);
end for;
else 
for r in [1..2] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H6, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg6, p^3);
end for;
end if;

// G36, 3r

if p eq 5 then 
for r in [1,2] do 
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H6, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg6, p^3);
end for;
else
if p mod 3 eq 1 then
for r in [1..6] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H6, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg6, p^3);
end for;
else 
for r in [1..2] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H6, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg6, p^3);
end for;
end if;
end if;

return H6, MinDeg6;
end function;

for p in PrimesInInterval (5, 11) do 
   "\n process prime ", p;
   L := Table3Cyclic_p31To36(p);
   H1, MinDeg1 := Check31Col3(L, p);
   H2, MinDeg2 := Check32Col3(L, p);
   H3, MinDeg3 := Check33Col3(L, p);
   H4, MinDeg4 := Check34Col3(L, p);
   H5, MinDeg5 := Check35Col3(L, p);
   H6, MinDeg6 := Check36Col3(L, p);
   H := H1 cat H2 cat H3 cat H4 cat H5 cat H6;
   MinDeg := MinDeg1 cat MinDeg2 cat MinDeg3
         cat MinDeg4 cat MinDeg5 cat MinDeg6;

   for i in [1..#L] do
      G := L[i];
      Q, phi := pQuotient(G, p, 10);
      A := phi (H[i]);
      m := Index(Q, A);
      assert m eq MinDeg[i];
      C := Core(Q, A);
      assert #C eq 1;
      phiA := CosetAction (Q, A);
      J := Image (phiA);
      // assert IsIsomorphic (J, PF);
      assert #J eq #Q;
      assert Degree (J) eq MinDeg[i];
   end for;
end for;

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

// Groups G are listed in the list L.
// Z(L[i]) is cyclic for i = 1 to #L.

//Phi22 with center Cp

My22 := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a2, a3, a4, a5, a6];
Beta := [a1];

// common relations, typically commutators
Comms := [ (a2, a3) = 1, (a2, a4) = 1, (a2, a5) = 1,
(a2, a6) = a1, (a3, a4) = a1, (a3, a5)= 1,
 (a3, a6) = 1, (a4, a5) = 1, (a4, a6)= 1, 
(a5, a6)= a2, a1^p = 1] cat
[(a1, Alpha[j]) = Id(F) : j in [1..5]];

L := [];

// G22, 1

G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p = a6^p = 1>;
Append (~L, G);

// G22, 2

G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p = 1,
a6^p = a1>;
Append (~L, G);

// G22, 3r

for r in [1,nu] do
G := quo <F | Comms, a2^p = a3^p = a4^p = a6^p = 1,
a5^p = a1^r>;
Append (~L, G);
end for;

// G22, 4

G := quo <F | Comms, a2^p = a3^p = a5^p = a6^p = 1,
a4^p = a1>;
Append (~L, G);

// G22, 5r

for r in [1,nu] do
G := quo <F | Comms, a2^p = a3^p = a6^p = 1,
a4^p = a1^r, a5^p = a1^r>;
Append (~L, G);
end for;

return L;
end function;

My24 := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a2, a3, a4, a5, a6];
Beta := [a1];

// common relations, typically commutators
Comms := [ (a2, a3) = 1, (a2, a4) = 1, (a2, a5) = 1,
(a2, a6) = a1, (a3, a4) = 1, (a3, a5)= 1,
 (a3, a6) = a2, (a4, a5) = a1, (a4, a6)= 1, 
(a5, a6)= a3, a1^p = 1] cat
[(a1, Alpha[j]) = Id(F) : j in [1..5]];

L := [];

// G24, 1

G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p = a6^p = 1>;
Append (~L, G);

// G24, 2

G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p = 1,
a6^p = a1>;
Append (~L, G);

// G24, 3r
w := PrimitiveRoot (p);

if p mod 3 eq 1 then add := [w^i: i in [0..2]];
else add := [1]; end if;
for r in add do
G := quo <F | Comms, a2^p = a3^p = a4^p = a6^p = 1,
a5^p = a1^r>;
Append (~L, G);
end for;

// G24, 4

G := quo <F | Comms, a2^p = a3^p = a5^p = a6^p = 1,
a4^p = a1>;
Append (~L, G);

return L;
end function;

//Phi27 with center Cp

My27 := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a2, a3, a4, a5, a6];
Beta := [a1];

// common relations, typically commutators
Comms := [ (a2, a3) = 1, (a2, a4) = 1, (a2, a5) = 1,
(a2, a6) = a1, (a3, a4) = 1, (a3, a5)= a1,
 (a3, a6) = a2, (a4, a5) = a1, (a4, a6)= 1, 
(a5, a6)= a3, a1^p = 1] cat
[(a1, Alpha[j]) = Id(F) : j in [1..5]];

L := [];

// G27, 1

G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p = a6^p = 1>;
Append (~L, G);

// G27, 2r
w := PrimitiveRoot (p);

if p mod 4 eq 1 then add := [w^i: i in [0..3]];
else add := [1,nu]; end if;
for r in add do
G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p =  1,
a6^p = a1^r>;
Append (~L, G);
end for;

// G27, 3r
w := PrimitiveRoot (p);

if p mod 3 eq 1 then add := [w^i: i in [0..2]];
else add := [1]; end if;
for r in add do
G := quo <F | Comms, a2^p = a3^p = a4^p = a6^p =  1,
a5^p = a1^r>;
Append (~L, G);
end for;

return L;
end function;

My28 := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a2, a3, a4, a5, a6];
Beta := [a1];

// common relations, typically commutators
Comms := [ (a2, a3) = 1, (a2, a4) = 1, (a2, a5) = 1,
(a2, a6) = a1, (a3, a4) = a1, (a3, a5)= 1,
 (a3, a6) = a2, (a4, a5) = a1, (a4, a6)= a3, 
(a5, a6)= 1, a1^p = 1, a2^p = 1, a3^p = a1,
a6^p = a5, a4^p = a2] cat
[(a1, Alpha[j]) = Id(F) : j in [1..5]];

L := [];


// G28, 2r

for r in [p-1] do
G := quo <F | Comms,   a6^(p^2) = a1^r>;
Append (~L, G);
end for;

return L;
end function;

//Phi29 with center Cp

My29 := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a2, a3, a4, a5, a6];
Beta := [a1];

// common relations, typically commutators
Comms := [ (a2, a3) = 1, (a2, a4) = 1, (a2, a5) = 1,
(a2, a6) = a1, (a3, a4) = a1, (a3, a5)= 1,
 (a3, a6) = a2^nu, (a4, a5) = a1, (a4, a6)= a3, 
(a5, a6)= 1, a1^p = 1, a2^p = 1, a3^p = a1,
a6^p = a5, a4^p = a2] cat
[(a1, Alpha[j]) = Id(F) : j in [1..5]];

L := [];

// G29, 2r

for r in [p-1] do
G := quo <F | Comms,   a6^(p^2) = a1^r>;
Append (~L, G);
end for;

return L;
end function;

//Phi30 with center Cp

My30 := function(p)

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a2, a3, a4, a5, a6];
Beta := [a1];

// common relations, typically commutators
Comms := [ (a2, a3) = 1, (a2, a4) = 1, (a2, a5) = 1,
(a2, a6) = a1, (a3, a4) = a1^(-1), (a3, a5)= 1,
 (a3, a6) = a2, (a4, a5) = a2, (a4, a6)= 1, 
(a5, a6)= a3, a1^p = 1] cat
[(a1, Alpha[j]) = Id(F) : j in [1..5]];

L := [];

// G30, 1

G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p = a6^p = 1>;
Append (~L, G);

// G30, 2

G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p =  1,
a6^p = a1>;
Append (~L, G);

// G30, 4

G := quo <F | Comms, a2^p = a3^p = a5^p = a6^p =  1,
a4^p = a1>;
Append (~L, G);

// G30, 6

G := quo <F | Comms, a2^p = a3^p = a5^p =  1,
a4^p = a1^2, a6^p = a1>;
Append (~L, G);

return L;
end function;

Table3Cyclic_p22To30 := function(p)
   return My22(p) cat My24(p) cat My27(p) cat My28(p) cat My29(p) cat My30(p);
end function;

// Checking of column "H"

Check22Col3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 0;
H1 := [];
MinDeg1 := [];

// G22, 1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H1, sub< F | Alpha[2], Alpha[3], Alpha[5]>);
Append (~MinDeg1, p^3);

// G22, 2

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H1, sub< F | Alpha[2], Alpha[4], Alpha[5]>);
Append (~MinDeg1, p^3);

// G22, 3r

for r in [1,nu] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H1, sub< F | Alpha[2], Alpha[4]>);
Append (~MinDeg1, p^4);
end for;

// G22, 4

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H1, sub< F | Alpha[2], Alpha[3], Alpha[5]>);
Append (~MinDeg1, p^3);

// G22, 5r

for r in [1,nu] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H1, sub< F | Alpha[2], Alpha[3]>);
Append (~MinDeg1, p^4);
end for;

return H1, MinDeg1;
end function;


Check24Col3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 7;
H2 := [];
MinDeg2 := [];

// G24, 1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H2, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg2, p^3);

// G24, 2

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H2, sub< F | Alpha[2], Alpha[3], Alpha[5]>);
Append (~MinDeg2, p^3);

// G24, 3r

if p mod 3 eq 1 then
for r in [1..3] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H2, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg2, p^3);
end for;
else
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H2, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg2, p^3);
end if;

// G24, 4

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H2, sub< F | Alpha[2], Alpha[3], Alpha[5]>);
Append (~MinDeg2, p^3);

return H2, MinDeg2;
end function;

// H2, MinDeg2 := Check24Col3(L);

Check27Col3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 10 + GCD(p-1, 3);
H3 := [];
MinDeg3 := [];

// G27, 1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H3, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg3, p^3);

// G27, 2r

if p mod 4 eq 1 then
for r in [1..4] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H3, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg3, p^3);
end for;
else 
for r in [1,nu] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H3, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg3, p^3);
end for;
end if;

// G27, 3r

if p mod 3 eq 1 then
for r in [1..3] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H3, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg3, p^3);
end for;
else 
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H3, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg3, p^3);
end if;

return H3, MinDeg3;
end function;

// H3, MinDeg3 := Check27Col3(L);

Check28Col3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 11 + 2*GCD(p-1, 3) + GCD(p-1,4);
H4 := [];
MinDeg4 := [];

// G28, 2r (r=p-1)

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H4, sub< F | Alpha[4], Alpha[3]*Alpha[2]*Alpha[6]^(p)>);
Append (~MinDeg4, p^3);

return H4, MinDeg4;
end function;

// H4, MinDeg4 := Check28Col3(L);

Check29Col3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 12 + 2*GCD(p-1, 3) + GCD(p-1,4);
H5 := [];
MinDeg5 := [];

// G29, 2r (r=p-1)

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H5, sub< F | Alpha[4], Alpha[3]*Alpha[2]*Alpha[6]^(p)>);
Append (~MinDeg5, p^3);

return H5, MinDeg5;
end function;

// H5, MinDeg5 := Check29Col3(L);

Check30Col3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 13 + 2*GCD(p-1, 3) + GCD(p-1,4);
H6 := [];
MinDeg6 := [];

// G30, 1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H6, sub< F | Alpha[2], Alpha[3], Alpha[5]>);
Append (~MinDeg6, p^3);

// G30, 2

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H6, sub< F | Alpha[2], Alpha[3], Alpha[5]>);
Append (~MinDeg6, p^3);

// G30, 4

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H6, sub< F | Alpha[2], Alpha[3], Alpha[5]>);
Append (~MinDeg6, p^3);

// G30, 6

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H6, sub< F | Alpha[2], Alpha[3], Alpha[5]>);
Append (~MinDeg6, p^3);

return H6, MinDeg6;
end function;

for p in PrimesInInterval (5, 11) do 
   "\n process prime ", p;
   L := Table3Cyclic_p22To30(p);
   H1, MinDeg1 := Check22Col3(L, p);
   H2, MinDeg2 := Check24Col3(L, p);
   H3, MinDeg3 := Check27Col3(L, p);
   H4, MinDeg4 := Check28Col3(L, p);
   H5, MinDeg5 := Check29Col3(L, p);
   H6, MinDeg6 := Check30Col3(L, p);
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
      assert Degree (J) eq m;
   end for;
end for;


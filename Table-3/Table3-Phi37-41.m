// Groups G are listed in the list L.
// Z(L[i]) is cyclic for i = 1 to #L.

//Phi37 with center Cp

My37 := function(p)

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a2, a3, a4, a5, a6];
Beta := [a1];

// common relations, typically commutators
Comms := [ (a2, a3) = 1, (a2, a4) = 1, (a2, a5) = a1,
(a2, a6) = 1, (a3, a4) = a1^(-1), (a3, a5)= a1,
 (a3, a6) = a2, (a4, a5) = a1, (a4, a6)= a3, 
(a5, a6)= a4, a1^p = 1] cat
[(a1, Alpha[j]) = Id(F) : j in [1..5]];

L := [];

// G37, 1

G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p = a6^p = 1>;
Append (~L, G);

// G37, 2

G := quo <F | Comms, a2^p = a3^p = a4^p = a6^p = 1,
a5^p = a1>;
Append (~L, G);

return L;
end function;

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

//Phi38 with center Cp

My38 := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a2, a3, a4, a5, a6];
Beta := [a1];

// common relations, typically commutators
Comms := [ (a2, a3) = 1, (a2, a4) = 1, (a2, a5) = 1,
(a2, a6) = a1, (a3, a4) = 1, (a3, a5)= a1,
 (a3, a6) = a2, (a4, a5) = a2, (a4, a6)= a3, 
(a5, a6)= a4, a1^p = 1] cat
[(a1, Alpha[j]) = Id(F) : j in [1..5]];

L := [];

if p eq 5 then 

// G38, 1r for p = 5
for r in [0..p-1] do 
G := quo <F | Comms, a2^p = a3^p = a4^p = 1, 
a5^p = a1^(-r), 
a6^p = a1^-((2 * (r-1)) mod p) >;
Append (~L, G);
end for;

// G38, 2r for p = 5 
for r in [0,2,3,4] do 
G := quo <F | Comms, a2^p = a3^p = a4^p = 1, 
a5^p = a1^-r, a6^p = 1 >;
Append (~L, G);
end for;

// G38, 3 for p = 5 
G := quo <F | Comms, a2^p = a3^p = a4^p = 1, 
a5^p = a1^-1, a6^p = a1 >;
Append (~L, G);

return L;

end if;

// G38, 1

G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p = a6^p = 1>;
Append (~L, G);

// G38, 2r 
w := PrimitiveRoot (p);

if p mod 5 eq 1 then add := [w^i: i in [0..4]];
else add := [1]; end if;
for r in add do
G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p = 1,
a6^p = a1^r>;
Append (~L, G);
end for;

// G38, 3r

for r in [1..(p-1)] do
G := quo <F | Comms, a2^p = a3^p = a4^p = a6^p = 1,
a5^p = a1^r>;
Append (~L, G);
end for;

// G38, 4r
w := PrimitiveRoot (p);

if p mod 4 eq 1 then add := [w^i: i in [0..3]];
else add := [1,nu]; end if;
for r in add do
G := quo <F | Comms, a2^p = a3^p = a4^p = 1,
a5^p = a1^r, a6^p = a1^(-r)>;
Append (~L, G);
end for;

return L;
end function;

//Phi39 with center Cp

My39 := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a2, a3, a4, a5, a6];
Beta := [a1];

// common relations, typically commutators
Comms := [ (a2, a3) = 1, (a2, a4) = 1, (a2, a5) = a1,
(a2, a6) = 1, (a3, a4) = a1^(-1), (a3, a5)= a1,
 (a3, a6) = a2, (a4, a5) = a2, (a4, a6)= a3, 
(a5, a6)= a4, a1^p = 1] cat
[(a1, Alpha[j]) = Id(F) : j in [1..5]];

L := [];

// G39, 1

G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p = a6^p = 1>;
Append (~L, G);

// G39, 2r
w := PrimitiveRoot (p);

if p mod 5 eq 1 then add := [w^i: i in [0..4]];
else add := [1]; end if;
for r in add do
G := quo <F | Comms, a2^p = a3^p = a4^p = a6^p = 1,
a5^p = a1^r>;
Append (~L, G);
end for;

return L;
end function;

//Phi40 with center Cp

My40 := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a2, a3, a4, a5, a6];
Beta := [a1];

// common relations, typically commutators
Comms := [ (a2, a3) = 1, (a2, a4) = 1, (a2, a5) = 1,
(a2, a6) = a1, (a3, a4) = 1, (a3, a5)= a1,
 (a3, a6) = 1, (a4, a5) = a2, (a4, a6)= a3, 
(a5, a6)= a4, a1^p = 1] cat
[(a1, Alpha[j]) = Id(F) : j in [1..5]];

L := [];

// G40, 1

G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p = a6^p = 1>;
Append (~L, G);

// G40, 2

G := quo <F | Comms, a2^p = a3^p = a4^p = a6^p = 1,
a5^p = a1>;
Append (~L, G);

// G40, 3r
w := PrimitiveRoot (p);

if p mod 3 eq 1 then add := [w^i: i in [0..2]];
else add := [1]; end if;
for r in add do
G := quo <F | Comms, a2^p = a3^p = a4^p = 1,
a5^p = a1, a6^p = a1^r>;
Append (~L, G);
end for;

return L;
end function;

//Phi41 with center Cp

My41 := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a2, a3, a4, a5, a6];
Beta := [a1];

// common relations, typically commutators
Comms := [ (a2, a3) = 1, (a2, a4) = 1, (a2, a5) = a1^(-nu),
(a2, a6) = 1, (a3, a4) = 1, (a3, a5)= 1,
 (a3, a6) = a1, (a4, a5) = a2, (a4, a6)= a3, 
(a5, a6)= a4, a1^p = 1] cat
[(a1, Alpha[j]) = Id(F) : j in [1..5]];

L := [];

// G41, 1

G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p = a6^p = 1>;
Append (~L, G);

// G41, 2r
w := PrimitiveRoot (p);

if p mod 3 eq 1 then add := [w^i: i in [0..2]];
else add := [1]; end if;
for r in add do
G := quo <F | Comms, a2^p = a3^p = a4^p = a6^p = 1,
a5^p = a1^r>;
Append (~L, G);
end for;

return L;
end function;

Table3Cyclic_p37To41 := function(p)
   return My37(p) cat My38(p) cat My39(p) cat My40(p) cat My41(p);
end function;

// Checking of column "H"

Check37Col3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 0;
H1 := [];
MinDeg1 := [];

// G37, 1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H1, sub< F | Alpha[2], Alpha[3], Alpha[6]>);
Append (~MinDeg1, p^3);

// G37, 2

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H1, sub< F | Alpha[2], Alpha[3], Alpha[6]>);
Append (~MinDeg1, p^3);

return H1, MinDeg1;
end function;

Check38Col3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 2;
H2 := [];
MinDeg2 := [];

if p eq 5 then

// G38, 1r for p = 5

for r in [0..p-1] do 
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H2, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg2, p^3);
end for;

// G38, 2r for p = 5 

for r in [0,2,3,4] do 
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H2, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg2, p^3);
end for;

// G38, 3 for p = 5 

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H2, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg2, p^3);

return H2, MinDeg2;
end if;

// G38, 1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H2, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg2, p^3);

// G38, 2r

if p mod 5 eq 1 then
for r in [1..5] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H2, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg2, p^3);
end for;
else
for r in [1] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H2, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg2, p^3);
end for;
end if;

// G38, 3r

for r in [1..(p-1)] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H2, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg2, p^3);
end for;

// G38, 4r

if p mod 4 eq 1 then
for r in [1..4] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H2, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg2, p^3);
end for;
else
for r in [1, nu] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H2, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg2, p^3);
end for;
end if;

return H2, MinDeg2;
end function;

Check39Col3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

if p eq 5 then 
count := 12;
else
count := 2 + p + GCD(p-1, 4) + GCD(p-1, 5);
end if;

H3 := [];
MinDeg3 := [];

// G39, 1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H3, sub< F | Alpha[2], Alpha[3], Alpha[6]>);
Append (~MinDeg3, p^3);

// G39, 2r

if p mod 5 eq 1 then
for r in [1..5] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H3, sub< F | Alpha[2], Alpha[3], Alpha[6]>);
Append (~MinDeg3, p^3);
end for;
else 
for r in [1] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H3, sub< F | Alpha[2], Alpha[3], Alpha[6]>);
Append (~MinDeg3, p^3);
end for;
end if;

return H3, MinDeg3;
end function;

Check40Col3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

if p eq 5 then 
count := 13 + GCD(p-1, 5);
else
count := 3 + p + GCD(p-1, 4) + 2*GCD(p-1, 5);
end if;

H4 := [];
MinDeg4 := [];

// G40, 1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H4, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg4, p^3);

// G40, 2

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H4, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg4, p^3);

// G40, 3r

if p mod 3 eq 1 then
for r in [1..3] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H4, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg4, p^3);
end for;
else
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H4, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg4, p^3);
end if;

return H4, MinDeg4;
end function;

Check41Col3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

if p eq 5 then 
count := 15 + GCD(p-1,3) + GCD(p-1, 5);
else
count := 5 + p + GCD(p-1, 3) + GCD(p-1, 4) + 2*GCD(p-1, 5);
end if;

H5 := [];
MinDeg5 := [];

// G41, 1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H5, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg5, p^3);

// G41, 2r

if p mod 3 eq 1 then
for r in [1..3] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H5, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg5, p^3);
end for;
else
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~H5, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg5, p^3);
end if;

return H5, MinDeg5;
end function;

for p in PrimesInInterval (5, 11) do 
   "\n process prime ", p;
   L := Table3Cyclic_p37To41(p);
   H1, MinDeg1 := Check37Col3(L, p);
   H2, MinDeg2 := Check38Col3(L, p);
   H3, MinDeg3 := Check39Col3(L, p);
   H4, MinDeg4 := Check40Col3(L, p);
   H5, MinDeg5 := Check41Col3(L, p);
   H := H1 cat H2 cat H3 cat H4 cat H5;
   MinDeg := MinDeg1 cat MinDeg2 cat MinDeg3 cat MinDeg4 cat MinDeg5;

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

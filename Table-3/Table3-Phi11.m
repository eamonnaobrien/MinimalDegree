load "../setup-permrep.m";

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

// Groups G are listed in the list L.
// d(Z(L[i])) = 3 for all i, i.e., i = 1 to #L

// G11 with centre of type Cp x Cp X Cp

My11 := function(p)

w := PrimitiveRoot(p);

K := GF(p);

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a4, a5, a6];
Beta := [a1, a2, a3];

// common relations, typically commutators
Comms := [
(a4, a5) = a1, (a5, a6) = a3, (a4, a6) = a2] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..3]]: i in [1..3]])
cat &cat([[(Beta[i], Beta[j]) = Id(F) : j in [i + 1..3]]: i in [1..3]]);

L := [];

// G11, 1

G := quo <F | Comms, a1^p = a2^p = a3^p = a4^p = a5^p = a6^p = 1>;
Append (~L, G);

// G11, 3

G := quo <F | Comms, a1^p = a2^p = a3^p = a4^p =   1,
a5^p = a2, a6^p = a1>;
Append (~L, G);

// G11, 5 (p-1 is a quadratic residue)

if IsPower(K!(p-1),2) eq true then
G := quo <F | Comms, a1^p = a2^p = a3^p = 1,
a4^p = a3, a5^p = a2^-1, a6^p = a1>;
Append (~L, G);
end if;

// G11, 5 (p-1 is a non-quadratic residue)

if IsPower(K!(p-1),2) eq false then
G := quo <F | Comms, a1^p = a2^p = a3^p = 1,
a4^p = a3, a5^p = a2^-1, a6^p = a1>;
Append (~L, G);
end if;

// G11, 6

G := quo <F | Comms, a1^p = a2^p = a3^p = a4^p =   1,
a5^p = a1, a6^p = a2>;
Append (~L, G);

// G11, 8

G := quo <F | Comms, a1^p = a2^p = a3^p = a4^p =   1,
a5^p = a1*a2, a6^p = a1*a2>;
Append (~L, G);

// G11, 9r

for r in [2..(p-1) div 2] do
G := quo <F | Comms, a1^p = a2^p = a3^p = a4^p =   1,
a5^p = a1*a2^r, a6^p = a1^r*a2>;
Append (~L, G);
end for;

// G11, 11

G := quo <F | Comms, a1^p = a2^p = a3^p =    1,
a4^p = a1, a5^p = a1, a6^p = a2*a3>;
Append (~L, G);

// G11, 12

G := quo <F | Comms, a1^p = a2^p = a3^p =    1,
a4^p = a1, a5^p = a1*a2, a6^p = a2*a3>;
Append (~L, G);

// G11, 14r (r=1)

for r in [1] do
if IsPower(K!(p-1),2) eq true then
G := quo <F | Comms, a1^p = a2^p = a3^p =    1,
a4^p = a3^r, a5^p = a1, a6^p = a1*a2>;
Append (~L, G);
end if;
end for;

// G11, 14r (r=nu)

for r in [nu] do
if IsPower(K!(p-1),2) eq false then
G := quo <F | Comms, a1^p = a2^p = a3^p =    1,
a4^p = a3^r, a5^p = a1, a6^p = a1*a2>;
Append (~L, G);
end if;
end for;

// G11, 15

G := quo <F | Comms, a1^p = a2^p = a3^p =    1,
a4^p = a3, a5^p = a1*a2, a6^p = a1*a2>;
Append (~L, G);

// G11, 16r

for r in [2..(p-1) div 2] do
G := quo <F | Comms, a1^p = a2^p = a3^p =   1,
a4^p = a3, a5^p = a1*a2^r, a6^p = a1^r*a2>;
Append (~L, G);
end for;

// G11, 17r

for r in [1..(p-1) div 2] do
G := quo <F | Comms, a1^p = a2^p = a3^p =  1,
a4^p = a3, a5^p = a1*a2^(nu*r), a6^p = a1^r*a2>;
Append (~L, G);
end for;

return L;
end function;

// Checking of column "H"

Check11Col3 := function (L, p)

w := PrimitiveRoot(p);

K := GF(p);

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu
nuin := Z ! (1/NonQuadraticResidue (p)); // nu^-1

if IsPower(K!(p-1),2) eq true then
Pair5r1 := function(p)
 for x in GF(p) do
   if x*x eq -1 mod p then 
    return x;
   end if;
end for;
end function;
end if;

if IsPower(K!(p-1),2) eq false then
Pair5r2 := function(p)
 for x in GF(p) do
  for y in GF(p) do
    for z in GF(p) do
       if x*y eq -1 mod p and x*z eq 1 mod p then
         return x,y,z;
       end if;
   end for;
 end for;
end for;
end function;
end if;

if IsPower(K!(p-1),2) eq true then
Pair14r1 := function(p)
 for x in GF(p) do
  for y in GF(p) do
   if x*x eq -1 mod p and x*y eq 1 mod p then 
     return x,y;
   end if;
  end for;
 end for;
end function;
end if;

if IsPower(K!(p-1),2) eq false then
Pair14r2 := function(p)
 for x in GF(p) do
  for y in GF(p) do
   if x*x eq -nuin mod p and x*y eq nuin mod p then 
    return x,y;
   end if;
end for;
end for;
end function;
end if;

count := 0;
T1 := [];
T2 := [];
T3 := [];
MinDeg := [];

// G11, 1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~T1, sub<F | Alpha[2], Alpha[5], Alpha[6]>);
Append (~T2, sub<F | Alpha[3], Alpha[4], Alpha[5]>);
Append (~T3, sub<F | Alpha[1], Alpha[4], Alpha[6]>);
Append (~MinDeg, 3*p^2);

// G11, 3

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~T1, sub<F | Alpha[2], Alpha[4], Alpha[6]>);
Append (~T2, sub<F | Alpha[3], Alpha[4], Alpha[6]*Alpha[5]>);
Append (~T3, sub<F | Alpha[3], Alpha[4], Alpha[6]*Alpha[5]^(-1)>);
Append (~MinDeg, 3*p^2);

// G11, 5

if IsPower(K!(p-1),2) eq true then
x := Pair5r1(p);
x := Z ! x;
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~T1, sub<F | Alpha[6], Alpha[5]^(x)*Alpha[4]>);
Append (~T2, sub<F | Alpha[5], Alpha[6]^(x)*Alpha[4]>);
Append (~T3, sub<F | Alpha[4], Alpha[5]^(x)*Alpha[6]>);
Append (~MinDeg, 3*p^2);
end if;

// G11, 5

if IsPower(K!(p-1),2) eq false then
count := count+1;
F := L[count];
for y in [1..(p-1) div 2] do
for x in [1..(p-1) div 2] do
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
H1 := sub<F | Alpha[6]*Alpha[4]^(x), 
Alpha[5]*Alpha[4]^(y)>;
H2:= sub<F | Alpha[6]*Alpha[4]^(x), 
Alpha[5]*Alpha[4]^(-y)>;
H3 := sub<F | Alpha[6]*Alpha[4]^(-x), 
Alpha[5]*Alpha[4]^(y)>;
Q, phi := pQuotient (F, p, 10);
 IH1 := phi (H1); IH2 := phi (H2); IH3 := phi (H3);
if #IH1 eq p^4 and #IH2 eq p^4 and #IH3 eq p^4 then
Append (~T1, H1);
Append (~T2, H2);
Append (~T3, H3);
break;
end if;
end for;
if #IH1 eq p^4 and #IH2 eq p^4 and #IH3 eq p^4 then
break;
end if;
end for;
Append (~MinDeg, 3*p^2);
end if;

// G11, 6

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~T1, sub<F | Alpha[3], Alpha[4], Alpha[6]>);
Append (~T2, sub<F | Alpha[3], Alpha[4], Alpha[5]>);
Append (~T3, sub<F | Alpha[2], Alpha[4], Alpha[6]*Alpha[5]>);
Append (~MinDeg, 3*p^2);

// G11, 8

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~T1, sub<F | Alpha[3], Alpha[4],
 Alpha[6]*Alpha[5]^(-1)>);
Append (~T2, sub<F | Alpha[3], Alpha[5], Alpha[6]>);
Append (~T3, sub<F | Alpha[2], Alpha[4], Alpha[6]>);
Append (~MinDeg, 3*p^2);

// G11, 9r

for r in [2..(p-1) div 2] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~T1, sub<F | Alpha[3], Alpha[4],
 Alpha[5]*Alpha[6]^(-1)>);
Append (~T2, sub<F | Alpha[3], Alpha[4],
 Alpha[5]*Alpha[6]>);
Append (~T3, sub<F | Alpha[2], Alpha[4], Alpha[6]>);
Append (~MinDeg, 3*p^2);
end for;

// G11, 11

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~T1, sub<F | Alpha[3], Alpha[4], Alpha[5]>);
Append (~T2, sub<F | Alpha[5]*Alpha[4], Alpha[6]>);
Append (~T3, sub<F | Alpha[5]*Alpha[4]^(-1), Alpha[6]>);
Append (~MinDeg, 3*p^2);

// G11, 12

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~T1, sub<F | Alpha[5]*Alpha[4]^(-1), Alpha[6]>);
Append (~T2, sub<F | Alpha[4], Alpha[5]>);
Append (~T3, sub<F | Alpha[5]*Alpha[4], Alpha[6]>);
Append (~MinDeg, 3*p^2);

// G11, 14r (r=1)

if IsPower(K!(p-1),2) eq true then
x, y := Pair14r1(p);
    x := Z ! x;
    y := Z ! y;
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~T1, sub<F | Alpha[5], Alpha[4]>);
Append (~T2, sub<F | Alpha[6]*Alpha[4]^(nu), Alpha[5]*Alpha[4]^(x)>);
Append (~T3, sub<F | Alpha[6]*Alpha[4]^(-nu), Alpha[5]*Alpha[4]^(y)>);
Append (~MinDeg, 3*p^2);
end if;

// G11, 14r (r=nu)

if IsPower(K!(p-1),2) eq false then
x, y := Pair14r2(p);
    x := Z ! x;
    y := Z ! y;
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~T1, sub<F | Alpha[5], Alpha[4]>);
Append (~T2, sub<F | Alpha[6]*Alpha[4]^(nu), Alpha[5]*Alpha[4]^(x)>);
Append (~T3, sub<F | Alpha[6]*Alpha[4]^(-nu), Alpha[5]*Alpha[4]^(y)>);
Append (~MinDeg, 3*p^2);
end if;

// G11, 15

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
Append (~T1, sub<F | Alpha[6]*Alpha[5], Alpha[4]>);
Append (~T2, sub<F | Alpha[6]*Alpha[5]^(-1), Alpha[5]*Alpha[4]>);
Append (~T3, sub<F | Alpha[6]*Alpha[5]^(-1), Alpha[4]>);
Append (~MinDeg, 3*p^2);

// G11, 16r

for r in [2..(p-1) div 2] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
H1 := sub<F | Alpha[6]*Alpha[5], Alpha[4]>;
H2:= sub<F | Alpha[6]*Alpha[5]^(-1), Alpha[4]>;
for x in [0..(p-1)] do
for y in [0..(p-1)] do
H3 := sub<F | Alpha[6]*Alpha[4]^(x), Alpha[5]*Alpha[4]^(y)>;
Q, phi := pQuotient (F, p, 10);
IH3 := phi (H3);
if #IH3 eq p^4 then
Append (~T3, H3);
break;
end if;
end for;
if #IH3 eq p^4 then
break;
end if;
end for;
Append (~T1, H1);
Append (~T2, H2);
Append (~MinDeg, 3*p^2);
end for;

// G11, 17r

for r in [1..(p-1) div 2] do
count := count+1;
F := L[count];
for y in [1..(p-1) div 2] do
for x in [1..(p-1) div 2] do
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
H1 := sub<F | Alpha[6]*Alpha[4]^(x), Alpha[5]*Alpha[4]^(y)>;
H2:= sub<F | Alpha[6]*Alpha[4]^(x), Alpha[5]*Alpha[4]^(-y)>;
H3 := sub<F | Alpha[6]*Alpha[4]^(-x), Alpha[5]*Alpha[4]^(y)>;
Q, phi := pQuotient (F, p, 10);
IH1 := phi (H1); IH2 := phi (H2); IH3 := phi (H3);
if #IH1 eq p^4 and #IH2 eq p^4 and #IH3 eq p^4 then
Append (~T1, H1);
Append (~T2, H2);
Append (~T3, H3);
break;
end if;
end for;
if #IH1 eq p^4 and #IH2 eq p^4 and #IH3 eq p^4 then
break;
end if;
end for;
Append (~MinDeg, 3*p^2);
end for;

return T1, T2, T3, MinDeg;
end function;

MAX := 7^6;

for p in PrimesInInterval (5, 11) do 
  "\n process prime ", p;
  L := My11(p);

  T1, T2, T3, MinDeg := Check11Col3(L, p);

  for i in [1..#L] do
     G := L[i];
     Q, phi := pQuotient(G, p, 10);
     A := phi(T1[i]);
     B := phi(T2[i]);
     C := phi(T3[i]);
     m1 := Index(Q, A);
     m2 := Index(Q, B);
     m3 := Index(Q, C);
     m := m1 + m2 + m3;
     C1 := Core(Q, A);
     C2 := Core(Q, B);
     C3 := Core(Q, C);
     CI := C1 meet C2 meet C3;
     assert #CI eq 1;
     phiA := CosetAction (Q, A);
     phiB := CosetAction (Q, B);
     phiC := CosetAction (Q, C);
     pi := PermutationRepresentationSumH (Q, [phiA, phiB, phiC]);
     J := Image (pi);
     assert #J eq #Q;
     if #J le MAX then assert IsIsomorphic (J, Q); end if;
     assert Degree (J) eq m;
     assert Degree (J) eq MinDeg[i];
  end for;
end for;

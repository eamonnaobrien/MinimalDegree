load "../setup-permrep.m";

//Phi21 with center Cp X Cp

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

My21 := function(p)
Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu
nuin := Z ! (1/NonQuadraticResidue (p)); // nu^-1

PairPhi2112 := function(p)
 for x in GF(p) do
  for y in GF(p) do
   if (x*x - nuin*y*y) eq nuin then 
    return x,y;
   end if;
  end for;
 end for;
end function;

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a3, a4, a5, a6];
Beta := [a1, a2];

// common relations, typically commutators
Comms := [
(a3, a4) = 1, (a3, a5)= a1, (a3, a6) = a2,
(a4, a5) = a2, (a4, a6)= a1^(nu), (a5, a6)= a3,  
(a1, a2) = 1, a1^p = 1, a2^p = 1, a3^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..4]]: i in [1..2]]);

L := [];

// G21, 1

G := quo <F | Comms,  a4^p = a5^p = a6^p = 1>;
Append (~L, G);

// G21, 3r

if (p mod 4) eq 1 then
for r in [1,nu] do
G := quo <F | Comms,  a4^p = a6^p = 1, a5^p = a1^r>;
Append (~L, G);
end for;

elif (p mod 4) eq 3 then
G := quo <F | Comms,  a4^p = a6^p = 1, a5^p = a1>;
Append (~L, G);
end if;

// G21, 4r

for r in [1,nu] do
G := quo <F | Comms,  a4^p = a6^p = 1, a5^p = a2^r>;
Append (~L, G);
end for;

// G21, 5rs

for r in [1,nu] do
for s in [1..(p-1) div 2] do
G := quo <F | Comms,  a4^p = a6^p = 1, a5^p = a2^r*a1^s>;
Append (~L, G);
end for;
end for;

// G21, 8

G := quo <F | Comms,  a4^p = 1,  a5^p = a1, a6^p = a2>;
Append (~L, G);

// G21, 9

G := quo <F | Comms,  a4^p = 1,  a5^p = a2^nuin, a6^p = a1>;
Append (~L, G);

// G21, 10r

for r in [1..(p-1) div 2] do
G := quo <F | Comms,  a4^p = 1,  a5^p = a2^(r*nuin)*a1, a6^p = a2*a1^r>;
Append (~L, G);
end for;

// G21, 11

G := quo <F | Comms,  a4^p = 1,  a5^p = a1^(-1), a6^p = a2>;
Append (~L, G);

// G21, 12

x, y := PairPhi2112(p);
x := Z ! x;
y := Z ! y;
G := quo <F | Comms,  a4^p = 1,  a5^p = a2^(-y*nuin mod p)*a1^(-x),
a6^p = a2^x*a1^y>;
Append (~L, G);

// G21, 13r
if (p mod 4) eq 1 then
for r in [2..(p-2)] do
G := quo <F | Comms,  a4^p = 1,  a5^p = a1^(r-1),
a6^p = a2^(r+1)>;
Append (~L, G);
end for;
else
for r in [2..(p-1) div 2] do
G := quo <F | Comms,  a4^p = 1,  a5^p = a1^(r-1),
a6^p = a2^(r+1)>;
Append (~L, G);
end for;
end if;

// G21, 14r
if (p mod 4) eq 1 then
for r in [1..(p-1) div 2] do
G := quo <F | Comms,  a4^p = 1,  a5^p = a2^(r*nuin mod p)*a1^(-1),
a6^p = a2*a1^r>;
Append (~L, G);
end for;
else
for r in [1..(p-1)] do
if (r*r mod p) ne p-nu then
G := quo <F | Comms,  a4^p = 1,  a5^p = a2^(r*nuin mod p)*a1^(-1),
a6^p = a2*a1^r>;
Append (~L, G);
end if;
end for;
end if;

// G21, 15rs
if (p mod 4) eq 1 then
   for r in [1..(p-1)] do
      for s in [1..(p-1) div 2] do
         if (r*r - nuin*s*s) mod p ne 1 then
            G := quo <F | Comms,  a4^p = 1,  a5^p = a2^(s*nuin mod p)*a1^(r-1),
                           a6^p = a2^((1+r) mod p)*a1^s>;
            Append (~L, G);
         end if;
      end for;
   end for;
else
   for r in [1..(p-1) div 2] do
      for s in [1..(p-1)] do
         if (r*r - nuin*s*s) mod p ne 1 then
            G := quo <F | Comms,  a4^p = 1,  a5^p = a2^(s*nuin mod p)*a1^(r-1),
                          a6^p = a2^((1+r) mod p)*a1^s>;
            Append (~L, G);
         end if;
      end for;
   end for;
end if;

// G21, 16k
if (p mod 4) eq 1 then
for k in [1..(p-1) div 2] do
x, y := PairPhi2112(p);
x := Z ! x;
y := Z ! y;
G := quo <F | Comms,  a4^p = 1,  a5^p = a2^(-y*nuin mod p)*a1^(k-x),
a6^p = a2^((k+x) mod p)*a1^y>;
Append (~L, G);
end for;
else
for k in [1..(p-1)] do
x, y := PairPhi2112(p);
x := Z ! x;
y := Z ! y;
G := quo <F | Comms,  a4^p = 1,  a5^p = a2^(-y*nuin mod p)*a1^(k-x),
a6^p = a2^((k+x) mod p)*a1^y>;
Append (~L, G);
end for;
end if;

// G21, 17k
if (p mod 4) eq 1 then
for k in [1..(p-1)] do
if (k*k mod p) ne p-1 then
x, y := PairPhi2112(p);
x := Z ! x;
y := Z ! y;
G := quo <F | Comms,  a4^p = 1,  a5^p = a2^(nuin*(k-y) mod p)*a1^(-x),
a6^p = a2^x*a1^((k+y) mod p)>;
Append (~L, G);
end if;
end for;
else
for k in [1..(p-1) div 2] do
x, y := PairPhi2112(p);
x := Z ! x;
y := Z ! y;
G := quo <F | Comms,  a4^p = 1,  a5^p = a2^(nuin*(k-y) mod p)*a1^(-x),
a6^p = a2^x*a1^((k+y) mod p)>;
Append (~L, G);
end for;
end if;

// G21, 18rs
if (p mod 4) eq 1 then
for r in [1..(p-1) div 2] do
for s in [1..(p-1)] do
if (r*r - nuin*s*s) mod p ne nuin then
x, y := PairPhi2112(p);
x := Z ! x;
y := Z ! y;
G := quo <F | Comms,  a4^p = 1,  a5^p = a2^(nuin*(s-y) mod p)*a1^(r-x),
a6^p = a2^((x+r) mod p)*a1^((y+s) mod p)>;
Append (~L, G);
end if;
end for;
end for;
else
for r in [1..(p-1)] do
for s in [1..(p-1) div 2] do
if (r*r - nuin*s*s) mod p ne nuin then
x, y := PairPhi2112(p);
x := Z ! x;
y := Z ! y;
G := quo <F | Comms,  a4^p = 1,  a5^p = a2^(nuin*(s-y) mod p)*a1^(r-x),
a6^p = a2^((x+r) mod p)*a1^((y+s) mod p)>;
Append (~L, G);
end if;
end for;
end for;
end if;

// G21, 2

G := quo <F | Comms,  a5^p = a6^p = 1, a4^p = a1>;
Append (~L, G);

// G21, 6r

for r in [1..(p-1)] do
G := quo <F | Comms,  a4^p = a2,  a5^p = 1, a6^p = a1^r>;
Append (~L, G);
end for;

// G21, 7rs

for r in [0..(p-1)] do
for s in [1..(p-1) div 2] do
G := quo <F | Comms,  a4^p = a2^r*a1, a5^p = 1, a6^p = a2^s>;
Append (~L, G);
end for;
end for;

return L;
end function;


Check21 := function(L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu
nuin := Z ! (1/NonQuadraticResidue (p)); // nu^-1

PairPhi2112 := function(p)
 for x in GF(p) do
  for y in GF(p) do
   if (x*x - nuin*y*y) eq nuin then 
    return x,y;
   end if;
  end for;
 end for;
end function;

count := 0;

PFlist1 := []; // lists the group G
PRlist1 := []; // lists the subgroup R
PNlist1 := []; // lists kernel of non-linear irr char from R
PSlist1 := []; // lists the subgroup S
PMlist1 := []; // lists kernel of non-linear irr char from S
Mu1 := [];     // Mu(G) from table

// G21, 1

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4), phi(F.1)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.3)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2)>;
GPM := sub<GPS  | phi(F.2), phi(F.4), phi(F.3)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, 2*p^3);

// G21, 3r

if (p mod 4) eq 1 then
for r in [1,nu] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4), phi(F.1)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.3)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2)>;
GPM := sub<GPS  | phi(F.2), phi(F.4), phi(F.3)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, 2*p^3);
end for;
elif (p mod 4) eq 3 then
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4), phi(F.1)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.3)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2)>;
GPM := sub<GPS  | phi(F.2), phi(F.4), phi(F.3)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, 2*p^3);
end if;

// G21, 4r

for r in [1,nu] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4), phi(F.1)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.3)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2)>;
GPM := sub<GPS  | phi(F.2), phi(F.4), phi(F.3)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, 2*p^3);
end for;

// G21, 5rs

for r in [1,nu] do
for s in [1..(p-1) div 2] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4), phi(F.1)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.3)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2)>;
GPM := sub<GPS  | phi(F.2), phi(F.4), phi(F.3)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, 2*p^3);
end for;
end for;

// G21, 8

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4), phi(F.1)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.3)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2)>;
GPM := sub<GPS  | phi(F.2), phi(F.4), phi(F.3)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, 2*p^3);

// G21, 9

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4), phi(F.1)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.3)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2)>;
GPM := sub<GPS  | phi(F.2), phi(F.4), phi(F.3)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, 2*p^3);

// G21, 10r

for r in [1..(p-1) div 2] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4), phi(F.1)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.3)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2)>;
GPM := sub<GPS  | phi(F.2), phi(F.4), phi(F.3)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, 2*p^3);
end for;

// G21, 11

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4), phi(F.1)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.3)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2)>;
GPM := sub<GPS  | phi(F.2), phi(F.4), phi(F.3)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, 2*p^3);

// G21, 12

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4), phi(F.1)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.3)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2)>;
GPM := sub<GPS  | phi(F.2), phi(F.4), phi(F.3)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, 2*p^3);

// G21, 13r

if (p mod 4) eq 1 then
      for r in [2..(p-2)] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4), phi(F.1)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.3)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2)>;
GPM := sub<GPS  | phi(F.2), phi(F.4), phi(F.3)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, 2*p^3);
end for;
else
for r in [2..(p-1) div 2] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4), phi(F.1)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.3)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2)>;
GPM := sub<GPS  | phi(F.2), phi(F.4), phi(F.3)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, 2*p^3);
end for;
end if;

// G21, 14r

if (p mod 4) eq 1 then
for r in [1..(p-1) div 2] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4), phi(F.1)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.3)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2)>;
GPM := sub<GPS  | phi(F.2), phi(F.4), phi(F.3)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, 2*p^3);
end for;
else
for r in [1..(p-1)] do
if (r*r mod p) ne p-nu then
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4), phi(F.1)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.3)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2)>;
GPM := sub<GPS  | phi(F.2), phi(F.4), phi(F.3)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, 2*p^3);
end if;
end for;
end if;

// G21, 15rs

if (p mod 4) eq 1 then
for r in [1..(p-1)] do
for s in [1..(p-1) div 2] do
if (r*r - nuin*s*s) mod p ne 1 then
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4), phi(F.1)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.3)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2)>;
GPM := sub<GPS  | phi(F.2), phi(F.4), phi(F.3)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, 2*p^3);
end if;
end for;
end for;
else
for r in [1..(p-1) div 2] do
for s in [1..(p-1)] do
if (r*r - nuin*s*s) mod p ne 1 then
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4), phi(F.1)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.3)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2)>;
GPM := sub<GPS  | phi(F.2), phi(F.4), phi(F.3)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, 2*p^3);
end if;
end for;
end for;
end if;


// G21, 16k

if (p mod 4) eq 1 then
for k in [1..(p-1) div 2] do
x, y := PairPhi2112(p);
x := Z ! x;
y := Z ! y;
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4), phi(F.1)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.3)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2)>;
GPM := sub<GPS  | phi(F.2), phi(F.4), phi(F.3)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, 2*p^3);
end for;
else
for k in [1..(p-1)] do
x, y := PairPhi2112(p);
x := Z ! x;
y := Z ! y;
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4), phi(F.1)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.3)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2)>;
GPM := sub<GPS | phi(F.2), phi(F.4), phi(F.3)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, 2*p^3);
end for;
end if;

// G21, 17k

if (p mod 4) eq 1 then
for k in [1..(p-1)] do
if (k*k mod p) ne p-1 then
x, y := PairPhi2112(p);
x := Z ! x;
y := Z ! y;
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4), phi(F.1)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.3)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2)>;
GPM := sub<GPS | phi(F.2), phi(F.4), phi(F.3)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, 2*p^3);
end if;
end for;
else
for k in [1..(p-1) div 2] do
x, y := PairPhi2112(p);
x := Z ! x;
y := Z ! y;
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4), phi(F.1)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.3)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2)>;
GPM := sub<GPS | phi(F.2), phi(F.4), phi(F.3)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, 2*p^3);
end for;
end if;


// G21, 18rs

if (p mod 4) eq 1 then
for r in [1..(p-1) div 2] do
for s in [1..(p-1)] do
if (r*r - nuin*s*s) mod p ne nuin then
x, y := PairPhi2112(p);
x := Z ! x;
y := Z ! y;
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4), phi(F.1)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.3)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2)>;
GPM := sub<GPS | phi(F.2), phi(F.4), phi(F.3)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, 2*p^3);
end if;
end for;
end for;
else
for r in [1..(p-1)] do
for s in [1..(p-1) div 2] do
if (r*r - nuin*s*s) mod p ne nuin then
x, y := PairPhi2112(p);
x := Z ! x;
y := Z ! y;
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4), phi(F.1)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.3)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2)>;
GPM := sub<GPS | phi(F.2), phi(F.4), phi(F.3)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, 2*p^3);
end if;
end for;
end for;
end if;

// G21, 2

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4)>;
GPN := sub<GPR | phi(F.4), phi(F.3)>;
GPS := sub<GPF | phi(F.6), phi(F.3), phi(F.4^p), phi(F.2)>;
GPM := sub<GPS | phi(F.2), phi(F.6), phi(F.3)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, 2*p^3);

// G21, 6r

for r in [1..(p-1)] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4)>;
GPN := sub<GPR | phi(F.4), phi(F.3)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.5), phi(F.2)>;
GPM := sub<GPS | phi(F.1), phi(F.5), phi(F.3)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, 2*p^3);
end for;

// G21, 7rs

for r in [0..(p-1)] do
for s in [1..(p-1) div 2] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4)>;
GPN := sub<GPR | phi(F.4), phi(F.3)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.6), phi(F.2)>;
GPM := sub<GPS | phi(F.2), phi(F.6), phi(F.3)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, 2*p^3);
end for;
end for;

return PFlist1, PRlist1, PNlist1, PSlist1, PMlist1, Mu1;
end function;

MAX := 7^6;
for p in PrimesInInterval (5, 11) do 
   "\nprocess p = ", p;
   L := My21(p);
   "#L is ", #L;
   PFlist1, PRlist1, PNlist1, PSlist1, PMlist1, Mu1 := Check21(L, p);
   PFlist := PFlist1;
   PRlist := PRlist1;
   PNlist := PNlist1;
   PSlist := PSlist1;
   PMlist := PMlist1;
   MinDeg := Mu1;

   for i in [1..#L] do
      PF := PFlist[i];
      PR := PRlist[i];
      PN := PNlist[i];
      PS := PSlist[i];
      PM := PMlist[i];
      Mu_value := MinDeg[i];

      Int := Core(PF, PN) meet Core(PF, PM);
      assert #Int eq 1;
      // printf "%o  %o\n", i, #Int;

      phiN := CosetAction (PF, PN);
      phiM := CosetAction (PF, PM);
      pi := PermutationRepresentationSumH (PF, [phiN, phiM]);
      J := Image (pi);
      assert #J eq #PF;
      if #J le MAX then assert IsIsomorphic (J, PF); end if;
      assert Degree (J) eq Mu_value;

      // Irreducibility checks for X_G 
      QPRN, f := quo<PR | PN>;
      linQP := LinearCharacters(QPRN);
      for j in [1..#linQP] do
         if IsFaithful(linQP[j]) eq true then
            chi := linQP[j];
            break;
         end if;
      end for;
      chi_bar := LiftCharacter(chi, f, PR);
      psi := Induction(chi_bar, PF);
      assert IsIrreducible(psi);

      QPSM, h := quo<PS | PM>;
      linQPM := LinearCharacters (QPSM);
      for j in [1..#linQPM] do
         if IsFaithful(linQPM[j]) eq true then
            lambda := linQPM[j];
            break;
         end if;
      end for;
      lambda_bar := LiftCharacter(lambda, h, PS);
      eta := Induction(lambda_bar, PF);
      assert IsIrreducible(eta);

   end for;
end for;

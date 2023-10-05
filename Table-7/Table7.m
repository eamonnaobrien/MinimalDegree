load "../setup-permrep.m";

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

// For all the groups in the list, c(G) = p^4

//Phi25 with center Cp

My25 := function(p)

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a2, a3, a4, a5, a6];
Beta := [a1];

// common relations, typically commutators
Comms := [ (a2, a3) = 1, (a2, a4) = 1, (a2, a5) = 1,
(a2, a6) = a1, (a3, a4) = 1, (a3, a5)= 1,
 (a3, a6) = a2, (a4, a5) = a1, (a4, a6)= a3, 
(a5, a6)= 1, a1^p = 1, a2^p = 1, a3^p = a1, a6^p = a5] cat
[(a1, Alpha[j]) = Id(F) : j in [1..5]];

L := [];

// G25, 1

G := quo <F | Comms, a6^(p^2) = 1,
a4^p = a2*a1^(-1)>;
Append (~L, G);

// G25, 2r

for r in [1..(p-1) div 2] do
G := quo <F | Comms,  a6^(p^2) = 1,
a4^p = a2*a1^(r-1)>;
Append (~L, G);
end for;

// G25, 3

G := quo <F | Comms, 
a4^p = a2, a6^(p^2) = a1>;
Append (~L, G);

return L;
end function;

//Phi26 with center Cp

My26 := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a2, a3, a4, a5, a6];
Beta := [a1];

// common relations, typically commutators
Comms := [ (a2, a3) = 1, (a2, a4) = 1, (a2, a5) = 1,
(a2, a6) = a1, (a3, a4) = 1, (a3, a5)= 1,
 (a3, a6) = a2^nu, (a4, a5) = a1, (a4, a6)= a3, 
(a5, a6)= 1, a1^p = 1, a2^p = 1, a3^p = a1,
 a6^p = a5] cat
[(a1, Alpha[j]) = Id(F) : j in [1..5]];

L := [];

// G26, 1

G := quo <F | Comms, a6^(p^2) = 1,
a4^p = a2*a1^(-1)>;
Append (~L, G);

// G26, 2r

for r in [1..(p-1) div 2] do
G := quo <F | Comms,  a6^(p^2) = 1,
a4^p = a2*a1^(r-1)>;
Append (~L, G);
end for;

// G26, 3

G := quo <F | Comms, 
a4^p = a2, a6^(p^2) = a1>;
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

// G27, 4r

for r in [1,nu] do
G := quo <F | Comms, a2^p = a3^p = a5^p = a6^p =  1,
a4^p = a1^r>;
Append (~L, G);
end for;

return L;
end function;


//Phi28 with center Cp

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

// G28, 1

G := quo <F | Comms,   a6^(p^2) = 1>;
Append (~L, G);

// G28, 2r

for r in [1..(p-2)] do
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

// G29, 1

G := quo <F | Comms,   a6^(p^2) = 1>;
Append (~L, G);

// G29, 2r

for r in [1..(p-2)] do
G := quo <F | Comms,   a6^(p^2) = a1^r>;
Append (~L, G);
end for;

return L;
end function;

//Phi30 with center Cp

My30 := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

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

// G30, 3r
w := PrimitiveRoot (p);

if p mod 3 eq 1 then add := [w^i: i in [0..2]];
else add := [1]; end if;
for r in add do
G := quo <F | Comms, a2^p = a3^p = a4^p = a6^p =  1,
a5^p = a1^r>;
Append (~L, G);
end for;

// G30, 5r
w := PrimitiveRoot (p);

if p mod 3 eq 1 then add := [w^i: i in [0..2]];
else add := [1]; end if;
for r in add do
G := quo <F | Comms, a2^p = a3^p =  a6^p =  1,
a4^p = a1^r, a5^p = a1^r>;
Append (~L, G);
end for;

return L;
end function;

//Phi31 with center Cp

My31 := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

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

// G31, 2

G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p = 1,
a6^p = a1>;
Append (~L, G);

// G31, 5r

for r in [1,nu] do
G := quo <F | Comms, a2^p = a3^p = a5^p = 1,
a4^p = a1, a6^p = a1^r>;
Append (~L, G);
end for;

// G31, 6

G := quo <F | Comms, a2^p = a3^p = 1,
a4^p = a1, a5^p = a1, a6^p = a1>;
Append (~L, G);


return L;
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

// G32, 2

G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p = 1, 
a6^p = a1>;
Append (~L, G);

// G32, 4r

for r in [1,nu] do
G := quo <F | Comms, a2^p = a3^p = a5^p = 1, 
a4^p = a1, a6^p = a1^r>;
Append (~L, G);
end for;

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

// G33, 4r

for r in [1,nu] do
G := quo <F | Comms, a2^p = a3^p = a4^p = a6^p = 1, 
a5^p = a1^r>;
Append (~L, G);
end for;

return L;
end function;


//Phi34 with center Cp

My34 := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

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

// G34, 2r

for r in [1,nu] do
G := quo <F | Comms, a2^p = 1, a4^p = a1^r>;
Append (~L, G);
end for;

return L;
end function;

//Phi37 with center Cp

My37 := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a2, a3, a4, a5, a6];
Beta := [a1];

// common relations, typically commutators
Comms := [ (a2, a3) = 1, (a2, a4) = 1, (a2, a5) = a1,
(a2, a6) = 1, (a3, a4) = a1^(-1), (a3, a5)= a1,
(a3, a6) = a2, 
(a4, a5) = 1, 
(a4, a6)= a3, 
(a5, a6)= a4, a1^p = 1] cat
[(a1, Alpha[j]) = Id(F) : j in [1..5]];

L := [];

// G37, 3r

for r in [1,nu] do
G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p = 1,
a6^p = a1^r>;
Append (~L, G);
end for;

// G37, 4r
w := PrimitiveRoot (p);

if p mod 4 eq 1 then add := [w^i: i in [0..3]];
else add := [1,nu]; end if;
for r in add do
G := quo <F | Comms, a2^p = a3^p = a4^p = 1,
a5^p =  a1, a6^p = a1^r>;
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

// G39, 3r
w := PrimitiveRoot (p);

if p mod 3 eq 1 then add := [w^i: i in [0..5]];
else add := [1,nu]; end if;
for r in add do
G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p = 1,
a6^p = a1^r>;
Append (~L, G);
end for;

// G39, 4r

if p eq 5 then
for r in [1..(p-1)] do
G := quo <F | Comms, a2^p = a3^p = a4^p = 1,
a5^p = a1, a6^p = a1^r>;
Append (~L, G);
end for;
else
for r in [1..(p-1)] do
G := quo <F | Comms, a2^p = a3^p = a4^p = 1,
a5^p = a1^r, a6^p = a1^r>;
Append (~L, G);
end for;
end if;

return L;
end function;

//Phi42 with center Cp

PairPhi42 := function(k, p)
 for x in GF(p) do
  for y in GF(p) do
   if (x*x - y*y) eq k then
    return x,y;
   end if;
  end for;
 end for;
end function;

My42 := function(p)

Z := Integers ();
    nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a2, a3, a4, a5, a6];
Beta := [a1];

// common relations, typically commutators
Comms := [ (a2, a3) = 1, (a2, a4) = 1, (a2, a5) = a1^(-1),
(a2, a6) = 1, (a3, a4) = 1, (a3, a5)= 1,
 (a3, a6) = a1, (a4, a5) = a2, (a4, a6)= a3, 
(a5, a6)= a4, a1^p = 1, a4^p = a1,
a2^p = 1, a3^p = 1] cat
[(a1, Alpha[j]) = Id(F) : j in [1..5]];

L := [];

// G42, 1

G := quo <F | Comms, a5^p = a3*a1^(-1), a6^p = a2*a1>;
Append (~L, G);

// G42, 2

G := quo <F | Comms, a5^p = a3, a6^p = a2>;
Append (~L, G);

// G42, 3k

for k in [1..(p-1)] do
    x, y := PairPhi42 (k, p);
    x := Z ! x;
    y := Z ! y;
G := quo <F | Comms, a5^p = a3*a1^(-x-1), a6^p = a2*a1^(1-y)>;
Append (~L, G);
end for;

return L;
end function;

//Phi43 with center Cp

My43 := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu
nuin := Z ! (1/NonQuadraticResidue (p)); // nu^-1

PairPhi43 := function(k, p)
 for x in GF(p) do
  for y in GF(p) do
   if (x*x - nuin*y*y) eq k then
    return x,y;
   end if;
  end for;
 end for;
end function;

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a2, a3, a4, a5, a6];
Beta := [a1];

// common relations, typically commutators
Comms := [ (a2, a3) = 1, (a2, a4) = 1, (a2, a5) = a1^(-nuin),
(a2, a6) = 1, (a3, a4) = 1, (a3, a5)= 1,
 (a3, a6) = a1, (a4, a5) = a2, (a4, a6)= a3, 
(a5, a6)= a4, a1^p = 1, a4^p = a1,
a2^p = 1, a3^p = 1] cat
[(a1, Alpha[j]) = Id(F) : j in [1..5]];

L := [];

// G43, 1

G := quo <F | Comms, a5^p = a3*a1^(-1), a6^p = a2^nu*a1>;
Append (~L, G);

// G43, 2k

for k in [1..(p-1)] do
    x, y := PairPhi43(k, p);
    x := Z ! x;
    y := Z ! y;
G := quo <F | Comms, a5^p = a3*a1^(-x-1), a6^p = a2^nu*a1^(1-y)>;
Append (~L, G);
end for;

return L;
end function;

Table7 := function(p)
return My25(p) cat My26(p) cat My27(p) cat My28(p)
   cat My29(p) cat My30(p) cat My31(p) cat My32(p)
   cat My33(p) cat My34(p) cat My37(p) cat My39(p)
   cat My42(p) cat My43(p);
end function;

Check25 := function(L, p)

Z := Integers ();

count := 0;

PFlist1 := [];
PRlist1 := [];
PNlist1 := [];

// G25, 1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.5)>;
GPN := sub<GPR | phi(F.2), phi(F.5)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);

// G25, 2r

for r in [1..(p-1) div 2] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.5)>;
GPN := sub<GPR | phi(F.2), phi(F.5)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
end for;

// G25, 3

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.3), phi(F.4)>;
GPN := sub<GPR | phi(F.4)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);

return PFlist1, PRlist1, PNlist1;
end function;

Check26 := function(L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 2 + (p-1) div 2;

PFlist2 := [];
PRlist2 := [];
PNlist2 := [];

// G26, 1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist2, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.5)>;
GPN := sub<GPR | phi(F.2), phi(F.5)>;
Append(~PRlist2, GPR);
Append(~PNlist2, GPN);

// G26, 2r

for r in [1..(p-1) div 2] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist2, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.5)>;
GPN := sub<GPR | phi(F.2), phi(F.5)>;
Append(~PRlist2, GPR);
Append(~PNlist2, GPN);
end for;

// G26, 3

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist2, GPF);
GPR := sub<GPF | phi(F.3), phi(F.4)>;
GPN := sub<GPR | phi(F.4)>;
Append(~PRlist2, GPR);
Append(~PNlist2, GPN);

return PFlist2, PRlist2, PNlist2;
end function;

Check27 := function(L, p)

Z := Integers ();
    nu := Z ! (NonQuadraticResidue (p)); // nu

count := p+3;

PFlist3 := [];
PRlist3 := [];
PNlist3 := [];

// G27, 4r
for r in [1,nu] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist3, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4)>;
GPN := sub<GPR | phi(F.2), phi(F.3)>;
Append(~PRlist3, GPR);
Append(~PNlist3, GPN);
end for;

return PFlist3, PRlist3, PNlist3;
end function;

Check28 := function(L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := p+5;

PFlist4 := [];
PRlist4 := [];
PNlist4 := [];

// G28, 1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist4, GPF);
GPR := sub<GPF | phi(F.3), phi(F.4^p), phi(F.6^p)>;
GPN := sub<GPR | phi(F.4^p), phi(F.6^p)>;
Append(~PRlist4, GPR);
Append(~PNlist4, GPN);

// G28, 2r (r = 1,...,(p-2))

for r in [1..(p-2)] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist4, GPF);
GPR := sub<GPF | phi(F.4), phi(F.3)*phi(F.2)*phi(F.6^p) >;
GPN := sub<GPR | phi(F.4)>;
Append(~PRlist4, GPR);
Append(~PNlist4, GPN);
end for;

return PFlist4, PRlist4, PNlist4;
end function;

Check29 := function(L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 2*p+4;

PFlist5 := [];
PRlist5 := [];
PNlist5 := [];

// G29, 1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist5, GPF);
GPR := sub<GPF | phi(F.3), phi(F.4^p), phi(F.6^p)>;
GPN := sub<GPR | phi(F.4^p), phi(F.6^p)>;
Append(~PRlist5, GPR);
Append(~PNlist5, GPN);

// G29, 2r (r = 1,...,(p-2))

for r in [1..(p-2)] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist5, GPF);
GPR := sub<GPF | phi(F.4), phi(F.3)*phi(F.2)*phi(F.6^p)>;
GPN := sub<GPR | phi(F.4)>;
Append(~PRlist5, GPR);
Append(~PNlist5, GPN);
end for;

return PFlist5, PRlist5, PNlist5;
end function;

Check30 := function(L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 3*p+3;

PFlist6 := [];
PRlist6 := [];
PNlist6 := [];

// G30, 3r
w := PrimitiveRoot (p);

if p mod 3 eq 1 then add := [w^i: i in [0..2]];
else add := [1]; end if;
for r in add do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist6, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.5)>;
GPN := sub<GPR | phi(F.2), phi(F.3)>;
Append(~PRlist6, GPR);
Append(~PNlist6, GPN);
end for;

// G30, 5r
w := PrimitiveRoot (p);

if p mod 3 eq 1 then add := [w^i: i in [0..2]];
else add := [1]; end if;
for r in add do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist6, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.5)>;
GPN := sub<GPR | phi(F.2), phi(F.3)>;
Append(~PRlist6, GPR);
Append(~PNlist6, GPN);
end for;

return PFlist6, PRlist6, PNlist6;
end function;

Check31 := function(L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 3*p + 3 + 2*GCD(p-1,3);

PFlist7 := [];
PRlist7 := [];
PNlist7 := [];

// G31, 2

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist7, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.6)>;
GPN := sub<GPR | phi(F.2), phi(F.3)>;
Append(~PRlist7, GPR);
Append(~PNlist7, GPN);

// G31, 5r

for r in [1,nu] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist7, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.6)>;
GPN := sub<GPR | phi(F.2), phi(F.3)>;
Append(~PRlist7, GPR);
Append(~PNlist7, GPN);
end for;

// G31, 6

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist7, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.6)>;
GPN := sub<GPR | phi(F.2), phi(F.3)>;
Append(~PRlist7, GPR);
Append(~PNlist7, GPN);

return PFlist7, PRlist7, PNlist7;
end function;

Check32 := function(L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 3*p + 7 + 2*GCD(p-1,3);

PFlist8 := [];
PRlist8 := [];
PNlist8 := [];

// G32, 2

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist8, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.6)>;
GPN := sub<GPR | phi(F.2), phi(F.3)>;
Append(~PRlist8, GPR);
Append(~PNlist8, GPN);

// G32, 4r

for r in [1, nu] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist8, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.6)>;
GPN := sub<GPR | phi(F.2), phi(F.3)>;
Append(~PRlist8, GPR);
Append(~PNlist8, GPN);
end for;

return PFlist8, PRlist8, PNlist8;
end function;

Check33 := function(L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 3*p + 10 + 2*GCD(p-1,3);

PFlist9 := [];
PRlist9 := [];
PNlist9 := [];

// G33, 4r

for r in [1,nu] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist9, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.5)>;
GPN := sub<GPR | phi(F.2), phi(F.3)>;
Append(~PRlist9, GPR);
Append(~PNlist9, GPN);
end for;

return PFlist9, PRlist9, PNlist9;
end function;

Check34 := function(L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 3*p + 12 + 2*GCD(p-1,3);

PFlist10 := [];
PRlist10 := [];
PNlist10 := [];

// G34, 2r

for r in [1,nu] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist10, GPF);
GPR := sub<GPF | phi(F.4), phi(F.5)>;
GPN := sub<GPR | phi(F.5)>;
Append(~PRlist10, GPR);
Append(~PNlist10, GPN);
end for;

return PFlist10, PRlist10, PNlist10;
end function;

Check37 := function(L, p)

Z := Integers ();
    nu := Z ! (NonQuadraticResidue (p)); // nu

count := 3*p + 14 + 2*GCD(p-1,3);

PFlist11 := [];
PRlist11 := [];
PNlist11 := [];

// G37, 3r

for r in [1,nu] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist11, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.6)>;
GPN := sub<GPR | phi(F.2), phi(F.3)>;
Append(~PRlist11, GPR);
Append(~PNlist11, GPN);
end for;

// G37, 4r
w := PrimitiveRoot (p);

if p mod 4 eq 1 then add := [w^i: i in [0..3]];
else add := [1,nu]; end if;
for r in add do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist11, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.6)>;
GPN := sub<GPR | phi(F.2), phi(F.3)>;
Append(~PRlist11, GPR);
Append(~PNlist11, GPN);
end for;

return PFlist11, PRlist11, PNlist11;
end function;

Check39 := function(L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 3*p + 16 + 2*GCD(p-1,3) + GCD(p-1, 4);

PFlist12 := [];
PRlist12 := [];
PNlist12 := [];

// G39, 3r
w := PrimitiveRoot (p);

if p mod 3 eq 1 then add := [w^i: i in [0..5]];
else add := [1,nu]; end if;
for r in add do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist12, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.6)>;
GPN := sub<GPR | phi(F.2), phi(F.3)>;
Append(~PRlist12, GPR);
Append(~PNlist12, GPN);
end for;

// G39, 4r

for r in [1..(p-1)] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist12, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.6)>;
GPN := sub<GPR | phi(F.2), phi(F.3)>;
Append(~PRlist12, GPR);
Append(~PNlist12, GPN);
end for;

return PFlist12, PRlist12, PNlist12;
end function;

Check42 := function(L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 4*p + 15 + 2*GCD(p-1,3) + GCD(p-1, 4) + GCD(p-1,6);

PFlist13 := [];
PRlist13 := [];
PNlist13 := [];

// G42, 1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist13, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4)>;
GPN := sub<GPR | phi(F.2), phi(F.3)>;
Append(~PRlist13, GPR);
Append(~PNlist13, GPN);

// G42, 2

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist13, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4)>;
GPN := sub<GPR | phi(F.2), phi(F.3)>;
Append(~PRlist13, GPR);
Append(~PNlist13, GPN);

// G42, 3k

for k in [1..(p-1)] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist13, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4)>;
GPN := sub<GPR | phi(F.2), phi(F.3)>;
Append(~PRlist13, GPR);
Append(~PNlist13, GPN);
end for;

return PFlist13, PRlist13, PNlist13;
end function;

Check43 := function(L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 5*p + 16 + 2*GCD(p-1,3) + GCD(p-1, 4) + GCD(p-1,6);

PFlist14 := [];
PRlist14 := [];
PNlist14 := [];

// G43, 1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist14, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4)>;
GPN := sub<GPR | phi(F.2), phi(F.3)>;
Append(~PRlist14, GPR);
Append(~PNlist14, GPN);

// G43, 2k

for k in [1..(p-1)] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist14, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4)>;
GPN := sub<GPR | phi(F.2), phi(F.3)>;
Append(~PRlist14, GPR);
Append(~PNlist14, GPN);
end for;

return PFlist14, PRlist14, PNlist14;
end function;

for p in PrimesInInterval (5, 11) do 
   "\nprocess p = ", p;
   L := Table7(p);

   PFlist1, PRlist1, PNlist1 := Check25(L, p);
   PFlist2, PRlist2, PNlist2 := Check26(L, p);
   PFlist3, PRlist3, PNlist3 := Check27(L, p);
   PFlist4, PRlist4, PNlist4 := Check28(L, p);
   PFlist5, PRlist5, PNlist5 := Check29(L, p);
   PFlist6, PRlist6, PNlist6 := Check30(L, p);
   PFlist7, PRlist7, PNlist7 := Check31(L, p);
   PFlist8, PRlist8, PNlist8 := Check32(L, p);
   PFlist9, PRlist9, PNlist9 := Check33(L, p);
   PFlist10, PRlist10, PNlist10 := Check34(L, p);
   PFlist11, PRlist11, PNlist11 := Check37(L, p);
   PFlist12, PRlist12, PNlist12 := Check39(L, p);
   PFlist13, PRlist13, PNlist13 := Check42(L, p);
   PFlist14, PRlist14, PNlist14 := Check43(L, p);
   
   PFlist := PFlist1 cat PFlist2 cat PFlist3 cat PFlist4 cat
             PFlist5 cat PFlist6 cat PFlist7 cat PFlist8 cat PFlist9 cat
             PFlist10 cat PFlist11 cat PFlist12 cat PFlist13 cat PFlist14;
    
   PRlist := PRlist1 cat PRlist2 cat PRlist3 cat PRlist4 cat
             PRlist5 cat PRlist6 cat PRlist7 cat PRlist8 cat PRlist9 cat
             PRlist10 cat  PRlist11 cat PRlist12 cat  PRlist13 cat PRlist14;    

   PNlist := PNlist1 cat PNlist2 cat PNlist3 cat PNlist4 cat
             PNlist5 cat PNlist6 cat PNlist7 cat PNlist8 cat PNlist9 cat
             PNlist10 cat  PNlist11 cat PNlist12 cat  PNlist13 cat PNlist14;
    
   for i in [1..#L] do
      PF := PFlist[i];
      PR := PRlist[i];
      PN := PNlist[i];
      Int := Core(PF, PN);
      assert #Int eq 1;
      phiN := CosetAction (PF, PN);
      J := Image (phiN);
      // assert IsIsomorphic (J, PF);
      assert #J eq #PF;
      assert Degree (J) eq p^4;

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

   end for;
end for;

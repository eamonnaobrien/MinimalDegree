load "../setup-permrep.m";

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

//Phi20 with center Cp X Cp

My20 := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a3, a4, a5, a6];
Beta := [a1, a2];

// common relations, typically commutators
Comms := [
(a3, a4) = 1, (a3, a5)= a1, (a3, a6) = a2,
(a4, a5) = 1, (a4, a6)= a1^(-1), (a5, a6)= a3,  
(a1, a2) = 1, a1^p = 1, a2^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..4]]: i in [1..2]]);

L := [];

// G20, 1

G := quo <F | Comms, a3^p = a4^p = a5^p = a6^p = 1>;
Append (~L, G);

// G20, 2r

for r in [1,nu] do
G := quo <F | Comms, a3^p = a4^p = a5^p = 1,
a6^p = a1^r>;
Append (~L, G);
end for;

// G20, 3

G := quo <F | Comms, a3^p = a4^p = a5^p = 1,
a6^p = a2>;
Append (~L, G);

// G20, 4

G := quo <F | Comms, a3^p = a4^p = a6^p = 1,
a5^p = a1>;
Append (~L, G);

// G20, 5r

for r in [1,nu] do
G := quo <F | Comms, a3^p = a4^p = a6^p = 1,
a5^p = a2^r>;
Append (~L, G);
end for;

// G20, 6r

for r in [1,nu] do
G := quo <F | Comms, a3^p = a4^p = a6^p = 1,
a5^p = a1*a2^r>;
Append (~L, G);
end for;

// G20, 7

G := quo <F | Comms, a3^p = a5^p = a6^p = 1,
a4^p = a1>;
Append (~L, G);

// G20, 8

G := quo <F | Comms, a3^p = a5^p = a6^p = 1,
a4^p = a2>;
Append (~L, G);

// G20, 9

G := quo <F | Comms, a3^p = a4^p = 1,
a5^p = a1, a6^p = a2>;
Append (~L, G);

// G20, 10r

for r in [1,nu] do
G := quo <F | Comms, a3^p = a4^p = 1,
a5^p = a1, a6^p = a2*a1^r>;
Append (~L, G);
end for;

// G20, 11r

for r in [2..(p-1)] do
G := quo <F | Comms, a3^p = a4^p = 1,
a5^p = a1, a6^p = a2^r>;
Append (~L, G);
end for;

// G20, 12rs

for r in [1,nu] do
for s in [1,nu] do
G := quo <F | Comms, a3^p = a4^p = 1,
a5^p = a2^r, a6^p = a1^s>;
Append (~L, G);
end for;
end for;

// G20, 13rs

for r in [1,nu] do
for s in [1..(p-1)] do
G := quo <F | Comms, a3^p = a4^p = 1,
a5^p = a2^r, a6^p = a2*a1^s>;
Append (~L, G);
end for;
end for;

// G20, 15r
w := PrimitiveRoot (p);

if p mod 4 eq 1 then add := [w^i: i in [0..3]];
else add := [1,nu]; end if;
for r in add do
G := quo <F | Comms, a3^p = a5^p = 1,
a4^p = a2, a6^p = a1^r>;
Append (~L, G);
end for;

// G20, 16r

for r in [1..(p-1)] do
G := quo <F | Comms, a3^p = a6^p = 1,
a4^p = a1, a5^p = a2^r>;
Append (~L, G);
end for;

// G20, 17r
w := PrimitiveRoot (p);

if p mod 3 eq 1 then add := [w^i: i in [0..2]];
else add := [1]; end if;
for r in add do
G := quo <F | Comms, a3^p = a6^p = 1,
a4^p = a2, a5^p = a1^r>;
Append (~L, G);
end for;

// G20, 18r

for r in [1..(p-1)] do
G := quo <F | Comms, a3^p = a6^p = 1,
a4^p = a2^r*a1, a5^p = a1>;
Append (~L, G);
end for;

return L;
end function;

Check20 := function(L, p)

w := PrimitiveRoot(p);

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 0;

PFlist := []; // lists the group G
PRlist := []; // lists the subgroup R
PNlist := []; // lists kernel of non-linear irr char. from R
PSlist := []; // lists the subgroup R
PMlist := []; // lists kernel of non-linear irr char. from S
MinDeg := []; //Mu(G) from table

// G20, 1

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2), phi(F.5)>;
GPN := sub<GPR | phi(F.1), phi(F.3), phi(F.4), phi(F.5)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2)>;
GPM := sub<GPS  | phi(F.3), phi(F.4), phi(F.2)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, p^3 + p^2);

// G20, 2r

for r in [1,nu] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2), phi(F.5)>;
GPN := sub<GPR | phi(F.1), phi(F.3), phi(F.4), phi(F.5)>;
GPS := sub<GPF | phi(F.6^p), phi(F.3), phi(F.4), phi(F.2)>;
GPM := sub<GPS  | phi(F.3), phi(F.4), phi(F.2)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, p^3 + p^2);
end for;

// G20, 3

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.6^p), phi(F.5)>;
GPN := sub<GPR | phi(F.1), phi(F.3), phi(F.4), phi(F.5)>;
GPS := sub<GPF | phi(F.6^p), phi(F.3), phi(F.4), phi(F.1)>;
GPM := sub<GPS  | phi(F.3), phi(F.4), phi(F.6^p)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, p^3 + p^2);

// G20, 4

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4), phi(F.5)>;
GPN := sub<GPR | phi(F.1), phi(F.3), phi(F.4), phi(F.5)>;
GPS := sub<GPF | phi(F.2), phi(F.3), phi(F.4), phi(F.1)>;
GPM := sub<GPS  | phi(F.3), phi(F.4), phi(F.2)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, p^3 + p^2);

// G20, 5r

for r in [1,nu] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.5)>;
GPN := sub<GPR | phi(F.1), phi(F.3), phi(F.4)>;
GPS := sub<GPF | phi(F.5), phi(F.4), phi(F.1)>;
GPM := sub<GPS  | phi(F.5), phi(F.4)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, 2*p^3);
end for;

// G20, 6r

for r in [1,nu] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.5)>;
GPN := sub<GPR | phi(F.1), phi(F.3), phi(F.4)>;
GPS := sub<GPF | phi(F.2), phi(F.3), phi(F.4), phi(F.1)>;
GPM := sub<GPS  | phi(F.2), phi(F.3), phi(F.4)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, 2*p^3);
end for;

// G20, 7

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4), phi(F.5)>;
GPN := sub<GPR | phi(F.1), phi(F.3), phi(F.4), phi(F.5)>;
GPS := sub<GPF | phi(F.2), phi(F.3), phi(F.4^p), phi(F.6)>;
GPM := sub<GPS  | phi(F.2), phi(F.3), phi(F.6)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, p^3 + p^2);

// G20, 8

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.2), phi(F.3), phi(F.4), phi(F.5)>;
GPN := sub<GPR | phi(F.1), phi(F.3), phi(F.5)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.4)>;
GPM := sub<GPS  | phi(F.4), phi(F.3)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, 2*p^3);

// G20, 9

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.6^p), phi(F.3), phi(F.4), phi(F.5)>;
GPN := sub<GPR | phi(F.1), phi(F.3), phi(F.4), phi(F.5)>;
GPS := sub<GPF | phi(F.5^p), phi(F.3), phi(F.4), phi(F.6^p)>;
GPM := sub<GPS  | phi(F.4), phi(F.3), phi(F.6^p)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, p^3 + p^2);

// G20, 10r

for r in [1,nu] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.6^p), phi(F.3), phi(F.4), phi(F.5)>;
GPN := sub<GPR | phi(F.1), phi(F.3), phi(F.4), phi(F.5)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2)>;
GPM := sub<GPS  | phi(F.4), phi(F.3), phi(F.2)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, p^3 + p^2);
end for;

// G20, 11r

for r in [2..(p-1)] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.6^p), phi(F.3), phi(F.4), phi(F.5)>;
GPN := sub<GPR | phi(F.1), phi(F.3), phi(F.4), phi(F.5)>;
GPS := sub<GPF | phi(F.5^p), phi(F.3), phi(F.4), phi(F.6^p)>;
GPM := sub<GPS  | phi(F.4), phi(F.3), phi(F.6^p)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, p^3 + p^2);
end for;

// G20, 12rs

for r in [1,nu] do
for s in [1,nu] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.6^p), phi(F.3), phi(F.4), phi(F.5)>;
GPN := sub<GPR | phi(F.1), phi(F.3), phi(F.4)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2)>;
GPM := sub<GPS  | phi(F.4), phi(F.3), phi(F.2)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, 2*p^3);
end for;
end for;

// G20, 13rs

for r in [1,nu] do
for s in [1..(p-1)] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.5)>;
GPN := sub<GPR | phi(F.1), phi(F.3), phi(F.4)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2)>;
GPM := sub<GPS  | phi(F.4), phi(F.3), phi(F.2)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, 2*p^3);
end for;
end for;

// G20, 15r
w := PrimitiveRoot (p);

if p mod 4 eq 1 then add := [w^i: i in [0..3]];
else add := [1,nu]; end if;
for r in add do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.6^p), phi(F.3), phi(F.4), phi(F.5)>;
GPN := sub<GPR | phi(F.1), phi(F.3), phi(F.5)>;
GPS := sub<GPF | phi(F.6^p), phi(F.3), phi(F.4)>;
GPM := sub<GPS  | phi(F.4), phi(F.3)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, 2*p^3);
end for;

// G20, 16r

for r in [1..(p-1)] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.3), phi(F.4), phi(F.5)>;
GPN := sub<GPR | phi(F.1), phi(F.3), phi(F.4)>;
GPS := sub<GPF | phi(F.6), phi(F.3), phi(F.4^p), phi(F.5^p)>;
GPM := sub<GPS  | phi(F.2), phi(F.3), phi(F.6)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, 2*p^3);
end for;

// G20, 17r
w := PrimitiveRoot (p);

if p mod 3 eq 1 then add := [w^i: i in [0..2]];
else add := [1]; end if;
for r in add do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.3), phi(F.4), phi(F.5)>;
GPN := sub<GPR | phi(F.1), phi(F.3), phi(F.5)>;
GPS := sub<GPF | phi(F.5^p), phi(F.3), phi(F.4)>;
GPM := sub<GPS  | phi(F.4), phi(F.3)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, 2*p^3);
end for;

// G20, 18r

for r in [1..(p-1)] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.3), phi(F.4), phi(F.5)>;
GPN := sub<GPR | phi(F.1), phi(F.3), phi(F.5)>;
GPS := sub<GPF | phi(F.3), phi(F.4), phi(F.5^p)>;
GPM := sub<GPS  | phi(F.4), phi(F.3)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, 2*p^3);
end for;

return PFlist, PRlist, PNlist, PSlist, PMlist, MinDeg;
end function;

MAX := 5^6;

for p in PrimesInInterval (5, 11) do 
   "\nprocess p = ", p;
   L := My20(p);
   "#L is ", #L;
   PFlist, PRlist, PNlist, PSlist, PMlist, MinDeg := Check20(L, p);

   for i in [1..#L] do
      PF := PFlist[i];
      PR := PRlist[i];
      PN := PNlist[i];
      PS := PSlist[i];
      PM := PMlist[i];
      Mu_value := MinDeg[i];
      Int := Core(PF, PN) meet Core(PF, PM);
      assert #Int eq 1;
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

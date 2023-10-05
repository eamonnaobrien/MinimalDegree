load "../setup-permrep.m";

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

My3B := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, b1, b2> := FreeGroup (6);
Alpha := [a1, a2, a3, a4];
Beta := [b1, b2];

// common relations, typically commutators
Comms := [
(a2, a3) = 1, (a2, a4)= a1, (a3, a4) = a2, a1 = b1^p,
(b1, b2) = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..4]]: i in [1..2]]);

L := [];

// G3, 10r

for r in [1,nu] do
G := quo <F | Comms, a2^p =  b1^(p^2) = b2^p = 1,
a3^p = b1^r, a4^p = b2>;
Append (~L, G);
end for;

return L;
end function;

My3C := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, b1, b2> := FreeGroup (6);
Alpha := [a1, a2, a3, a4];
Beta := [b1, b2];

// common relations, typically commutators
Comms := [
(a2, a3) = 1, (a2, a4)= a1, (a3, a4) = a2, a1 = b2,
(b1, b2) = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..4]]: i in [1..2]]);

L := [];

// G3, 16r

for r in [1,nu] do
G := quo <F | Comms, a2^p =  b1^(p^2) = b2^p = 1,
a3^p = b2^r, a4^p = b1>;
Append (~L, G);
end for;

return L;
end function;

My4A := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, b1, b2> := FreeGroup (7);
Alpha := [a1, a2, a3, a4, a5];
Beta := [b1, b2];

// common relations, typically commutators
Comms := [
(a2, a3) = 1, (a2, a4)= 1, (a3, a4) = 1,
(a4, a5) = a2, (a3, a5) = a1, (a2, a5) = 1, a1 = b1^p,
a2 = b2, (b1, b2) = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..5]]: i in [1..2]]);

L := [];

// G4, 3

G := quo <F | Comms,  a4^p = a5^p = b1^(p^2) = b2^p = 1,
a3^p = b2>;
Append (~L, G);

// G4, 4

G := quo <F | Comms,  a3^p = a5^p = b1^(p^2) = b2^p = 1,
a4^p = b1>;
Append (~L, G);

// G4, 7

G := quo <F | Comms,  a3^p = a4^p = b1^(p^2) = b2^p = 1,
a5^p = b2>;
Append (~L, G);

// G4, 9r

for r in [1,nu] do
G := quo <F | Comms,   a5^p = b1^(p^2) = b2^p = 1,
a3^p = b2^r, a4^p = b1>;
Append (~L, G);
end for;

// G4, 11

G := quo <F | Comms,   a4^p = b1^(p^2) = b2^p = 1,
a3^p = b2, a5^p = b1>;
Append (~L, G);

// G4, 12

G := quo <F | Comms,   a3^p = b1^(p^2) = b2^p = 1,
a4^p = b1, a5^p = b2>;
Append (~L, G);

return L;
end function;

My6A := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, b1, b2> := FreeGroup (7);
Alpha := [a1, a2, a3, a4, a5];
Beta := [b1, b2];

// common relations, typically commutators
Comms := [
(a2, a3) = 1, (a2, a4)= 1, (a3, a4) = a1,
(a4, a5) = a3, (a3, a5) = a2, (a2, a5) = 1, a1 = b1^p,
a2 = b2, (b1, b2) = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..5]]: i in [1..2]]);

L := [];

// G6, 1

G := quo <F | Comms, a3^p = a4^p = a5^p = b1^(p^2) = b2^p = 1>;
Append (~L, G);

// G6, 2r

for r in [1,nu] do
G := quo <F | Comms, a3^p = a4^p =  b1^(p^2) = b2^p = 1,
a5^p = b1^r>;
Append (~L, G);
end for;

// G6, 5r

for r in [1,nu] do
G := quo <F | Comms, a3^p = a5^p =  b1^(p^2) = b2^p = 1,
a4^p = b2^r>;
Append (~L, G);
end for;

// G6, 6rs

for r in [1,nu] do
for s in [1,nu] do
G := quo <F | Comms, a3^p =  b1^(p^2) = b2^p = 1,
a4^p = b2^r, a5^p = b1^s>;
Append (~L, G);
end for;
end for;

return L;
end function;

Table5Phi3to6 := function(p)
   return My3B(p) cat My3C(p) cat My4A(p) cat My6A(p);
end function;

CheckPhi3to6 := function(L, p)

w := PrimitiveRoot(p);

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 0;

PFlist := []; // lists the group G
PRlist := []; // lists the subgroup R
PNlist := []; // lists kernel of non-linear irr char. from R
PSlist := []; // lists the subgroup R
PMlist := []; // lists kernel of non-linear irr char. from S
MinDeg := []; // Mu(G) from Table 5

// 3, 10r

for r in [1,nu] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.3), phi(F.4^p), phi(F.2)>;
GPN := sub<GPR | phi(F.4^p), phi(F.2)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2), phi(F.5), phi(F.6)>;
GPM := sub<GPS | phi(F.3), phi(F.1), phi(F.2)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, p^4 + p^2);
end for;

// 3, 16r

for r in [1,nu] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.3), phi(F.4^p), phi(F.2)>;
GPN := sub<GPR | phi(F.4^p), phi(F.2)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2), phi(F.5), phi(F.6)>;
GPM := sub<GPS | phi(F.3), phi(F.1), phi(F.2)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, 2*p^3);
end for;

// 4, 3

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.3), phi(F.4), phi(F.6)>;
GPN := sub<GPR | phi(F.4), phi(F.6)>;
GPS := sub<GPF | phi(F.3), phi(F.4), phi(F.6)>;
GPM := sub<GPS | phi(F.3), phi(F.4)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, 2*p^3);

// 4, 4

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.3), phi(F.4), phi(F.2)>;
GPN := sub<GPR | phi(F.2), phi(F.3)>;
GPS := sub<GPF | phi(F.3), phi(F.4), phi(F.2)>;
GPM := sub<GPS | phi(F.3), phi(F.4)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, p^4 + p^2);

// 4, 7

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.3), phi(F.4), phi(F.5^p), phi(F.6)>;
GPN := sub<GPR | phi(F.3), phi(F.4), phi(F.6)>;
GPS := sub<GPF | phi(F.3), phi(F.4), phi(F.5^p), phi(F.6)>;
GPM := sub<GPS | phi(F.3), phi(F.4), phi(F.5^p)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, p^3 + p^2);

// 4, 9r

for r in [1,nu] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.3), phi(F.4)>;
GPN := sub<GPR | phi(F.4)>;
GPS := sub<GPF | phi(F.3), phi(F.4)>;
GPM := sub<GPS | phi(F.3)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, p^4 + p^3 );
end for;

// 4, 11

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.3), phi(F.4), phi(F.5^p)>;
GPN := sub<GPR | phi(F.3), phi(F.4)>;
GPS := sub<GPF | phi(F.3), phi(F.4), phi(F.5^p)>;
GPM := sub<GPS | phi(F.4), phi(F.5^p)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, 2*p^3 );

// 4, 12

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.3), phi(F.4), phi(F.5^p)>;
GPN := sub<GPR | phi(F.3), phi(F.4)>;
GPS := sub<GPF | phi(F.3), phi(F.4), phi(F.5^p)>;
GPM := sub<GPS | phi(F.3), phi(F.5^p)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, p^4 + p^2 );

// 6, 1

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4), phi(F.6)>;
GPN := sub<GPR | phi(F.1), phi(F.3), phi(F.4), phi(F.6)>;
GPS := sub<GPF | phi(F.2), phi(F.3), phi(F.5), phi(F.6)>;
GPM := sub<GPS | phi(F.2), phi(F.3), phi(F.5)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, p^3 + p^2 );

// 6, 2r

for r in [1,nu] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.5)>;
GPN := sub<GPR | phi(F.2), phi(F.3)>;
GPS := sub<GPF | phi(F.2), phi(F.3), phi(F.5^p), phi(F.4)>;
GPM := sub<GPS | phi(F.1), phi(F.3), phi(F.5^p), phi(F.4)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, p^4 + p^2 );
end for;

// 6, 5r

for r in [1,nu] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.4), phi(F.3), phi(F.5^p), phi(F.6)>;
GPN := sub<GPR | phi(F.1), phi(F.3), phi(F.6)>;
GPS := sub<GPF | phi(F.6), phi(F.3), phi(F.5)>;
GPM := sub<GPS | phi(F.2), phi(F.3), phi(F.5)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, 2*p^3);
end for;

// 6, 6rs

for r in [1,nu] do
for s in [1,nu] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.4), phi(F.3), phi(F.5^p)>;
GPN := sub<GPR | phi(F.1), phi(F.3), phi(F.5^p)>;
GPS := sub<GPF | phi(F.4^p), phi(F.3), phi(F.5)>;
GPM := sub<GPS | phi(F.2), phi(F.3)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, p^4 + p^3);
end for;
end for;

return PFlist, PRlist, PNlist, PSlist, PMlist, MinDeg;
end function;

MAX := 7^6;

for p in PrimesInInterval (5, 11) do 
   "\nprocess p = ", p;
   L := Table5Phi3to6(p);

   PFlist, PRlist, PNlist, PSlist, PMlist, MinDeg := CheckPhi3to6(L, p);

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

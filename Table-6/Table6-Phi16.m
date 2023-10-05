load "../setup-permrep.m";

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

My16 := function(p)
Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a3, a4, a5, a6];
Beta := [a1, a2];

// common relations, typically commutators
Comms := [
(a3, a4) = 1, (a3, a5)= 1, (a3, a6) = a1,
(a4, a5) = 1, (a4, a6)= a2, (a5, a6)= a3,  
(a1, a2) = 1, a1^p = 1, a2^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..4]]: i in [1..2]]);

L := [];

// G16, 5

G := quo <F | Comms, a3^p = a4^p = a6^p = 1,
a5^p = a2>;
Append (~L, G);

// G16, 8r

for r in [1,nu] do
G := quo <F | Comms, a3^p = a4^p = 1,
a5^p = a1^r, a6^p = a2>;
Append (~L, G);
end for;

// G16, 9

G := quo <F | Comms, a3^p = a4^p = 1,
a5^p = a2, a6^p = a1>;
Append (~L, G);

// G16, 10

G := quo <F | Comms, a3^p = a5^p = 1,
a4^p = a1, a6^p = a2>;
Append (~L, G);

// G16, 12r
w := PrimitiveRoot (p);

if p mod 3 eq 1 then add := [w^i: i in [0..2]];
else add := [1]; end if;
for r in add do
G := quo <F | Comms, a3^p = a6^p = 1,
a4^p = a1^r, a5^p = a2>;
Append (~L, G);
end for;

return L;
end function;


Check16 := function(L, p)
Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 0;

PFlist := []; // lists the group G
PRlist := []; // lists the subgroup R
PNlist := []; // lists kernel of 1st non-linear irr char.
PMlist := []; // lists kernel of 2nd non-linear irr char.
MinDeg := []; //Mu(G) from table

// G16, 5

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.5)>;
GPN := sub<GPR | phi(F.1), phi(F.3), phi(F.4)>;
GPM := sub<GPF | phi(F.3), phi(F.4), phi(F.5)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PMlist, GPM);
Append(~MinDeg, p^3 + p^2);

// G16, 8r

for r in [1, nu] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.6^p), phi(F.3), phi(F.4), phi(F.5)>;
GPN := sub<GPR | phi(F.5), phi(F.3), phi(F.4)>;
GPM := sub<GPF | phi(F.3), phi(F.4), phi(F.6^p)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PMlist, GPM);
Append(~MinDeg, p^3 + p^2);
end for;

// G16, 9

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.6^p), phi(F.3), phi(F.4), phi(F.5)>;
GPN := sub<GPR | phi(F.5), phi(F.3), phi(F.4)>;
GPM := sub<GPF | phi(F.3), phi(F.4), phi(F.6^p)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PMlist, GPM);
Append(~MinDeg, p^3 + p^2);

// G16, 10

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.6^p), phi(F.3), phi(F.4), phi(F.5)>;
GPN := sub<GPR | phi(F.5), phi(F.3), phi(F.4)>;
GPM := sub<GPF | phi(F.3), phi(F.5), phi(F.6^p)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PMlist, GPM);
Append(~MinDeg, p^3 + p^2);

// G16, 12r
w := PrimitiveRoot (p);

if p mod 3 eq 1 then add := [w^i: i in [0..2]];
else add := [1]; end if;
for r in add do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.3), phi(F.4), phi(F.5)>;
GPN := sub<GPR | phi(F.5), phi(F.3)>;
GPM := sub<GPF | phi(F.3), phi(F.4)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PMlist, GPM);
Append(~MinDeg, 2*p^3);
end for;

return PFlist, PRlist, PNlist, PMlist, MinDeg;
end function;

MAX := 11^6;
for p in PrimesInInterval (5, 11) do 
   "\nprocess p = ", p;
   L := My16(p);
   PFlist, PRlist, PNlist, PMlist, MinDeg := Check16(L, p);

   for i in [1..#L] do
      PF := PFlist[i];
      PR := PRlist[i];
      PN := PNlist[i];
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

      QPRM, h := quo<PR | PM>;
      linQPM := LinearCharacters (QPRM);
      for j in [1..#linQPM] do
         if IsFaithful(linQPM[j]) eq true then
            lambda := linQPM[j];
            break;
         end if;
      end for;
      lambda_bar := LiftCharacter(lambda, h, PR);
      eta := Induction(lambda_bar, PF);
      assert IsIrreducible(eta);

   end for;
end for;

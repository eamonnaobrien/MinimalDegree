load "../setup-permrep.m";

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

//Phi12 with center Cp X Cp

My12 := function(p)

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a3, a4, a5, a6];
Beta := [a1, a2];

// common relations, typically commutators
Comms := [
(a3, a4) = a1, (a3, a5)= 1, (a3, a6) = 1,
(a4, a5) = 1, (a4, a6)= 1, (a5, a6)= a2,  
(a1, a2) = 1, a1^p = 1, a2^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..4]]: i in [1..2]]);

L := [];

// G12, 6

G := quo <F | Comms, a3^p = a6^p = 1,
a4^p = a1*a2, a5^p = a1*a2>;
Append (~L, G);

// G12, 9

G := quo <F | Comms,  a4^p = a6^p = 1,
a3^p = a2, a5^p = a1>;
Append (~L, G);

// G12, 10

G := quo <F | Comms,  a4^p = a6^p = 1,
a3^p = a1*a2, a5^p = a1>;
Append (~L, G);

// G12, 12r

for r in [2..(p-1)] do
G := quo <F | Comms,  a4^p = a6^p = 1,
a3^p = a1*a2, a5^p = a1^(r)*a2>;
Append (~L, G);
end for;

// G12, 13

G := quo <F | Comms,  a4^p = a2, a6^p = 1,
a3^p = a1, a5^p = a1>;
Append (~L, G);

// G12, 14

G := quo <F | Comms,  a4^p = a1, a6^p = 1,
a3^p = a2, a5^p = a2>;
Append (~L, G);

// G12, 15

G := quo <F | Comms,  a4^p = a1, a6^p = 1,
a3^p = a1*a2, a5^p = a1*a2>;
Append (~L, G);

// G12, 16

G := quo <F | Comms,  a4^p = a2, a6^p = a2,
a3^p = a1, a5^p = a1>;
Append (~L, G);

return L;
end function;

Check12 := function(L, p)
Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 0;

PFlist1 := []; // lists the group G
PRlist1 := []; // lists the subgroup R
PNlist1 := []; // lists kernel of non-linear irr char from R
PSlist1 := []; // lists the subgroup S
PMlist1 := []; // lists kernel of non-linear irr char from S
Mu1 := [];     // Mu(G) from Table 6 

// G12, 6

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.2), phi(F.5), phi(F.3), phi(F.6)>;
GPN := sub<GPR | phi(F.3), phi(F.6), phi(F.2)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.6)>;
GPM := sub<GPS  | phi(F.3), phi(F.6), phi(F.1)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, 2*p^3);

// G12, 9

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.3), phi(F.5), phi(F.4)>;
GPN := sub<GPR | phi(F.4), phi(F.5), phi(F.1)>;
GPS := sub<GPF | phi(F.5), phi(F.3), phi(F.6)>;
GPM := sub<GPS | phi(F.3), phi(F.6), phi(F.2)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, 2*p^3);

// G12, 10

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.4), phi(F.3), phi(F.5)>;
GPN := sub<GPR | phi(F.4), phi(F.5), phi(F.1)>;
GPS := sub<GPF | phi(F.3), phi(F.5^p), phi(F.6)>;
GPM := sub<GPS | phi(F.3), phi(F.6)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, 2*p^3);

// G12, 12r

for r in [2..(p-1)] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.2), phi(F.4), phi(F.1), phi(F.3), phi(F.6)>;
GPN := sub<GPR | phi(F.4), phi(F.6), phi(F.1)>;
GPS := sub<GPF | phi(F.2), phi(F.1), phi(F.4), phi(F.5), phi(F.6)>;
GPM := sub<GPS | phi(F.4), phi(F.6), phi(F.2)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, 2*p^3);
end for;

// G12, 13

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.6), phi(F.5), phi(F.4)>;
GPN := sub<GPR | phi(F.4), phi(F.6), phi(F.2)>;
GPS := sub<GPF | phi(F.3), phi(F.4), phi(F.6)>;
GPM := sub<GPS | phi(F.3), phi(F.6), phi(F.1)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, 2*p^3);

// G12, 14

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.3), phi(F.5), phi(F.4^p), phi(F.6)>;
GPN := sub<GPR | phi(F.3), phi(F.5), phi(F.6), phi(F.2)>;
GPS := sub<GPF | phi(F.3), phi(F.4), phi(F.6)>;
GPM := sub<GPS | phi(F.4), phi(F.6), phi(F.1)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, p^3 + p^2);

// G12, 15

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.6)>;
GPN := sub<GPR | phi(F.3), phi(F.6)>;
GPS := sub<GPF | phi(F.3), phi(F.4), phi(F.6)>;
GPM := sub<GPS | phi(F.4), phi(F.6), phi(F.1)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, 2*p^3);

// G12, 16

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.3), phi(F.4), phi(F.5)>;
GPN := sub<GPR | phi(F.3), phi(F.5), phi(F.1)>;
GPS := sub<GPF | phi(F.4), phi(F.5), phi(F.6)>;
GPM := sub<GPS | phi(F.4), phi(F.6), phi(F.2)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PSlist1, GPS);
Append(~PMlist1, GPM);
Append(~Mu1, 2*p^3);

return PFlist1, PRlist1, PNlist1, PSlist1, PMlist1, Mu1;
end function;

MAX := 5^6;
for p in PrimesInInterval (5, 11) do 
   "\nprocess p = ", p;
   L := My12(p);
   PFlist1, PRlist1, PNlist1, PSlist1, PMlist1, Mu1 := Check12(L, p);
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

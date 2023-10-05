load "../setup-permrep.m";

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

//Phi13 with center Cp X Cp

My13 := function(p)

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

Z := Integers ();
    nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
Alpha := [a3, a4, a5, a6];
Beta := [a1, a2];

// common relations, typically commutators
Comms := [
(a3, a4) = 1, (a3, a5)= a1, (a3, a6) = a2,
(a4, a5) = a2, (a4, a6)= 1, (a5, a6)= 1,  
(a1, a2) = 1, a1^p = 1, a2^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..4]]: i in [1..2]]);

L := [];

// G13, 1

G := quo <F | Comms, a3^p = a4^p = a5^p = a6^p = 1>;
Append (~L, G);

// G13, 2

G := quo <F | Comms, a4^p = a5^p = a6^p = 1,
 a3^p = a2>;
Append (~L, G);

// G13, 3

G := quo <F | Comms, a4^p = a5^p = a6^p = 1,
 a3^p = a1>;
Append (~L, G);


// G13, 5

G := quo <F | Comms, a3^p = a5^p = a6^p = 1,
 a4^p = a1>;
Append (~L, G);

// G13, 6

G := quo <F | Comms, a4^p =  a6^p = 1,
 a3^p = a1, a5^p = a2>;
Append (~L, G);

// G13, 7r

for r in [1..(p-1)] do
G := quo <F | Comms, a5^p =  a6^p = 1,
 a3^p = a1^r, a4^p = a2>;
Append (~L, G);
end for;

// G13, 8r

for r in [1,nu] do
G := quo <F | Comms, a5^p =  a6^p = 1,
 a3^p = a2, a4^p = a1^r>;
Append (~L, G);
end for;

// G13, 9

G := quo <F | Comms, a4^p =  a5^p = 1,
 a3^p = a1, a6^p = a2>;
Append (~L, G);

// G13, 10

G := quo <F | Comms, a4^p =  a5^p = 1,
 a3^p = a2, a6^p = a1>;
Append (~L, G);

// G13, 11

G := quo <F | Comms, a3^p =  a5^p = 1,
 a4^p = a1, a6^p = a2>;
Append (~L, G);

return L;
end function;


Check13 := function(L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 0;

PFlist2 := []; // lists the group G
PRlist2 := []; // lists the subgroup R
PNlist2 := []; // lists kernel of non-linear irr char from R
PSlist2 := []; // lists the subgroup S
PMlist2 := []; // lists kernel of non-linear irr char from S
Mu2 := []; //Mu(G) from table

// G13, 1

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist2, GPF);
GPR := sub<GPF | phi(F.1), phi(F.2), phi(F.3), phi(F.4), phi(F.6)>;
GPN := sub<GPR | phi(F.2), phi(F.3), phi(F.4), phi(F.6)>;
GPS := sub<GPF | phi(F.1), phi(F.2), phi(F.3), phi(F.4)>;
GPM := sub<GPS  | phi(F.1), phi(F.4), phi(F.3)>;
Append(~PRlist2, GPR);
Append(~PNlist2, GPN);
Append(~PSlist2, GPS);
Append(~PMlist2, GPM);
Append(~Mu2, p^3 + p^2);

// G13, 2

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist2, GPF);
GPR := sub<GPF | phi(F.1), phi(F.2), phi(F.3), phi(F.4), phi(F.6)>;
GPN := sub<GPR | phi(F.2), phi(F.3), phi(F.4), phi(F.6)>;
GPS := sub<GPF | phi(F.1), phi(F.2), phi(F.6), phi(F.4)>;
GPM := sub<GPS  | phi(F.1), phi(F.4), phi(F.6)>;
Append(~PRlist2, GPR);
Append(~PNlist2, GPN);
Append(~PSlist2, GPS);
Append(~PMlist2, GPM);
Append(~Mu2, p^3 + p^2);

// G13, 3

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist2, GPF);
GPR := sub<GPF | phi(F.1), phi(F.2), phi(F.5), phi(F.4), phi(F.6)>;
GPN := sub<GPR | phi(F.2), phi(F.5), phi(F.4), phi(F.6)>;
GPS := sub<GPF | phi(F.2), phi(F.3), phi(F.4)>;
GPM := sub<GPS  | phi(F.3), phi(F.4)>;
Append(~PRlist2, GPR);
Append(~PNlist2, GPN);
Append(~PSlist2, GPS);
Append(~PMlist2, GPM);
Append(~Mu2, p^3 + p^2);

// G13, 5

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist2, GPF);
GPR := sub<GPF |  phi(F.2), phi(F.3), phi(F.4), phi(F.6)>;
GPN := sub<GPR | phi(F.3), phi(F.2), phi(F.6)>;
GPS := sub<GPF | phi(F.2), phi(F.6), phi(F.4)>;
GPM := sub<GPS  | phi(F.6), phi(F.4)>;
Append(~PRlist2, GPR);
Append(~PNlist2, GPN);
Append(~PSlist2, GPS);
Append(~PMlist2, GPM);
Append(~Mu2, 2*p^3);

// G13, 6

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist2, GPF);
GPR := sub<GPF |  phi(F.1), phi(F.5), phi(F.4), phi(F.6)>;
GPN := sub<GPR | phi(F.4), phi(F.5), phi(F.2), phi(F.6)>;
GPS := sub<GPF | phi(F.2), phi(F.3), phi(F.4)>;
GPM := sub<GPS  | phi(F.3), phi(F.4)>;
Append(~PRlist2, GPR);
Append(~PNlist2, GPN);
Append(~PSlist2, GPS);
Append(~PMlist2, GPM);
Append(~Mu2, p^3 + p^2);

// G13, 7r

for r in [1..(p-1)] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist2, GPF);
GPR := sub<GPF |  phi(F.5), phi(F.3^p), phi(F.4), phi(F.6)>;
GPN := sub<GPR | phi(F.2), phi(F.4), phi(F.5), phi(F.6)>;
GPS := sub<GPF | phi(F.3^p), phi(F.5), phi(F.6), phi(F.4^p)>;
GPM := sub<GPS  | phi(F.3^p), phi(F.5), phi(F.6)>;
Append(~PRlist2, GPR);
Append(~PNlist2, GPN);
Append(~PSlist2, GPS);
Append(~PMlist2, GPM);
Append(~Mu2, p^3 + p^2);
end for;

// G13, 8r

for r in [1,nu] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist2, GPF);
GPR := sub<GPF |  phi(F.3), phi(F.4), phi(F.6)>;
GPN := sub<GPR | phi(F.3), phi(F.2), phi(F.6)>;
GPS := sub<GPF | phi(F.5), phi(F.3^p), phi(F.4^p), phi(F.6)>;
GPM := sub<GPS  | phi(F.5), phi(F.4^p), phi(F.6)>;
Append(~PRlist2, GPR);
Append(~PNlist2, GPN);
Append(~PSlist2, GPS);
Append(~PMlist2, GPM);
Append(~Mu2, 2*p^3);
end for;

// G13, 9

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist2, GPF);
GPR := sub<GPF |  phi(F.1), phi(F.2), phi(F.5), phi(F.4), phi(F.6)>;
GPN := sub<GPR | phi(F.4), phi(F.5), phi(F.2), phi(F.6)>;
GPS := sub<GPF | phi(F.2), phi(F.3), phi(F.4)>;
GPM := sub<GPS  | phi(F.3), phi(F.4)>;
Append(~PRlist2, GPR);
Append(~PNlist2, GPN);
Append(~PSlist2, GPS);
Append(~PMlist2, GPM);
Append(~Mu2, p^3 + p^2);

// G13, 10

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist2, GPF);
GPR := sub<GPF |  phi(F.5), phi(F.4), phi(F.6)>;
GPN := sub<GPR | phi(F.4), phi(F.5), phi(F.2)>;
GPS := sub<GPF | phi(F.6), phi(F.3^p), phi(F.4)>;
GPM := sub<GPS  | phi(F.6), phi(F.4)>;
Append(~PRlist2, GPR);
Append(~PNlist2, GPN);
Append(~PSlist2, GPS);
Append(~PMlist2, GPM);
Append(~Mu2, 2*p^3);

// G13, 11

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist2, GPF);
GPR := sub<GPF |  phi(F.5), phi(F.4), phi(F.6)>;
GPN := sub<GPR | phi(F.6), phi(F.5), phi(F.2)>;
GPS := sub<GPF | phi(F.6^p), phi(F.3), phi(F.4)>;
GPM := sub<GPS  | phi(F.3), phi(F.4)>;
Append(~PRlist2, GPR);
Append(~PNlist2, GPN);
Append(~PSlist2, GPS);
Append(~PMlist2, GPM);
Append(~Mu2, 2*p^3);

return PFlist2, PRlist2, PNlist2, PSlist2, PMlist2, Mu2;
end function;

MAX := 7^6;
for p in PrimesInInterval (5, 11) do 
   "\nprocess p = ", p;
   L := My13(p);
   PFlist2, PRlist2, PNlist2, PSlist2, PMlist2, Mu2 := Check13(L, p);
   PFlist := PFlist2;
   PRlist := PRlist2;
   PNlist := PNlist2;
   PSlist := PSlist2;
   PMlist := PMlist2;
   MinDeg := Mu2;

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


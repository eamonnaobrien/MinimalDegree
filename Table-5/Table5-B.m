// Entries in Table 5 with centre of rank 3

load "../setup-permrep.m";

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

My4B := function(p)

w := PrimitiveRoot(p);

K := GF(p);

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, b1, b2, b3> := FreeGroup (8);
Alpha := [a1, a2, a3, a4, a5];
Beta := [b1, b2, b3];

// common relations, typically commutators
Comms := [
(a2, a3) = 1, (a2, a4)= 1, (a3, a4) = 1,
(a4, a5) = a2, (a3, a5) = a1, (a2, a5) = 1, a1 = b1,
a2 = b2] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..5]]: i in [1..3]])
cat &cat([[(Beta[i], Beta[j]) = Id(F) : j in [i + 1..3]]: i in [1..3]]);

L := [];

// G4, 28

G := quo <F | Comms, a3^p =  b1^p = b2^p = b3^p = 1, 
a4^p = b1, a5^p = b3>;
Append (~L, G);

// G4, 32

G := quo <F | Comms,  b1^p = b2^p = b3^p = 1, 
a3^p =  b2, a4^p = b1^nu, a5^p = b3>;
Append (~L, G);

// G4, 33

G := quo <F | Comms,  b1^p = b2^p = b3^p = 1, 
a3^p =  b1, a4^p = b1*b2, a5^p = b3>;
Append (~L, G);

// G4, 34r

for r in [1..(p-2) by 2] do
G := quo <F | Comms,  b1^p = b2^p = b3^p = 1, 
a3^p = b1^2*b2, a4^p = b1^((w^r-1) mod p), a5^p = b3>;
Append (~L, G);
end for;

return L;
end function;

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

// G11, 2

G := quo <F | Comms, a1^p = a2^p = a3^p = a4^p = a5^p =  1,
a6^p = a1>;
Append (~L, G);

// G11, 4

G := quo <F | Comms, a1^p = a2^p = a3^p = a4^p =   1,
a5^p = a2^nu, a6^p = a1>;
Append (~L, G);

// G11, 7

G := quo <F | Comms, a1^p = a2^p = a3^p = a4^p =   1,
a5^p = a1, a6^p = a2*a1>;
Append (~L, G);

// G11, 10r

for r in [1..(p-1) div 2] do
G := quo <F | Comms, a1^p = a2^p = a3^p = a4^p =   1,
a5^p = a1*a2^(nu*r), a6^p = a1^r*a2>;
Append (~L, G);
end for;

// G11, 13

G := quo <F | Comms, a1^p = a2^p = a3^p =    1,
a4^p = a3, a5^p = a1, a6^p = a2>;
Append (~L, G);

// G11, 14r (r=1)

for r in [1] do
if IsPower(K!(p-1),2) eq false then
G := quo <F | Comms, a1^p = a2^p = a3^p =    1,
a4^p = a3^r, a5^p = a1, a6^p = a1*a2>;
Append (~L, G);
end if;
end for;

// G11, 14r (r=nu)

for r in [nu] do
if IsPower(K!(p-1),2) eq true then
G := quo <F | Comms, a1^p = a2^p = a3^p =    1,
a4^p = a3^r, a5^p = a1, a6^p = a1*a2>;
Append (~L, G);
end if;
end for;

return L;
end function;

Table5Phi4_11 := function(p)
   return My4B(p) cat My11(p);
end function;

CheckPhi4_11 := function(L, p)

w := PrimitiveRoot(p);
K := GF(p);
Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 0;

PFlist := []; // lists the group G
PRlist := []; // lists the subgroup R
PNlist := []; // lists kernel of non-linear irr char. from R
PSlist := []; // lists the subgroup S
PMlist := []; // lists kernel of non-linear irr char. from S
PTlist := []; // lists the subgroup T
PLlist := []; // lists kernel of non-linear irr char. from T
MinDeg := []; // Mu(G) from Table 5 

// 4, 28

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.3), phi(F.4), phi(F.2), phi(F.5^p)>;
GPN := sub<GPR | phi(F.3), phi(F.4), phi(F.5^p)>;
GPS := sub<GPF | phi(F.3), phi(F.4), phi(F.2), phi(F.5^p)>;
GPM := sub<GPS | phi(F.3), phi(F.2), phi(F.5^p)>;
GPT := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2),
                 phi(F.5), phi(F.6), phi(F.7), phi(F.8)>;
GPL := sub<GPT | phi(F.3), phi(F.1), phi(F.2), phi(F.4)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~PTlist, GPT);
Append(~PLlist, GPL);
Append(~MinDeg, p^3 + 2*p^2);

// 4, 32

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.3), phi(F.4), phi(F.5^p)>;
GPN := sub<GPR | phi(F.4), phi(F.5^p)>;
GPS := sub<GPF | phi(F.3), phi(F.4), phi(F.5^p)>;
GPM := sub<GPS | phi(F.3), phi(F.5^p)>;
GPT := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2),
 phi(F.5), phi(F.6), phi(F.7), phi(F.8)>;
GPL := sub<GPT | phi(F.3), phi(F.1), phi(F.2), phi(F.4)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~PTlist, GPT);
Append(~PLlist, GPL);
Append(~MinDeg, 2*p^3 + p^2);

// 4, 33

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.3), phi(F.5), phi(F.7)>;
GPN := sub<GPR | phi(F.3), phi(F.1), phi(F.5)>;
GPS := sub<GPF | phi(F.5), phi(F.4), phi(F.6)>;
GPM := sub<GPS | phi(F.2), phi(F.5)>;
GPT := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2),
 phi(F.5), phi(F.6), phi(F.7), phi(F.8)>;
GPL := sub<GPT | phi(F.3), phi(F.1), phi(F.2), phi(F.4)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~PTlist, GPT);
Append(~PLlist, GPL);
Append(~MinDeg, p^3 + 2*p^2);

// 4, 34r

for r in [1..(p-2) by 2] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.3), phi(F.4), phi(F.5^p)>;
GPN := sub<GPR | phi(F.3), phi(F.5^p)>;
GPS := sub<GPF | phi(F.3), phi(F.4), phi(F.5^p)>;
GPM := sub<GPS | phi(F.4), phi(F.5^p)>;
GPT := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2),
                 phi(F.5), phi(F.6), phi(F.7), phi(F.8)>;
GPL := sub<GPT | phi(F.3), phi(F.1), phi(F.2), phi(F.4)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~PTlist, GPT);
Append(~PLlist, GPL);
Append(~MinDeg, 2*p^3 + p^2);
end for;

// 11, 2

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2), phi(F.5)>;
GPN := sub<GPR | phi(F.1), phi(F.3), phi(F.4), phi(F.5)>;
GPS := sub<GPF | phi(F.2), phi(F.3), phi(F.4), phi(F.6)>;
GPM := sub<GPS | phi(F.2), phi(F.4), phi(F.6)>;
GPT := sub<GPF | phi(F.3), phi(F.2), phi(F.5), phi(F.6)>;
GPL := sub<GPT | phi(F.3), phi(F.2), phi(F.5)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~PTlist, GPT);
Append(~PLlist, GPL);
Append(~MinDeg, p^3 + 2*p^2);

// 11, 4

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.5)>;
GPN := sub<GPR | phi(F.1), phi(F.3), phi(F.4)>;
GPS := sub<GPF | phi(F.2), phi(F.3), phi(F.4), phi(F.6)>;
GPM := sub<GPS | phi(F.2), phi(F.4), phi(F.6)>;
GPT := sub<GPF | phi(F.3), phi(F.5), phi(F.6)>;
GPL := sub<GPT | phi(F.3), phi(F.5)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~PTlist, GPT);
Append(~PLlist, GPL);
Append(~MinDeg, 2*p^3 + p^2);

// 11, 7

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.6^p), phi(F.3), phi(F.4), phi(F.2), phi(F.5)>;
GPN := sub<GPR | phi(F.1), phi(F.3), phi(F.4), phi(F.5)>;
GPS := sub<GPF | phi(F.1), phi(F.2), phi(F.3), phi(F.4), phi(F.6)>;
GPM := sub<GPS | phi(F.2), phi(F.4), phi(F.6)>;
GPT := sub<GPF | phi(F.3), phi(F.5), phi(F.6)>;
GPL := sub<GPT | phi(F.3), phi(F.6)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~PTlist, GPT);
Append(~PLlist, GPL);
Append(~MinDeg, p^3 + 2*p^2);

// 11, 10r

for r in [1..(p-1) div 2] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.5)>;
GPN := sub<GPR | phi(F.1), phi(F.5), phi(F.4)>;
GPS := sub<GPF | phi(F.2), phi(F.3), phi(F.4), phi(F.6)>;
GPM := sub<GPS | phi(F.2), phi(F.4), phi(F.3)>;
GPT := sub<GPF | phi(F.3), phi(F.5), phi(F.6)>;
GPL := sub<GPT | phi(F.3), phi(F.6)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~PTlist, GPT);
Append(~PLlist, GPL);
Append(~MinDeg, 2*p^3 + p^2);
end for;

// 11, 13

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.6^p), phi(F.4), phi(F.5)>;
GPN := sub<GPR | phi(F.1), phi(F.5), phi(F.4)>;
GPS := sub<GPF | phi(F.5^p), phi(F.4), phi(F.6)>;
GPM := sub<GPS | phi(F.2), phi(F.4), phi(F.6)>;
GPT := sub<GPF | phi(F.1), phi(F.5*F.6), phi(F.4)>;
GPL := sub<GPT | phi(F.1), phi(F.5*F.6), phi(F.2*F.1)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~PTlist, GPT);
Append(~PLlist, GPL);
Append(~MinDeg, p^3 + 2*p^2);

// 11, 14r (r=1)

for r in [1] do
if p mod 4 eq 3 then 
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.6), phi(F.4^p), phi(F.5)>;
GPN := sub<GPR | phi(F.3), phi(F.6)>;
GPS := sub<GPF | phi(F.5^p), phi(F.4), phi(F.6)>;
GPM := sub<GPS | phi(F.2), phi(F.6)>;
GPT := sub<GPF | phi(F.6^p), phi(F.5), phi(F.4)>;
GPL := sub<GPT | phi(F.1), phi(F.5), phi(F.4)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~PTlist, GPT);
Append(~PLlist, GPL);
Append(~MinDeg, 2*p^3 + p^2);
end if;
end for;

// 11, 14r (r=nu)

for r in [nu] do
if p mod 4 eq 1 then 
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.6), phi(F.4^p), phi(F.5)>;
GPN := sub<GPR | phi(F.3), phi(F.6)>;
GPS := sub<GPF | phi(F.5^p), phi(F.4), phi(F.6)>;
GPM := sub<GPS | phi(F.2), phi(F.6)>;
GPT := sub<GPF | phi(F.6^p), phi(F.5), phi(F.4)>;
GPL := sub<GPT | phi(F.1), phi(F.5), phi(F.4)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~PTlist, GPT);
Append(~PLlist, GPL);
Append(~MinDeg, 2*p^3 + p^2);
end if;
end for;

return PFlist, PRlist, PNlist, PSlist,
   PMlist, PTlist, PLlist, MinDeg;
end function;

MAX := 7^6;

for p in PrimesInInterval (5, 11) do 
   "\nProcess p = ", p;
   L := Table5Phi4_11(p);
   PFlist, PRlist, PNlist, PSlist,
      PMlist, PTlist, PLlist, MinDeg := CheckPhi4_11(L, p);

   for i in [1..#L] do
      PF := PFlist[i];
      PR := PRlist[i];
      PN := PNlist[i];
      PS := PSlist[i];
      PM := PMlist[i];
      PT := PTlist[i];
      PL := PLlist[i];
      Mu_value := MinDeg[i];

      Int := Core(PF, PN) meet Core(PF, PM) meet Core(PF, PL);
      assert #Int eq 1;
      // printf "%o  %o\n", i, #Int;

      phiN := CosetAction (PF, PN);
      phiM := CosetAction (PF, PM);
      phiL := CosetAction (PF, PL);
      pi := PermutationRepresentationSumH (PF, [phiN, phiM, phiL]);
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

      QPTL, l := quo<PT | PL>;
      linQPL := LinearCharacters (QPTL);
      for j in [1..#linQPL] do
         if IsFaithful(linQPL[j]) eq true then
            rho := linQPL[j];
            break;
         end if;
      end for;
      rho_bar := LiftCharacter(rho, l, PT);
      delta := Induction(rho_bar, PF);
      assert IsIrreducible(delta);

   end for;
end for;

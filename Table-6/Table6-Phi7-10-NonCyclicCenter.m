load "../setup-permrep.m";

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

//Phi7 with center Cp X Cp

My7 := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, b1, b2> := FreeGroup (7);
Alpha := [a1, a2, a3, a4, a5];
Beta := [b1, b2];

// common relations, typically commutators
Comms := [
(a2, a3) = 1, (a2, a4)= 1, (a3, a4) = a1,
(a4, a5) = a2, (a3, a5) = 1, (a2, a5) = a1, a1 = b1, 
(b1, b2) = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..5]]: i in [1..2]]);

L := [];

// G7, 14

G := quo <F | Comms, a2^p = a4^p =  b1^p = b2^p = 1,
a3^p = b1, a5^p = b2>;
Append (~L, G);

return L;
end function;

//Phi8 with center Cp X Cp

My8 := function(p)

F<a1, a2, a3, a4, a5, b1, b2> := FreeGroup (7);
Alpha := [a1, a2, a3, a4, a5];
Beta := [b1, b2];

// common relations, typically commutators
Comms := [
(a2, a3) = 1, (a2, a4)= 1, (a3, a4) = a1,
(a4, a5) = a2, (a3, a5) = 1, (a2, a5) = a1, a1 = b1, 
(b1, b2) = 1, a3^-1 = a5^p] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..5]]: i in [1..2]]);

L := [];

// G8, 7

G := quo <F | Comms,   b1^p = b2^p = 1,
a4^p = a2, a5^(p^2) =b2>;
Append (~L, G);

return L;
end function;

//Phi9 with center Cp X Cp

My9 := function(p)

F<a1, a2, a3, a4, a5, b1, b2> := FreeGroup (7);
Alpha := [a1, a2, a3, a4, a5];
Beta := [b1, b2];

// common relations, typically commutators
Comms := [
(a2, a3) = 1, (a2, a4)= 1, (a3, a4) = 1,
(a4, a5) = a3, (a3, a5) = a2, (a2, a5) = a1, a1 = b1, 
(b1, b2) = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..5]]: i in [1..2]]);

L := [];

// G9, 9r
w := PrimitiveRoot (p);

if p mod 3 eq 1 then add := [w^i: i in [0..2]]; else add := [1]; end if;
for r in add do
G := quo <F | Comms, a2^p = a3^p = b1^p = b2^p = 1,
               a4^p = b1^r, a5^p = b2>;
Append (~L, G);
end for;

return L;
end function;

//Phi10 with center Cp X Cp

My10 := function(p)

F<a1, a2, a3, a4, a5, b1, b2> := FreeGroup (7);
Alpha := [a1, a2, a3, a4, a5];
Beta := [b1, b2];

// common relations, typically commutators
Comms := [
(a2, a3) = 1, (a2, a4)= 1, (a3, a4) = a1,
(a4, a5) = a3, (a3, a5) = a2, (a2, a5) = a1, a1 = b1, 
(b1, b2) = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..5]]: i in [1..2]]);

L := [];

// G10, 6

G := quo <F | Comms, a2^p = a3^p = a4^p =  b1^p = b2^p = 1,
a5^p = b2>;
Append (~L, G);

// G10, 9r
w := PrimitiveRoot (p);

if p mod 3 eq 1 then add := [w^i: i in [0..2]];
else add := [1]; end if;
for r in add do
G := quo <F | Comms, a2^p = a3^p =  b1^p = b2^p = 1,
               a4^p = b1^r, a5^p = b2>;
Append (~L, G);
end for;

return L;
end function;

Table6Phi7to10 := function(p)
   return My7(p) cat My8(p) cat My9(p) cat My10(p);
end function;

Check7 := function(L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 0;

PFlist1 := []; // lists the group G
PRlist1 := []; // lists the subgroup R
PNlist1 := []; // lists kernel of non-linear irr char.
PKlist1 := []; // lists kernel of linear char.
Mu1 := [];     // Mu(G) from Table 6 

// G7, 14

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3^p), phi(F.4), phi(F.5^p)>;
GPN := sub<GPR | phi(F.2), phi(F.4), phi(F.5^p)>;
GPK := sub<GPF | phi(F.1), phi(F.2), phi(F.3), phi(F.4)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PKlist1, GPK);
Append(~Mu1, p^3 + p^2);

return PFlist1, PRlist1, PNlist1, PKlist1, Mu1;
end function;

Check8 := function(L, p)

count := 1;

PFlist2 := []; // lists the group G
PRlist2 := []; // lists the subgroup R
PNlist2 := []; // lists kernel of non-linear irr char.
PKlist2 := []; // lists kernel of linear char.
Mu2 := []; //Mu(G) from table

// G8, 7

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist2, GPF);
GPR := sub<GPF | phi(F.4^(p^2)), phi(F.5)>;
GPN := sub<GPR | phi(F.5)>;
GPK := sub<GPF | phi(F.1), phi(F.2), phi(F.4)>;
Append(~PRlist2, GPR);
Append(~PNlist2, GPN);
Append(~PKlist2, GPK);
Append(~Mu2, 2*p^3);

return PFlist2, PRlist2, PNlist2, PKlist2, Mu2;
end function;

Check9 := function(L, p)

count := 2;

PFlist3 := []; // lists the group G
PRlist3 := []; // lists the subgroup R
PNlist3 := []; // lists kernel of non-linear irr char.
PKlist3 := []; // lists kernel of linear char.
Mu3 := [];     // Mu(G) from table 5 

// G9, 9r
w := PrimitiveRoot (p);

if p mod 3 eq 1 then add := [w^i: i in [0..2]];
else add := [1]; end if;
for r in add do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist3, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4), phi(F.5^p)>;
GPN := sub<GPR | phi(F.2), phi(F.3), phi(F.5^p)>;
GPK := sub<GPF | phi(F.1), phi(F.2), phi(F.3), phi(F.4)>;
Append(~PRlist3, GPR);
Append(~PNlist3, GPN);
Append(~PKlist3, GPK);
Append(~Mu3, p^3 + p^2);
end for;

return PFlist3, PRlist3, PNlist3, PKlist3, Mu3;
end function;

Check10 := function(L, p)

count := 2 + GCD(p-1, 3);

PFlist4 := []; // lists the group G
PRlist4 := []; // lists the subgroup R
PNlist4 := []; // lists kernel of non-linear irr char.
PKlist4 := []; // lists kernel of linear char.
Mu4 := [];     // Mu(G) from Table 6

// G10, 6

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist4, GPF);
GPR := sub<GPF | phi(F.1), phi(F.2), phi(F.3), phi(F.5^p)>;
GPN := sub<GPR | phi(F.2), phi(F.3), phi(F.5^p)>;
GPK := sub<GPF | phi(F.1), phi(F.2), phi(F.3), phi(F.4)>;
Append(~PRlist4, GPR);
Append(~PNlist4, GPN);
Append(~PKlist4, GPK);
Append(~Mu4, p^3 + p^2);

// G10, 9r
w := PrimitiveRoot (p);

if p mod 3 eq 1 then add := [w^i: i in [0..2]];
else add := [1]; end if;
for r in add do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist4, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.4^p), phi(F.5^p)>;
GPN := sub<GPR | phi(F.2), phi(F.3), phi(F.5^p)>;
GPK := sub<GPF | phi(F.1), phi(F.2), phi(F.3), phi(F.4)>;
Append(~PRlist4, GPR);
Append(~PNlist4, GPN);
Append(~PKlist4, GPK);
Append(~Mu4, p^3 + p^2);
end for;

return PFlist4, PRlist4, PNlist4, PKlist4, Mu4;
end function;

MAX := 11^6;

for p in PrimesInInterval (5, 11) do 
   "\nprocess p = ", p;
   L := Table6Phi7to10(p);

   PFlist1, PRlist1, PNlist1, PKlist1, Mu1 := Check7(L, p);
   PFlist2, PRlist2, PNlist2, PKlist2, Mu2 := Check8(L, p);
   PFlist3, PRlist3, PNlist3, PKlist3, Mu3 := Check9(L, p);
   PFlist4, PRlist4, PNlist4, PKlist4, Mu4 := Check10(L, p);
   PFlist := PFlist1 cat PFlist2 cat PFlist3 cat PFlist4;
   PRlist := PRlist1 cat PRlist2 cat PRlist3 cat PRlist4;
   PNlist := PNlist1 cat PNlist2 cat PNlist3 cat PNlist4;
   PKlist := PKlist1 cat PKlist2 cat PKlist3 cat PKlist4;
   MinDeg := Mu1 cat Mu2 cat Mu3 cat Mu4;

   for i in [1..#L] do
      PF := PFlist[i];
      PR := PRlist[i];
      PN := PNlist[i];
      PK := PKlist[i];
      Mu_value := MinDeg[i];
      Int := Core(PF, PN) meet Core(PF, PK);
      assert #Int eq 1;

      phiN := CosetAction (PF, PN);
      phiK := CosetAction (PF, PK);
      pi := PermutationRepresentationSumH (PF, [phiN, phiK]);
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

      QPFK, h := quo<PF | PK>;
      linQPK := LinearCharacters (QPFK);
      for j in [1..#linQPK] do
         if IsFaithful(linQPK[j]) eq true then
            lambda := linQPK[j];
            break;
         end if;
      end for;
      eta := LiftCharacter(lambda, h, PF);
      assert IsIrreducible(eta);

   end for;
end for;

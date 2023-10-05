load "../setup-permrep.m";

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

My3D := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, b1, b2, b3> := FreeGroup (7);
Alpha := [a1, a2, a3, a4];
Beta := [b1, b2, b3];

// common relations, typically commutators
Comms := [
(a2, a3) = 1, (a2, a4)= a1, (a3, a4) = a2, a1 = b1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..4]]: i in [1..3]])
cat &cat([[(Beta[i], Beta[j]) = Id(F) : j in [i + 1..3]]: i in [1..3]]);

L := [];

// G3, 24r

for r in [1,nu] do
G := quo <F | Comms, a2^p =  b1^p = b2^p = b3^p = 1,
a3^p = b1^r, a4^p = b2>;
Append (~L, G);
end for;

return L;
end function;

My4B := function(p)

w := PrimitiveRoot(p);

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

// G4, 18

G := quo <F | Comms, a3^p =  b1^p = b2^p = b3^p = 1, 
a4^p = b1, a5^p = b2>;
Append (~L, G);

// G4, 19

G := quo <F | Comms, a3^p = a5^p =  b1^p = b2^p = b3^p = 1, 
a4^p = b1>;
Append (~L, G);

// G4, 23

G := quo <F | Comms, a5^p =  b1^p = b2^p = b3^p = 1, 
a3^p = b2, a4^p = b1^nu>;
Append (~L, G);

// G4, 24

G := quo <F | Comms, a5^p =  b1^p = b2^p = b3^p = 1, 
a3^p = b1, a4^p = b1*b2>;
Append (~L, G);

// G4, 25r

for r in [1..(p-2) by 2] do
G := quo <F | Comms, a5^p =  b1^p = b2^p = b3^p = 1, 
a3^p = b1^2*b2, a4^p = b1^((w^r-1) mod p)>;
Append (~L, G);
end for;

return L;
end function;

My6B := function(p)

w := PrimitiveRoot(p);

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, b1, b2, b3> := FreeGroup (8);
Alpha := [a1, a2, a3, a4, a5];
Beta := [b1, b2, b3];

// common relations, typically commutators
Comms := [
(a2, a3) = 1, (a2, a4)= 1, (a3, a4) = a1,
(a4, a5) = a3, (a3, a5) = a2, (a2, a5) = 1, a1 = b1,
a2 = b2] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..5]]: i in [1..3]])
cat &cat([[(Beta[i], Beta[j]) = Id(F) : j in [i + 1..3]]: i in [1..3]]);

L := [];

// G6, 11r

for r in [1,nu] do
G := quo <F | Comms, a3^p = a4^p =  b1^p = b2^p = b3^p = 1, a5^p = b1^r>;
Append (~L, G);
end for;

// G6, 17r

for r in [1,nu] do
G := quo <F | Comms, a3^p =  b1^p = b2^p = b3^p = 1, 
              a4^p = b1, a5^p = (b1^r)*b2>;
Append (~L, G);
end for;

// G6, 18

G := quo <F | Comms, a3^p =  b1^p = b2^p = b3^p = 1,
a4^p = b2, a5^p = b1^nu>;
Append (~L, G);

// G6, 19r

for r in [1..(p-2) by 2] do
G := quo <F | Comms, a3^p =  b1^p = b2^p = b3^p = 1,
a4^p = b1^2*b2, a5^p = b1^((w^r-1) mod p)>;
Append (~L, G);
end for;

return L;
end function;

Table4 := function(p)
   return My3D(p) cat My4B(p) cat My6B(p);
end function;

CheckTable4 := function(L, p)
Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 0;

Hlist := []; // lists the subgroup H 
Rlist := []; // lists the subgroup R
Nlist := []; // lists kernel of non-linear irr char. from R
Slist := []; // lists the subgroup S
Mlist := []; // lists kernel of non-linear irr char. from S
MinDeg := []; // Mu(H) from Table 4 
GMinDeg := []; // Mu(G) from Table 4 

// 3, 24r

for r in [1,nu] do
count := count+1;
F := L[count];
H := sub<F | F.1, F.2, F.3, F.4, F.5, F.6>;
Append(~Hlist, H);
GPR := sub<F | (F.3), (F.4^p), (F.2)>;
GPN := sub<F | (F.4^p), (F.2)>;
GPS := sub<F | (F.1), (F.3), (F.4), (F.2), (F.5), (F.6)>;
GPM := sub<F  | (F.3), (F.1), (F.2)>;
Append(~Rlist, GPR);
Append(~Nlist, GPN);
Append(~Slist, GPS);
Append(~Mlist, GPM);
Append(~MinDeg, p^3 + p^2);
Append(~GMinDeg, p^3 + p^2 + p);
end for;

// 4, 18

count := count+1;
F := L[count];
H := sub<F | F.1, F.2, F.3, F.4, F.5, F.6, F.7>;
Append(~Hlist, H);
GPR := sub<F | (F.3), (F.4), (F.5^p)>;
GPN := sub<F | (F.4), (F.3)>;
GPS := sub<F | (F.3), (F.4), (F.5^p)>;
GPM := sub<F  | (F.3), (F.5^p)>;
Append(~Rlist, GPR);
Append(~Nlist, GPN);
Append(~Slist, GPS);
Append(~Mlist, GPM);
Append(~MinDeg, p^3 + p^2);
Append(~GMinDeg, p^3 + p^2 + p);

// 4, 19

count := count+1;
F := L[count];
H := sub<F | F.1, F.2, F.3, F.4, F.5, F.6, F.7>;
Append(~Hlist, H);
GPR := sub<F | (F.2), (F.3), (F.4)>;
GPN := sub<F | (F.4), (F.3)>;
GPS := sub<F | (F.2), (F.3), (F.4)>;
GPM := sub<F  | (F.2), (F.3)>;
Append(~Rlist, GPR);
Append(~Nlist, GPN);
Append(~Slist, GPS);
Append(~Mlist, GPM);
Append(~MinDeg, p^3 + p^2);
Append(~GMinDeg, p^3 + p^2 + p);

// 4, 23

count := count+1;
F := L[count];
H := sub<F | F.1, F.2, F.3, F.4, F.5, F.6, F.7>;
Append(~Hlist, H);
GPR := sub<F | (F.3), (F.4)>;
GPN := sub<F | (F.3)>;
GPS := sub<F | (F.3), (F.4)>;
GPM := sub<F | (F.4)>;
Append(~Rlist, GPR);
Append(~Nlist, GPN);
Append(~Slist, GPS);
Append(~Mlist, GPM);
Append(~MinDeg, 2*p^3);
Append(~GMinDeg, 2*p^3 + p);

// 4, 24

count := count+1;
F := L[count];
H := sub<F | F.1, F.2, F.3, F.4, F.5, F.6, F.7>;
Append(~Hlist, H);
GPR := sub<F | (F.5), (F.4)>;
GPN := sub<F | (F.2), (F.5)>;
GPS := sub<F | (F.3), (F.2), (F.5)>;
GPM := sub<F | (F.1), (F.3), (F.5)>;
Append(~Rlist, GPR);
Append(~Nlist, GPN);
Append(~Slist, GPS);
Append(~Mlist, GPM);
Append(~MinDeg, p^3 + p^2);
Append(~GMinDeg, p^3 + p^2 + p);

// 4, 25r

for r in [1..(p-2) by 2] do
count := count+1;
F := L[count];
H := sub<F | F.1, F.2, F.3, F.4, F.5, F.6, F.7>;
Append(~Hlist, H);
GPR := sub<F | (F.3), (F.4)>;
GPN := sub<F | (F.3)>;
GPS := sub<F | (F.3), (F.4)>;
GPM := sub<F | (F.4)>;
Append(~Rlist, GPR);
Append(~Nlist, GPN);
Append(~Slist, GPS);
Append(~Mlist, GPM);
Append(~MinDeg, 2*p^3);
Append(~GMinDeg, 2*p^3 + p);
end for;

// 6, 11r

for r in [1,nu] do
count := count+1;
F := L[count];
H := sub<F | F.1, F.2, F.3, F.4, F.5, F.6, F.7>;
Append(~Hlist, H);
GPR := sub<F | (F.3), (F.2), (F.5^p), (F.4)>;
GPN := sub<F | (F.1), (F.3), (F.4)>;
GPS := sub<F | (F.3), (F.2), (F.5)>;
GPM := sub<F | (F.2), (F.3)>;
Append(~Rlist, GPR);
Append(~Nlist, GPN);
Append(~Slist, GPS);
Append(~Mlist, GPM);
Append(~MinDeg, p^3 + p^2);
Append(~GMinDeg, p^3 + p^2 + p);
end for;

// 6, 17r

for r in [1,nu] do
count := count+1;
F := L[count];
H := sub<F | F.1, F.2, F.3, F.4, F.5, F.6, F.7>;
Append(~Hlist, H);
GPR := sub<F | (F.3), (F.7), (F.4)>;
GPN := sub<F | (F.1), (F.3), (F.4)>;
GPS := sub<F | (F.3), (F.4^p), (F.5)>;
GPM := sub<F | (F.2), (F.3)>;
Append(~Rlist, GPR);
Append(~Nlist, GPN);
Append(~Slist, GPS);
Append(~Mlist, GPM);
Append(~MinDeg, p^3 + p^2);
Append(~GMinDeg, p^3 + p^2 + p);
end for;

// 6, 18

count := count+1;
F := L[count];
H := sub<F | F.1, F.2, F.3, F.4, F.5, F.6, F.7>;
Append(~Hlist, H);
GPR := sub<F | (F.3), (F.5), (F.4^p)>;
GPN := sub<F | (F.2), (F.3)>;
GPS := sub<F | (F.3), (F.4), (F.5^p)>;
GPM := sub<F | (F.1), (F.3)>;
Append(~Rlist, GPR);
Append(~Nlist, GPN);
Append(~Slist, GPS);
Append(~Mlist, GPM);
Append(~MinDeg, 2*p^3);
Append(~GMinDeg, 2*p^3 + p);

// 6, 19r

for r in [1..(p-2) by 2] do
count := count+1;
F := L[count];
H := sub<F | F.1, F.2, F.3, F.4, F.5, F.6, F.7>;
Append(~Hlist, H);
GPR := sub<F | (F.3), (F.5), (F.4^p)>;
GPN := sub<F | (F.2), (F.3)>;
GPS := sub<F | (F.3), (F.4), (F.5^p)>;
GPM := sub<F | (F.1), (F.3)>;
Append(~Rlist, GPR);
Append(~Nlist, GPN);
Append(~Slist, GPS);
Append(~Mlist, GPM);
Append(~MinDeg, 2*p^3);
Append(~GMinDeg, 2*p^3 + p);
end for;

return Hlist, Rlist, Nlist, Slist, Mlist, MinDeg, GMinDeg;
end function;

MAX := 7^6;

for p in PrimesInInterval (5, 11) do 
   "\nProcess p = ", p;
   L := Table4(p);
   Hlist, Rlist, Nlist, Slist, Mlist, MinDeg, GMinDeg := CheckTable4(L, p);

   for i in [1..#L] do
      G := L[i];
      Q, phi := pQuotient (G, p, 10);
      PH := phi(Hlist[i]);
      PR := phi(Rlist[i]);
      PN := phi(Nlist[i]);
      PS := phi(Slist[i]);
      PM := phi(Mlist[i]);
      HMu := MinDeg[i];
      GMu := GMinDeg[i];

      Int := Core(PH, PN) meet Core(PH, PM);
      assert #Int eq 1;
      // printf "%o  %o\n", i, #Int;

      phiN := CosetAction (PH, PN);
      phiM := CosetAction (PH, PM);
      pi := PermutationRepresentationSumH (PH, [phiN, phiM]);
      J := Image (pi);
      assert #J eq #PH;
      if #J le MAX then assert IsIsomorphic (J, PH); end if;
      assert Degree (J) eq HMu;

      // Irreducibility checks for X_H 
      QPRN, f := quo<PR | PN>;
      linQP := LinearCharacters(QPRN);
      for j in [1..#linQP] do
         if IsFaithful(linQP[j]) eq true then
            chi := linQP[j];
            break;
         end if;
      end for;
      chi_bar := LiftCharacter(chi, f, PR);
      psi := Induction(chi_bar, PH);
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
      eta := Induction(lambda_bar, PH);
      assert IsIrreducible(eta);

      // setup perm rep for G
      I, IS := DetermineMinRep (G, Q, PH, [PN, PM], phi);
      assert #&meet[Core (Q, s): s in IS] eq 1;
      assert #I eq #Q;
      if #Q le MAX then assert IsIsomorphic (I, Q); end if;
      assert Degree (I) eq GMu;
   end for;
end for;

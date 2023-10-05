load "../setup-permrep.m";

// For all the groups in the list, c(G) = p^4

My8 := function(p)

F<a1, a2, a3, a4, a5, b1> := FreeGroup (6);
Alpha := [a1, a2, a3, a4, a5];

// common relations, typically commutators
Comms := [
(a2, a3) = 1, (a2, a4)= 1, (a3, a4) = a1,
(a4, a5) = a2, (a3, a5) = 1, (a2, a5) = a1, a1 = b1^p,
a3^-1 = a5^p]
cat
[(b1, Alpha[j]) = Id(F) : j in [1..5]];

L := [];

// G8, 1

G := quo <F | Comms,  a5^(p^2) = b1^(p^2) = 1,
a4^p*a2^-1 = b1^-1>;
Append (~L, G);

// G8, 3

G := quo <F | Comms,   b1^(p^2) = 1,
a4^p*a2^-1 = b1^-1, a5^(p^2) = b1^p>;
Append (~L, G);

return L;
end function;

My10 := function(p)

F<a1, a2, a3, a4, a5, b1> := FreeGroup (6);
Alpha := [a1, a2, a3, a4, a5];

// common relations, typically commutators
Comms := [
(a2, a3) = 1, (a2, a4)= 1, (a3, a4) = a1,
(a4, a5) = a3, (a3, a5) = a2, (a2, a5) = a1, a1 = b1^p]
cat
[(b1, Alpha[j]) = Id(F) : j in [1..5]];

L := [];

// G10, 1

G := quo <F | Comms, a2^p = a3^p = a4^p = a5^p = b1^(p^2) = 1>;
Append (~L, G);

// G10, 2r
w := PrimitiveRoot (p);

if p mod 4 eq 1 then add := [w^i: i in [0..3]];
else add := [w^i: i in [0..1]]; end if;
for r in add do
G := quo <F | Comms, a2^p = a3^p = a4^p = b1^(p^2) = 1,
               a5^p = b1^r>;
Append (~L, G);
end for;

return L;
end function;

Table6CyclicCenter := function(p)
   return My8(p) cat My10(p);
end function;

Check8 := function(L, p)

count := 0;

PFlist1 := []; // lists the group G
PRlist1 := []; // lists the subgroup R
PNlist1 := []; // lists kernel of non-linear irr char. from R

// G8, 1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.2), phi(F.4)>;
GPN := sub<GPR | phi(F.4)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);

// G8, 3

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.2), phi(F.4)>;
GPN := sub<GPR | phi(F.4)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);

return PFlist1, PRlist1, PNlist1;
end function;

Check10 := function(L, p)

Z := Integers ();

count := 2;

PFlist2 := [];
PRlist2 := [];
PNlist2 := [];

// G10, 1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist2, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.6)>;
GPN := sub<GPR | phi(F.2), phi(F.3)>;
Append(~PRlist2, GPR);
Append(~PNlist2, GPN);

// G10, 2r
w := PrimitiveRoot (p);

if p mod 4 eq 1 then add := [w^i: i in [0..3]];
else add := [w^i: i in [0..1]]; end if;
for r in add do
count := count+1;
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6];
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist2, GPF);
GPR := sub<GPF | phi(F.2), phi(F.3), phi(F.5^p)>;
GPN := sub<GPR | phi(F.2), phi(F.3)>;
Append(~PRlist2, GPR);
Append(~PNlist2, GPN);
end for;

return PFlist2, PRlist2, PNlist2;
end function;

for p in PrimesInInterval (5, 11) do 
   "\nprocess p = ", p;
   L := Table6CyclicCenter(p);
   PFlist1, PRlist1, PNlist1 := Check8(L, p);
   PFlist2, PRlist2, PNlist2 := Check10(L, p);
   PFlist := PFlist1 cat PFlist2;  // lists the group G
   PRlist := PRlist1 cat PRlist2;  // lists the subgroup R
   PNlist := PNlist1 cat PNlist2;  // lists kernel of non-linear irr char. from R
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
      // printf "%o  %o\n", i, #Int;

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

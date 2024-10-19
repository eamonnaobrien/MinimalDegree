
// exceptional groups from Phi34

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;
   
Table3Phi34 := function(p)
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
   
   // G34, 1
   G := quo <F | Comms, a2^p = a4^p = 1>;
   Append (~L, G);
   
   return L;
end function;
   
Check34 := function(L, p)
   
   w := PrimitiveRoot(p);
   K := GF(p);
   
   Z := Integers ();
   nu := Z ! (NonQuadraticResidue (p)); // nu
   
   Glist := [];
   Tlist := [];
   Nlist := [];
   MuGlist := [];
   MuTlist := [];
   
   count := 0;
   
   // (34, 1) 
   count := count+1;
   F := L[count];
   Alpha := [F.1]; Beta:= [F.2, F.3, F.4, F.5, F.6];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.1 ) >;
   Append(~Nlist, N1);
   
   // Q is phi_4(221)b
   Q := Group < a, a1, a2, b1, b2 | (a1, a) = b1, (a2, a) = b2,
               (b1, a) = 1, (b2, a) = 1, (a1, a2) = 1, (a1, b1) = 1, 
               (a1, b2) = 1, (a2, b1) = 1, (a2, b2) = 1, (b1, b2) = 1,  
               a2^p = b1, a^p = b2, a1^p = 1, b1^p = 1, b2^p = 1>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, p^3);
   Append(~MuTlist, p^3+p^2);
   
   return Glist, Tlist, Nlist, MuGlist, MuTlist;
end function;

for p in PrimesInInterval (5, 13) do 
   "\nprocess p = ", p;
   L := Table3Phi34(p);

   Glist, Tlist, Nlist, MuGlist, MuTlist := Check34(L, p);

   for i in [1..#L] do
      P := Glist[i];
      N := Nlist[i];
      T := Tlist[i];
      MuP := MuGlist[i];
      MuT := MuTlist[i];
      assert IsNormal (P, N);
      Q := quo< P | N>;
      assert IsIsomorphic(Q, T);
      assert MuP eq Mu(P);
      assert MuT eq Mu(T);
   end for;
end for;

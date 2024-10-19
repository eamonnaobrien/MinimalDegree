// exceptional groups from Phi28

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;
   
Table3Phi28 := function(p)
   
   Z := Integers ();
   nu := Z ! (NonQuadraticResidue (p)); // nu
   
   F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
   Alpha := [a2, a3, a4, a5, a6];
   Beta := [a1];
   
   // common relations, typically commutators
   Comms := [ (a2, a3) = 1, (a2, a4) = 1, (a2, a5) = 1,
   (a2, a6) = a1, (a3, a4) = a1, (a3, a5)= 1,
   (a3, a6) = a2, (a4, a5) = a1, (a4, a6)= a3, 
   (a5, a6)= 1, a1^p = 1, a2^p = 1, a3^p = a1,
   a6^p = a5, a4^p = a2] cat
   [(a1, Alpha[j]) = Id(F) : j in [1..5]];
   
   L := [];
   
   // G28, 2r (r=p-1)
   r := p - 1;
   G := quo <F | Comms, a6^(p^2) = a1^r>;
   Append (~L, G);
   
   return L;
end function;
   
Check28 := function(L, p)
   
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
   
   // (28, 2r) (r=p-1)
   count := count+1;
   F := L[count];
   Alpha := [F.1]; Beta:= [F.2, F.3, F.4, F.5, F.6];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.1 ) >;
   Append(~Nlist, N1);
   
   // Q is phi_3(221)b_1
   Q := Group < a, a1, a2, a3 | (a1, a) = a2, (a2, a) = a3,
                (a3, a) = 1, (a1, a2) = 1, (a1, a3) = 1, (a2, a3) = 1,  
                a2^p = 1, a3^p = 1, a^(p^2) = 1, a1^p = a3>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, p^3);
   Append(~MuTlist, p^3+p^2);
   
   return Glist, Tlist, Nlist, MuGlist, MuTlist;
   end function;

for p in PrimesInInterval (5, 13) do 
   "\nprocess p = ", p;
   L := Table3Phi28(p);

   Glist, Tlist, Nlist, MuGlist, MuTlist := Check28(L, p);

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

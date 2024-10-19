// exceptional groups from Phi12

Table3Phi12 := function(p)
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
   
   // G12, 1
   G := quo <F | Comms, a3^p = a4^p = a5^p = a6^p = 1>;
   Append (~L, G);
   
   // G12, 2
   G := quo <F | Comms, a4^p = a5^p = a6^p = 1, a3^p = a1>;
   Append (~L, G);
   
   // G12, 8
   G := quo <F | Comms, a4^p = a6^p = 1, a3^p = a1, a5^p = a2>;
   Append (~L, G);
   
   return L;
end function;

NonQuadraticResidue := function (p)
   for x in GF (p) do
      if not IsPower (x, 2) then return x; end if;
   end for;
end function;
   
Check12 := function(L, p)
   
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
   
   // G(12, 1)
   count := count+1;
   F := L[count];
   Alpha := [F.3, F.4, F.5, F.6]; Beta:= [F.1, F.2];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.1*F.2 ) >;
   Append(~Nlist, N1);
   
   // Q is phi_5(1^5)
   Q := Group < a1, a2, a3, a4, b | (a1, a2) = b, (a3, a1)= 1, 
               (a1, a4) = 1, (a1, b) = 1, (a2, a3) = 1, (a2, a4) = 1, 
               (a2, b) = 1, (a3, a4) = b, (a3, b) = 1, (a4, b) = 1,
               a2^p = 1, a3^p = 1, a4^p = 1, b^p = 1, a1^(p) = 1 >;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 2*p^2);
   Append(~MuTlist, p^3);
   
   // G(12, 2)
   count := count+1;
   F := L[count];
   Alpha := [F.3, F.4, F.5, F.6]; Beta:= [F.1, F.2];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.1*F.2 ) >;
   Append(~Nlist, N1);
   
   // Q is phi_5(2111)
   Q := Group < a1, a2, a3, a4, b | (a1, a2) = b, (a3, a1)= 1, 
               (a1, a4) = 1, (a1, b) = 1, (a2, a3) = 1, (a2, a4) = 1, 
               (a2, b) = 1, (a3, a4) = b, (a3, b) = 1, (a4, b) = 1,
               a2^p = 1, a3^p = 1, a4^p = 1, b^p = 1, a1^(p) = b>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 2*p^2);
   Append(~MuTlist, p^3);
   
   // G(12, 8)
   count := count+1;
   F := L[count];
   Alpha := [F.3, F.4, F.5, F.6]; Beta:= [F.1, F.2];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.1*F.2 ) >;
   Append(~Nlist, N1);
   
   // Q is phi_5(2111)
   Q := Group < a1, a2, a3, a4, b | (a1, a2) = b, (a3, a1) = 1, 
               (a1, a4) = 1, (a1, b) = 1, (a2, a3) = 1, (a2, a4) = 1, 
               (a2, b) = 1, (a3, a4) = b, (a3, b) = 1, (a4, b) = 1,
               a2^p = 1, a3^p = 1, a4^p = 1, b^p = 1, a1^(p) = b>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 2*p^2);
   Append(~MuTlist, p^3);
   
   return Glist, Tlist, Nlist, MuGlist, MuTlist;
end function;

for p in PrimesInInterval (5, 13) do 
   "\nprocess p = ", p;
   L := Table3Phi12(p);

   Glist, Tlist, Nlist, MuGlist, MuTlist := Check12(L, p);

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

// exceptional groups from Phi9

NonQuadraticResidue := function (p)
   for x in GF (p) do
      if not IsPower (x, 2) then return x; end if;
   end for;
end function;

My9B := function(p)
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
   
   // G9, 8
   G := quo <F | Comms, a4^p = b2, a2^p = a3^p = a5^p = b1^p = b2^p = 1>;
   Append (~L, G);
   
   // G9, 10
   G := quo <F | Comms, a2^p = a3^p = b1^p = b2^p = 1, a4^p = b2, a5^p = b1>;
   Append (~L, G);
   
   return L;
end function;
   
Table3Phi9 := function(p)
   return My9B(p);
end function;
   
Check9 := function(L, p)
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
   
   // G(9, 8)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.6*F.7^(-1) ) >;
   Append(~Nlist, N1);
   
   // Q is phi_9(2111)b_1
   Q := Group < a, a1, a2, a3, a4 | (a1, a) = a2, (a2, a) = a3,
               (a3, a) = a4, (a4, a) = 1, (a1, a2) = 1, (a1, a3)= 1,
               (a1, a4) = 1, (a2, a3) = 1, (a2, a4) = 1, (a3, a4) = 1,
               a2^p = 1, a3^p = 1, a4^p = 1, a^p = 1, a1^p = a4>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 2*p^2);
   Append(~MuTlist, p^3);
   
   // G(9, 10)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.6*F.7^(-1) ) >;
   Append(~Nlist, N1);
   
   // Q is phi_9(2111)b_1
   Q := Group < a, a1, a2, a3, a4 | (a1, a) = a2, (a2, a) = a3,
               (a3, a) = a4, (a4, a) = 1, (a1, a2) = 1, (a1, a3)= 1,
               (a1, a4) = 1, (a2, a3) = 1, (a2, a4) = 1, (a3, a4) = 1,
               a2^p = 1, a3^p = 1, a4^p = 1, a^p = 1, a1^p = a4>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 2*p^2);
   Append(~MuTlist, p^3);
   
   return Glist, Tlist, Nlist, MuGlist, MuTlist;
end function;
   
for p in PrimesInInterval (5, 13) do 
   "\nprocess p = ", p;
   L := Table3Phi9(p);

   Glist, Tlist, Nlist, MuGlist, MuTlist := Check9(L, p);

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

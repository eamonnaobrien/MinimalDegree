// exceptional groups from Phi17 

NonQuadraticResidue := function (p)
   for x in GF (p) do
      if not IsPower (x, 2) then return x; end if;
   end for;
end function;
   
Table3Phi17 := function(p)
   Z := Integers ();
   nu := Z ! (NonQuadraticResidue (p)); // nu
   
   F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
   Alpha := [a3, a4, a5, a6];
   Beta := [a1, a2];
   
   // common relations, typically commutators
   Comms := [
   (a3, a4) = 1, (a3, a5)= 1, (a3, a6) = a1,
   (a4, a5) = a2, (a4, a6)= 1, (a5, a6)= a3,  
   (a1, a2) = 1, a1^p = 1, a2^p = 1] cat
   &cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..4]]: i in [1..2]]);
   
   L := [];
   
   // G17, 1
   G := quo <F | Comms, a3^p = a4^p = a5^p = a6^p = 1>;
   Append (~L, G);
   
   // G17, 2
   G := quo <F | Comms, a3^p = a4^p = a5^p = 1,
   a6^p = a1>;
   Append (~L, G);
   
   // G17, 6
   G := quo <F | Comms, a3^p = a4^p = a6^p = 1, a5^p = a2>;
   Append (~L, G);
   
   // G17, 12
   G := quo <F | Comms, a3^p = a5^p = a6^p = 1, a4^p = a2>;
   Append (~L, G);
   
   // G17, 16
   G := quo <F | Comms, a3^p = a4^p = 1, a5^p = a2, a6^p = a1>;
   Append (~L, G);
   
   // G17, 21
   G := quo <F | Comms, a3^p = a5^p = 1, a4^p = a2, a6^p = a1>;
   Append (~L, G);
   
   return L;
end function;
   
Check17 := function(L, p)
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
   
   // G(17, 1)
   count := count+1;
   F := L[count];
   Alpha := [F.3, F.4, F.5, F.6]; Beta:= [F.1, F.2];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.1*F.2 ) >;
   Append(~Nlist, N1);
   
   // Q is phi_7(1^5)
   Q := Group < a, a1, a2, a3, b | (a1, a) = a2, (a2, a) = a3,
               (b, a) = 1, (a3, a) = 1, (a1, a2) = 1, (a1, b)= a3, 
              (a1, a3) = 1, (a2, a3) = 1, (a2, b) = 1, (a3, b) = 1, 
              a2^p = 1, a3^p = 1, a^p = 1, a1^p = 1, b^p = 1>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 2*p^2);
   Append(~MuTlist, p^3);
   
   // G(17, 2)
   count := count+1;
   F := L[count];
   Alpha := [F.3, F.4, F.5, F.6]; Beta:= [F.1, F.2];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.1*F.2 ) >;
   Append(~Nlist, N1);
   
   // Q is phi_7(2111)a
   Q := Group < a, a1, a2, a3, b | (a1, a) = a2, (a2, a) = a3,
               (b, a) = 1, (a3, a) = 1, (a1, a2) = 1, (a1, b)= a3, 
              (a1, a3) = 1, (a2, a3) = 1, (a2, b) = 1, (a3, b) = 1, 
              a2^p = 1, a3^p = 1, a^p = a3, a1^p = 1, b^p = 1>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 2*p^2);
   Append(~MuTlist, p^3);
   
   // G(17, 6)
   count := count+1;
   F := L[count];
   Alpha := [F.3, F.4, F.5, F.6]; Beta:= [F.1, F.2];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.1*F.2 ) >;
   Append(~Nlist, N1);
   
   if IsPower(K!(p-1),2) eq true then
      // Q is phi_7(2111)b_1
      Q := Group < a, a1, a2, a3, b | (a1, a) = a2, (a2, a) = a3,
               (b, a) = 1, (a3, a) = 1, (a1, a2) = 1, (a1, b)= a3, 
              (a1, a3) = 1, (a2, a3) = 1, (a2, b) = 1, (a3, b) = 1, 
              a2^p = 1, a3^p = 1, a^p = 1, a1^p = a3, b^p = 1>;
      B := pQuotient (Q, p, 5);
      Append(~Tlist, B);
   else 
      // Q is phi_7(2111)b_nu
      Q := Group < a, a1, a2, a3, b | (a1, a) = a2, (a2, a) = a3,
               (b, a) = 1, (a3, a) = 1, (a1, a2) = 1, (a1, b)= a3, 
              (a1, a3) = 1, (a2, a3) = 1, (a2, b) = 1, (a3, b) = 1, 
              a2^p = 1, a3^p = 1, a^p = 1, a1^p = a3^(nu), b^p = 1>;
      B := pQuotient (Q, p, 5);
      Append(~Tlist, B);
   end if;
   
   Append(~MuGlist, 2*p^2);
   Append(~MuTlist, p^3);
   
   // G(17, 12)
   count := count+1;
   F := L[count];
   Alpha := [F.3, F.4, F.5, F.6]; Beta:= [F.1, F.2];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.1*F.2 ) >;
   Append(~Nlist, N1);
   
   // Q is phi_7(2111)c
   Q := Group < a, a1, a2, a3, b | (a1, a) = a2, (a2, a) = a3,
                (b, a) = 1, (a3, a) = 1, (a1, a2) = 1, (a1, b)= a3, 
               (a1, a3) = 1, (a2, a3) = 1, (a2, b) = 1, (a3, b) = 1, 
               a2^p = 1, a3^p = 1, a^p = 1, a1^p = 1, b^p = a3>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 2*p^2);
   Append(~MuTlist, p^3);
   
   // G(17, 16)
   count := count+1;
   F := L[count];
   Alpha := [F.3, F.4, F.5, F.6]; Beta:= [F.1, F.2];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.1*F.2 ) >;
   Append(~Nlist, N1);
   
   if IsPower(K!(p-1),2) eq true then
      // Q is phi_7(2111)b_1
      Q := Group < a, a1, a2, a3, b | (a1, a) = a2, (a2, a) = a3,
                   (b, a) = 1, (a3, a) = 1, (a1, a2) = 1, (a1, b)= a3, 
                  (a1, a3) = 1, (a2, a3) = 1, (a2, b) = 1, (a3, b) = 1, 
                  a2^p = 1, a3^p = 1, a^p = 1, a1^p = a3, b^p = 1>;
      B := pQuotient (Q, p, 5);
      Append(~Tlist, B);
   else 
      // Q is phi_7(2111)b_nu
      Q := Group < a, a1, a2, a3, b | (a1, a) = a2, (a2, a) = a3,
                  (b, a) = 1, (a3, a) = 1, (a1, a2) = 1, (a1, b)= a3, 
                 (a1, a3) = 1, (a2, a3) = 1, (a2, b) = 1, (a3, b) = 1, 
                 a2^p = 1, a3^p = 1, a^p = 1, a1^p = a3^(nu), b^p = 1>;
      B := pQuotient (Q, p, 5);
      Append(~Tlist, B);
   end if;
   
   Append(~MuGlist, 2*p^2);
   Append(~MuTlist, p^3);
   
   // G(17, 21)
   count := count+1;
   F := L[count];
   Alpha := [F.3, F.4, F.5, F.6]; Beta:= [F.1, F.2];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.1*F.2 ) >;
   Append(~Nlist, N1);
   
   // Q is phi_7(2111)c
   Q := Group < a, a1, a2, a3, b | (a1, a) = a2, (a2, a) = a3,
               (b, a) = 1, (a3, a) = 1, (a1, a2) = 1, (a1, b)= a3, 
              (a1, a3) = 1, (a2, a3) = 1, (a2, b) = 1, (a3, b) = 1, 
              a2^p = 1, a3^p = 1, a^p = 1, a1^p = 1, b^p = a3>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 2*p^2);
   Append(~MuTlist, p^3);
   
   return Glist, Tlist, Nlist, MuGlist, MuTlist;
end function;

for p in PrimesInInterval (5, 13) do 
   "\nprocess p = ", p;
   L := Table3Phi17(p);

   Glist, Tlist, Nlist, MuGlist, MuTlist := Check17(L, p);

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

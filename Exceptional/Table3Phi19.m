// exceptional groups from Phi19

NonQuadraticResidue := function (p)
   for x in GF (p) do
      if not IsPower (x, 2) then return x; end if;
   end for;
end function;
   
Table3Phi19 := function(p)

   K := GF(p);
   w := PrimitiveRoot(p);
   
   Z := Integers ();
   nu := Z ! (NonQuadraticResidue (p)); // nu
   
   F<a, a1, a2, b, b1, b2> := FreeGroup (6);
   Alpha := [a, a1, a2, b];
   Beta := [b1, b2];
   
   // common relations, typically commutators
   Comms := [
   (a, a1) = b1, (a, a2)= 1, (a, b) = 1,
   (a1, a2) = b, (b, a1)= b1, (b, a2)= b2,  
   (b1, b2) = 1, b1^p = 1, b2^p = 1] cat
   &cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..4]]: i in [1..2]]);
   
   L := [];
   
   // (2211)a
   G := quo <F | Comms, a^p = b^p = 1, a1^p = b1, a2^p = b2>;
   Append (~L, G);
   
   // (2211)b_r
   for r in [1..(p-1) div 2] do
       G := quo <F | Comms, a^p = b^p = 1, a1^p = b1, a2^p = b2^(w^r mod p)>;
       Append (~L, G);
   end for;
   
   // (21^4)a
   G := quo <F | Comms, a^p = b^p = 1, a1^p = b1, a2^p = 1>;
   Append (~L, G);
   
   // (1^6)
   G := quo <F | Comms, a^p = 1, b^p  = 1, a1^p = 1, a2^p = 1>;
   Append (~L, G);
   
   return L;
end function;
   
Check19 := function(L, p)
   
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
   
   // (2211)a
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4]; Beta:= [F.5, F.6];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.5*F.6 ) >;
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
   
   // (2211)b_r
   for r in [1..(p-1) div 2] do
      count := count+1;
      F := L[count];
      Alpha := [F.1, F.2, F.3, F.4]; Beta:= [F.5, F.6];
      G1, phi := pQuotient(F, p, 6);
      Append(~Glist, G1);
      N1 := sub<G1 | phi( F.5*F.6^r ) >;
      Append(~Nlist, N1);
      A1 := quo< G1 | N1>;
      for s in [1, nu] do
         // Q is phi_7(2111)b_s
         Q := Group < a, a1, a2, a3, b | (a1, a) = a2, (a2, a) = a3,
                      (b, a) = 1, (a3, a) = 1, (a1, a2) = 1, (a1, b)= a3, 
                      (a1, a3) = 1, (a2, a3) = 1, (a2, b) = 1, (a3, b) = 1, 
                      a2^p = 1, a3^p = 1, a^p = 1, a1^p = a3^(s), b^p = 1>;
         B := pQuotient (Q, p, 5);
         if IsIsomorphic(A1, B) then Append(~Tlist, B); break; end if;
      end for;
      Append(~MuGlist, 2*p^2);
      Append(~MuTlist, p^3);
   end for;
   
   // (21^4)a
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4]; Beta:= [F.5, F.6];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.5*F.6 ) >;
   Append(~Nlist, N1);
   
   if IsPower(K!(p-1),2) eq true then
      // Q is phi_7(2111)b_n1
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
   
   // (1^6)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4]; Beta:= [F.5, F.6];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.5*F.6 ) >;
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
   
   return Glist, Tlist, Nlist, MuGlist, MuTlist;
end function;

for p in PrimesInInterval (5, 13) do 
   "\nprocess p = ", p;
   L := Table3Phi19(p);

   Glist, Tlist, Nlist, MuGlist, MuTlist := Check19(L, p);

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

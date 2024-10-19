// exceptional groups from Phi6

NonQuadraticResidue := function (p)
   for x in GF (p) do
       if not IsPower (x, 2) then return x; end if;
   end for;
end function;
   
My6A := function(p)
   Z := Integers ();
   nu := Z ! (NonQuadraticResidue (p)); // nu
   
   F<a1, a2, a3, a4, a5, b1, b2> := FreeGroup (7);
   Alpha := [a1, a2, a3, a4, a5];
   Beta := [b1, b2];
   
   // common relations, typically commutators
   Comms := [
   (a2, a3) = 1, (a2, a4)= 1, (a3, a4) = a1,
   (a4, a5) = a3, (a3, a5) = a2, (a2, a5) = 1, a1 = b1^p,
   a2 = b2, (b1, b2) = 1] cat
   &cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..5]]: i in [1..2]]);
   
   L := [];
   
   // G6, 4
   G := quo <F | Comms, a3^p = a5^p = b1^(p^2) = b2^p = 1, a4^p = b1>;
   Append (~L, G);
   
   // G6, 7r
   for r in [1..(p-1)] do
      G := quo <F | Comms, a3^p = b1^(p^2) = b2^p = 1, a4^p = b1^r, a5^p = b2>;
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
   (a4, a5) = a3, (a3, a5) = a2, (a2, a5) = 1, a1 = b1, a2 = b2] cat
   &cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..5]]: i in [1..3]])
   cat &cat([[(Beta[i], Beta[j]) = Id(F) : j in [i + 1..3]]: i in [1..3]]);
   
   L := [];
   
   // G6, 9
   G := quo <F | Comms, a3^p = a4^p = b1^p = b2^p = b3^p = 1, a5^p = b3>;
   Append (~L, G);
   
   // G6, 10
   G := quo <F | Comms, a3^p = a4^p = b1^p = b2^p = b3^p = 1, a5^p = b2>;
   Append (~L, G);
   
   // G6, 12r
   for r in [1,nu] do
      G := quo <F | Comms, a3^p = b1^p = b2^p = b3^p = 1, a4^p = b2^r, a5^p = b3>;
      Append (~L, G);
   end for;
   
   // G6, 13
   G := quo <F | Comms, a3^p = b1^p = b2^p = b3^p = 1, a4^p = b1, a5^p = b3>;
   Append (~L, G);
   
   // G6, 15
   G := quo <F | Comms, a3^p = b1^p = b2^p = b3^p = 1, a4^p = b2, a5^p = b1>;
   Append (~L, G);
   
   // G6, 16r
   for r in [1..(p-3) div 2] do
      G := quo <F | Comms, a3^p = b1^p = b2^p = b3^p = 1,
                    a4^p = b1^(w^r mod p), a5^p = b2>;
      Append (~L, G);
   end for;
   
   return L;
end function;
   
Table3Phi6 := function(p)
   return My6A(p) cat My6B(p);
end function;
   
Check6 := function(L, p)
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
   
   // G(6, 4)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.6^(p)*F.7^(-1) ) >;
   Append(~Nlist, N1);
   
   // Q is phi_3(311)b_1
   Q := Group < a, a1, a2, a3 | (a1, a) = a2, (a2, a) = a3, (a1, a2) = 1, 
                (a, a3) = 1, (a1, a3) = 1, (a2, a3) = 1,
                a2^p = 1, a3^p = 1, a^p = 1, a1^(p^2) = a3>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, p^3 + p^2);
   Append(~MuTlist, p^4);
   
   // G(6, 7r)
   for r in [1..(p-1)] do
      count := count+1;
      F := L[count];
      Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7];
      G1, phi := pQuotient(F, p, 6);
      Append(~Glist, G1);
      N1 := sub<G1 | phi( F.6^(r*p)*F.7^(-1) ) >;
      Append(~Nlist, N1);
   
      // Q is phi_3(311)b_1
      Q := Group < a, a1, a2, a3 | (a1, a) = a2, (a2, a) = a3, (a1, a2) = 1, 
                   (a, a3) = 1, (a1, a3) = 1, (a2, a3) = 1,
                   a2^p = 1, a3^p = 1, a^p = 1, a1^(p^2) = a3>;
      B := pQuotient (Q, p, 5);
      Append(~Tlist, B);
   
      Append(~MuGlist, p^3 + p^2);
      Append(~MuTlist, p^4);
   end for;
   
   // G(6, 9)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7, F.8];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.6*F.8^(-1) ) >;
   Append(~Nlist, N1);
   
   // Q is phi_6(2111)b_1
   Q := Group < a1, a2, b, b1, b2 | (a1, a2) = b, (b, a1) = b1,
               (b, a2) = b2, (b1, b2) = 1, (a1, b1) = 1, (a1, b2) = 1, 
               (a2, b1) = 1, (a2, b2) = 1, (b, b1) = 1, (b, b2) = 1,
               b^p = 1, b1^p = 1, b2^p = 1, a1^p = 1, a2^p = b1>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 3*p^2);
   Append(~MuTlist, p^3 + p^2);
   
   // G(6, 10)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7, F.8];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.6*F.7^(-1) ) >;
   Append(~Nlist, N1);
   
   if IsPower(K!(p-1),2) eq true then
      // Q is phi_3(2111)b_1
      Q := Group < a, a1, a2, a3, ga | (a1, a) = a2, (a2, a) = a3, (a1, a2) = 1, 
                  (a, ga) = 1, (a1, ga) = 1, (a2, ga) = 1, (a, a3) = 1, 
                  (a1, a3) = 1, (a2, a3) = 1, (a3, ga) = 1,
                  a2^p = 1, a3^p = 1, a^p = 1, a1^(p) = a3, ga^p = 1>;
      B := pQuotient (Q, p, 5);
      Append(~Tlist, B);
   else 
      // Q is phi_3(2111)b_nu
      Q := Group < a, a1, a2, a3, ga | (a1, a) = a2, (a2, a) = a3, (a1, a2) = 1, 
                  (a, ga) = 1, (a1, ga) = 1, (a2, ga) = 1, (a, a3) = 1, 
                  (a1, a3) = 1, (a2, a3) = 1, (a3, ga) = 1,
                  a2^p = 1, a3^p = 1, a^p = 1, a1^(p) = a3^(nu), ga^p = 1>;
      B := pQuotient (Q, p, 5);
      Append(~Tlist, B);
   end if;
   
   Append(~MuGlist, 2*p^2 + p);
   Append(~MuTlist, p^3 + p);
   
   // G(6, 12r), r = 1, nu and p = 3 mod 4
   for r in [1, nu] do
      if IsPower(K!(p-1),2) eq false then
         count := count+1;
         F := L[count];
         Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7, F.8];
         G1, phi := pQuotient(F, p, 6);
         Append(~Glist, G1);
         N1 := sub<G1 | phi( F.6*F.8^(r) ) >;
         Append(~Nlist, N1);
   
         // Q is phi_6(221)d_0
         Q := Group < a1, a2, b, b1, b2 | (a1, a2) = b, (b, a1) = b1,
                      (b, a2) = b2, (b1, b2) = 1, (a1, b1) = 1, (a1, b2) = 1, 
                      (a2, b1) = 1, (a2, b2) = 1, (b, b1) = 1, (b, b2) = 1,
                      b^p = 1, b1^p = 1, b2^p = 1, a1^p = b2, a2^p = b1^nu>;
         B := pQuotient (Q, p, 5);
         Append(~Tlist, B);
   
         Append(~MuGlist, 3*p^2);
         Append(~MuTlist, 2*p^3);
      end if;
   end for;
   
   // G(6, 12r), r = 1 and p = 1 mod 4
   for r in [1] do
      if IsPower(K!(p-1),2) eq true then
         count := count+1;
         F := L[count];
         Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7, F.8];
         G1, phi := pQuotient(F, p, 6);
         Append(~Glist, G1);
         N1 := sub<G1 | phi( F.6*F.8^(nu) ) >;
         Append(~Nlist, N1);
  
         // Q is phi_6(221)d_0
         Q := Group < a1, a2, b, b1, b2 | (a1, a2) = b, (b, a1) = b1,
                      (b, a2) = b2, (b1, b2) = 1, (a1, b1) = 1, (a1, b2) = 1, 
                      (a2, b1) = 1, (a2, b2) = 1, (b, b1) = 1, (b, b2) = 1,
                      b^p = 1, b1^p = 1, b2^p = 1, a1^p = b2, a2^p = b1^nu>;
         B := pQuotient (Q, p, 5);
         Append(~Tlist, B);
   
         Append(~MuGlist, 3*p^2);
         Append(~MuTlist, 2*p^3);
      end if;
   end for;
   
   // G(6, 12r), r = nu and p = 1 mod 4
   for r in [nu] do
      if IsPower(K!(p-1),2) eq true then
         count := count+1;
         F := L[count];
         Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7, F.8];
         G1, phi := pQuotient(F, p, 6);
         Append(~Glist, G1);
         N1 := sub<G1 | phi( F.6*F.8 ) >;
         Append(~Nlist, N1);
   
         // Q is phi_6(221)d_0
         Q := Group < a1, a2, b, b1, b2 | (a1, a2) = b, (b, a1) = b1,
                      (b, a2) = b2, (b1, b2) = 1, (a1, b1) = 1, (a1, b2) = 1, 
                      (a2, b1) = 1, (a2, b2) = 1, (b, b1) = 1, (b, b2) = 1,
                      b^p = 1, b1^p = 1, b2^p = 1, a1^p = b2, a2^p = b1^nu>;
         B := pQuotient (Q, p, 5);
         Append(~Tlist, B);
   
         Append(~MuGlist, 3*p^2);
         Append(~MuTlist, 2*p^3);
      end if;
   end for;
   
   // G(6, 13)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7, F.8];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.6*F.7^(-1)*F.8 ) >;
   Append(~Nlist, N1);
   
   if IsPower(K!(p-1),2) eq true then
      // Q is phi_6(221)c_1
      Q := Group < a1, a2, b, b1, b2 | (a1, a2) = b, (b, a1) = b1,
                   (b, a2) = b2, (b1, b2) = 1, (a1, b1) = 1, (a1, b2) = 1, 
                   (a2, b1) = 1, (a2, b2) = 1, (b, b1) = 1, (b, b2) = 1,
                   b^p = 1, b1^p = 1, b2^p = 1, a1^(4*p) = b2^(-1), a2^p = b1*b2>;
      B := pQuotient (Q, p, 5);
      Append(~Tlist, B);
   else
      // Q is phi_6(221)c_nu
      Q := Group < a1, a2, b, b1, b2 | (a1, a2) = b, (b, a1) = b1,
                  (b, a2) = b2, (b1, b2) = 1, (a1, b1) = 1, (a1, b2) = 1, 
                  (a2, b1) = 1, (a2, b2) = 1, (b, b1) = 1, (b, b2) = 1, b^p = 1, 
                  b1^p = 1, b2^p = 1, a1^(4*p) = b2^(-nu), a2^p = b1^(nu)*b2^(nu)>;
      B := pQuotient (Q, p, 5);
      Append(~Tlist, B);
   end if;
   
   Append(~MuGlist, 3*p^2);
   Append(~MuTlist, p^3 + p^2);
   
   // G(6, 15)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7, F.8];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.7 ) >;
   Append(~Nlist, N1);
   
   if IsPower(K!(p-1),2) eq true then
      // Q is phi_3(2111)b_1
      Q := Group < a, a1, a2, a3, ga | (a1, a) = a2, (a2, a) = a3, (a1, a2) = 1, 
                   (a, ga) = 1, (a1, ga) = 1, (a2, ga) = 1, (a, a3) = 1, 
                   (a1, a3) = 1, (a2, a3) = 1, (a3, ga) = 1,
                   a2^p = 1, a3^p = 1, a^p = 1, a1^(p) = a3, ga^p = 1>;
      B := pQuotient (Q, p, 5);
      Append(~Tlist, B);
   else
      // Q is phi_3(2111)b_nu
      Q := Group < a, a1, a2, a3, ga | (a1, a) = a2, (a2, a) = a3, (a1, a2) = 1, 
                  (a, ga) = 1, (a1, ga) = 1, (a2, ga) = 1, (a, a3) = 1, 
                  (a1, a3) = 1, (a2, a3) = 1, (a3, ga) = 1,
                  a2^p = 1, a3^p = 1, a^p = 1, a1^(p) = a3^nu, ga^p = 1>;
      B := pQuotient (Q, p, 5);
      Append(~Tlist, B);
   end if;
   
   Append(~MuGlist, 2*p^2 + p);
   Append(~MuTlist, p^3 + p);
   
   // G(6, 16r)
   for r in [1..(p-3) div 2] do
      count := count+1;
      F := L[count];
      Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7, F.8];
      G1, phi := pQuotient(F, p, 6);
      Append(~Glist, G1);
      N1 := sub<G1 | phi( F.6^(-r)*F.7 ) >;
      Append(~Nlist, N1);
   
      A1 := quo< G1 | N1>;
      for s in [1, nu] do
         // Q is phi_3(2111)b_s
         Q := Group < a, a1, a2, a3, ga | (a1, a) = a2, (a2, a) = a3, (a1, a2) = 1, 
                     (a, ga) = 1, (a1, ga) = 1, (a2, ga) = 1, (a, a3) = 1, 
                     (a1, a3) = 1, (a2, a3) = 1, (a3, ga) = 1,
                     a2^p = 1, a3^p = 1, a^p = 1, a1^(p) = a3^(s), ga^p = 1>;
         B := pQuotient (Q, p, 5);
         if IsIsomorphic(A1, B) then Append(~Tlist, B); break;
         end if;
      end for;
      Append(~MuGlist, 2*p^2 + p);
      Append(~MuTlist, p^3 + p);
   end for;
   
   return Glist, Tlist, Nlist, MuGlist, MuTlist;
end function;

for p in PrimesInInterval (5, 13) do 
   "\nprocess p = ", p;
   L := Table3Phi6(p);

   Glist, Tlist, Nlist, MuGlist, MuTlist := Check6(L, p);

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

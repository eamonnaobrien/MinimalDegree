// exceptional groups from Phi11

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

Table3Phi11 := function(p)
   w := PrimitiveRoot(p);
   
   K := GF(p);
   
   Z := Integers ();
   nu := Z ! (NonQuadraticResidue (p)); // nu
   
   F<a1, a2, a3, a4, a5, a6> := FreeGroup (6);
   Alpha := [a4, a5, a6];
   Beta := [a1, a2, a3];
   
   // common relations, typically commutators
   Comms := [
   (a4, a5) = a1, (a5, a6) = a3, (a4, a6) = a2] cat
   &cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..3]]: i in [1..3]])
   cat &cat([[(Beta[i], Beta[j]) = Id(F) : j in [i + 1..3]]: i in [1..3]]);
   
   L := [];
   
   // G11, 3
   G := quo <F | Comms, a1^p = a2^p = a3^p = a4^p = 1, a5^p = a2, a6^p = a1>;
   Append (~L, G);
   
   // G11, 5
   G := quo <F | Comms, a1^p = a2^p = a3^p = 1, a4^p = a3, a5^p = a2^-1, a6^p = a1>;
   Append (~L, G);
   
   // G11, 8
   G := quo <F | Comms, a1^p = a2^p = a3^p = a4^p = 1, a5^p = a1*a2, a6^p = a1*a2>;
   Append (~L, G);
   
   // G11, 9r
   for r in [2..(p-1) div 2] do
      G := quo <F | Comms, a1^p = a2^p = a3^p = a4^p = 1, a5^p = a1*a2^r, a6^p = a1^r*a2>;
      Append (~L, G);
   end for;
   
   // G11, 11
   G := quo <F | Comms, a1^p = a2^p = a3^p = 1, a4^p = a1, a5^p = a1, a6^p = a2*a3>;
   Append (~L, G);
   
   // G11, 12
   G := quo <F | Comms, a1^p = a2^p = a3^p = 1, a4^p = a1, a5^p = a1*a2, a6^p = a2*a3>;
   Append (~L, G);
   
   // G11, 14r (r = 1 and p = 1 mod 4)
   for r in [1] do
      if IsPower(K!(p-1),2) eq true then
         G := quo <F | Comms, a1^p = a2^p = a3^p = 1, a4^p = a3^r, a5^p = a1, a6^p = a1*a2>;
         Append (~L, G);
      end if;
   end for;
   
   // G11, 14r (r = nu and p = 3 mod 4)
   for r in [nu] do
      if IsPower(K!(p-1),2) eq false then
         G := quo <F | Comms, a1^p = a2^p = a3^p = 1, a4^p = a3^r, a5^p = a1, a6^p = a1*a2>;
         Append (~L, G);
      end if;
   end for;
   
   // G11, 15
   G := quo <F | Comms, a1^p = a2^p = a3^p = 1, a4^p = a3, a5^p = a1*a2, a6^p = a1*a2>;
   Append (~L, G);
   
   // G11, 16r
   for r in [2..(p-1) div 2] do
      G := quo <F | Comms, a1^p = a2^p = a3^p = 1,
                  a4^p = a3, a5^p = a1*a2^r, a6^p = a1^r*a2>;
      Append (~L, G);
   end for;
   
   // G11, 17r
   for r in [1..(p-1) div 2] do
      G := quo <F | Comms, a1^p = a2^p = a3^p = 1,
                  a4^p = a3, a5^p = a1*a2^(nu*r), a6^p = a1^r*a2>;
      Append (~L, G);
   end for;
   
   return L;
end function;
   
Check11 := function(L, p)
   
   w := PrimitiveRoot(p);
   
   K := GF(p);
   
   Z := Integers ();
   nu := Z ! (NonQuadraticResidue (p)); // nu
   
   PairPhi4 := function(s, p)
      for x in GF(p) do
         if 4*x eq (w^(2*s + 1) - 1) mod p and x ne 0 then
           return Z!x;
         end if;
      end for;
   end function;
   
   Glist := [];
   Tlist := [];
   Nlist := [];
   MuGlist := [];
   MuTlist := [];
   
   count := 0;
   
   // (11, 3) 
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3]; Beta:= [F.4, F.5, F.6];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.1 ) >;
   Append(~Nlist, N1);
   
   // Q is phi_4(2111)c
   Q := Group < a, a1, a2, b1, b2 | (a1, a) = b1, (a2, a) = b2,
               (b1, a) = 1, (b2, a) = 1, (a1, a2) = 1, (a1, b1) = 1, 
               (a1, b2) = 1, (a2, b1) = 1, (a2, b2) = 1, (b1, b2) = 1,  
               a2^p = b1, a^p = 1, a1^p = 1, b1^p = 1, b2^p = 1>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 3*p^2);
   Append(~MuTlist, p^3+p^2);
   
   // (11, 5) 
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3]; Beta:= [F.4, F.5, F.6];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.1*F.2^(-1) ) >;
   Append(~Nlist, N1);
   
   // Q is phi_4(221)f_0
   Q := Group < a, a1, a2, b1, b2 | (a1, a) = b1, (a2, a) = b2,
               (b1, a) = 1, (b2, a) = 1, (a1, a2) = 1, (a1, b1) = 1, 
               (a1, b2) = 1, (a2, b1) = 1, (a2, b2) = 1, (b1, b2) = 1,  
               a2^p = b1^(nu), a^p = 1, a1^p = b2, b1^p = 1, b2^p = 1>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 3*p^2);
   Append(~MuTlist, 2*p^3);
   
   // (11, 8) 
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3]; Beta:= [F.4, F.5, F.6];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.1 ) >;
   Append(~Nlist, N1);
   
   // Q is phi_4(2111)c
   Q := Group < a, a1, a2, b1, b2 | (a1, a) = b1, (a2, a) = b2,
               (b1, a) = 1, (b2, a) = 1, (a1, a2) = 1, (a1, b1) = 1, 
               (a1, b2) = 1, (a2, b1) = 1, (a2, b2) = 1, (b1, b2) = 1,  
               a2^p = b1, a^p = 1, a1^p = 1, b1^p = 1, b2^p = 1>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 3*p^2);
   Append(~MuTlist, p^3+p^2);
   
   // (11, 9r) 
   for r in [2..(p-1) div 2] do
      count := count+1;
      F := L[count];
      Alpha := [F.1, F.2, F.3]; Beta:= [F.4, F.5, F.6];
      G1, phi := pQuotient(F, p, 6);
      Append(~Glist, G1);
      N1 := sub<G1 | phi( F.1*F.2^r ) >;
      Append(~Nlist, N1);
   
      // Q is phi_4(2111)c
      Q := Group < a, a1, a2, b1, b2 | (a1, a) = b1, (a2, a) = b2,
                  (b1, a) = 1, (b2, a) = 1, (a1, a2) = 1, (a1, b1) = 1, 
                  (a1, b2) = 1, (a2, b1) = 1, (a2, b2) = 1, (b1, b2) = 1,  
                  a2^p = b1, a^p = 1, a1^p = 1, b1^p = 1, b2^p = 1>;
      B := pQuotient (Q, p, 5);
      Append(~Tlist, B);
      Append(~MuGlist, 3*p^2);
      Append(~MuTlist, p^3+p^2);
   end for;
   
   // (11, 11) 
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3]; Beta:= [F.4, F.5, F.6];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.1*F.3 ) >;
   Append(~Nlist, N1);
   
   // Q is G_46 (Girnat)
   Q := Group < g1, g2, g3, g4, g5 | (g2, g1) = g4*g5, (g3, g1)= g5, 
               (g4, g1) = 1, (g5, g1) = 1, (g2, g3) = 1, (g2, g4) = 1,
               (g2, g5) = 1, (g3, g4) = 1, (g3, g5) = 1, (g4, g5) = 1, 
               g1^p = 1, g2^p = g4, g3^p = g5, g4^p = 1, g5^p = 1>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   Append(~MuGlist, 3*p^2);
   Append(~MuTlist, p^3+p^2);
   
   // (11, 12) 
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3]; Beta:= [F.4, F.5, F.6];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.1*F.3 ) >;
   Append(~Nlist, N1);
   
   A1 := quo< G1 | N1>;
   for s in [1..(p-1) div 2] do
      x := PairPhi4 (s, p);
   
      // Q is phi_4(221)f_r
      Q := Group < a, a1, a2, b1, b2 | (a1, a) = b1, (a2, a) = b2,
               (b1, a) = 1, (b2, a) = 1, (a1, a2) = 1, (a1, b1) = 1, 
               (a1, b2) = 1, (a2, b1) = 1, (a2, b2) = 1, (b1, b2) = 1,  
               a2^p = b1*b2, a^p = 1, a1^p = b2^x, b1^p = 1, b2^p = 1>;
      B := pQuotient (Q, p, 5);
      if IsIsomorphic(A1, B) then Append(~Tlist, B); break; end if;
   end for;
   
   Append(~MuGlist, 3*p^2);
   Append(~MuTlist, 2*p^3);
   
   // (11, 14r) r = 1 and p=1 mod 4
   if IsPower(K!(p-1),2) eq true then
      count := count+1;
      F := L[count];
      Alpha := [F.1, F.2, F.3]; Beta:= [F.4, F.5, F.6];
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
      Append(~MuGlist, 3*p^2);
      Append(~MuTlist, p^3+p^2);
   end if;
   
   // (11, 14r) r = nu and p=3 mod 4
   if IsPower(K!(p-1),2) eq false then
      count := count+1;
      F := L[count];
      Alpha := [F.1, F.2, F.3]; Beta:= [F.4, F.5, F.6];
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
      Append(~MuGlist, 3*p^2);
      Append(~MuTlist, p^3+p^2);
   end if;
   
   // (11, 15) 
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3]; Beta:= [F.4, F.5, F.6];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.1*F.2 ) >;
   Append(~Nlist, N1);
   
   // Q is phi_4(2111)c
   Q := Group < a, a1, a2, b1, b2 | (a1, a) = b1, (a2, a) = b2,
                (b1, a) = 1, (b2, a) = 1, (a1, a2) = 1, (a1, b1) = 1, 
                (a1, b2) = 1, (a2, b1) = 1, (a2, b2) = 1, (b1, b2) = 1,  
                a2^p = b1, a^p = 1, a1^p = 1, b1^p = 1, b2^p = 1>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 3*p^2);
   Append(~MuTlist, p^3+p^2);
   
   // (11, 16r) 
   for r in [2..(p-1) div 2] do
      count := count+1;
      F := L[count];
      Alpha := [F.1, F.2, F.3]; Beta:= [F.4, F.5, F.6];
      G1, phi := pQuotient(F, p, 6);
      Append(~Glist, G1);
      N1 := sub<G1 | phi( F.1*F.2 ) >;
      Append(~Nlist, N1);
   
      // Q is phi_4(221)b
      Q := Group < a, a1, a2, b1, b2 | (a1, a) = b1, (a2, a) = b2,
                  (b1, a) = 1, (b2, a) = 1, (a1, a2) = 1, (a1, b1) = 1, 
                 (a1, b2) = 1, (a2, b1) = 1, (a2, b2) = 1, (b1, b2) = 1,  
                 a2^p = b1, a^p = b2, a1^p = 1, b1^p = 1, b2^p = 1>;
      B := pQuotient (Q, p, 5);
      Append(~Tlist, B);
   
      Append(~MuGlist, 3*p^2);
      Append(~MuTlist, p^3+p^2);
   end for;
   
   // (11, 17r) 
   for r in [1..(p-1) div 2] do
      count := count+1;
      F := L[count];
      Alpha := [F.1, F.2, F.3]; Beta:= [F.4, F.5, F.6];
      G1, phi := pQuotient(F, p, 6);
      Append(~Glist, G1);
      N1 := sub<G1 | phi( F.3 ) >;
      Append(~Nlist, N1);
   
      A1 := quo< G1 | N1>;
      for s in [1..(p-1) div 2] do
         x := PairPhi4 (s, p);
   
         // Q is phi_4(221)f_r
         Q := Group < a, a1, a2, b1, b2 | (a1, a) = b1, (a2, a) = b2,
             (b1, a) = 1, (b2, a) = 1, (a1, a2) = 1, (a1, b1) = 1, 
             (a1, b2) = 1, (a2, b1) = 1, (a2, b2) = 1, (b1, b2) = 1,  
             a2^p = b1*b2, a^p = 1, a1^p = b2^x, b1^p = 1, b2^p = 1>;
         B := pQuotient (Q, p, 5);
         if IsIsomorphic(A1, B) then Append(~Tlist, B); break; end if;
      end for;
   
      Append(~MuGlist, 3*p^2);
      Append(~MuTlist, 2*p^3);
   end for;
   return Glist, Tlist, Nlist, MuGlist, MuTlist;
end function;

for p in PrimesInInterval (5, 7) do 
   "\nprocess p = ", p;
   L := Table3Phi11(p);

   Glist, Tlist, Nlist, MuGlist, MuTlist := Check11(L, p);

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

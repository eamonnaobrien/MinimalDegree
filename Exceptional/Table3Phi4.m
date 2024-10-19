// exceptional groups from Phi4

NonQuadraticResidue := function (p)
   for x in GF (p) do
      if not IsPower (x, 2) then return x; end if;
   end for;
end function;
   
My4A := function(p)
   Z := Integers ();
   nu := Z ! (NonQuadraticResidue (p)); // nu
   
   F<a1, a2, a3, a4, a5, b1, b2> := FreeGroup (7);
   Alpha := [a1, a2, a3, a4, a5];
   Beta := [b1, b2];
   
   // common relations, typically commutators
   Comms := [
   (a2, a3) = 1, (a2, a4)= 1, (a3, a4) = 1,
   (a4, a5) = a2, (a3, a5) = a1, (a2, a5) = 1, a1 = b1^p,
   a2 = b2, (b1, b2) = 1] cat
   &cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..5]]: i in [1..2]]);
   
   L := [];
   
   // G4, 2
   G := quo <F | Comms, a4^p = a5^p = b1^(p^2) = b2^p = 1, a3^p = b1>;
   Append (~L, G);
   
   // G4, 8r
   for r in [1..(p-1)] do
       G := quo <F | Comms,   a5^p = b1^(p^2) = b2^p = 1, a3^p = b1^r, a4^p = b2>;
       Append (~L, G);
   end for;
   
   // G4, 10
   G := quo <F | Comms, a4^p = b1^(p^2) = b2^p = 1, a3^p = b1, a5^p = b2>;
   Append (~L, G);
   
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
   
   // G4, 16
   G := quo <F | Comms, a3^p =  b1^p = b2^p = b3^p = 1, a4^p = b2, a5^p = b1>;
   Append (~L, G);
   
   // G4, 17
   G := quo <F | Comms, a3^p = a5^p= b1^p = b2^p = b3^p = 1, a4^p = b2>;
   Append (~L, G);
   
   // G4, 21r
   for r in [1..(p-3) div 2] do
      G := quo <F | Comms, a5^p =  b1^p = b2^p = b3^p = 1, 
                    a3^p = b1^(w^r mod p), a4^p = b2>;
   Append (~L, G);
   end for;
   
   // G4, 22
   G := quo <F | Comms, a5^p =  b1^p = b2^p = b3^p = 1, a3^p = b2, a4^p = b1>;
   Append (~L, G);
   
   // G4, 27
   G := quo <F | Comms, a3^p =  b1^p = b2^p = b3^p = 1, a4^p = b2, a5^p = b3>;
   Append (~L, G);
   
   // G4, 30r
   for r in [1..(p-3) div 2] do
      G := quo <F | Comms,  b1^p = b2^p = b3^p = 1, a3^p = b1^(w^r mod p), 
                    a4^p = b2, a5^p = b3>;
      Append (~L, G);
   end for;
   
   // G4, 31
   G := quo <F | Comms,  b1^p = b2^p = b3^p = 1, a3^p =  b2, a4^p = b1, a5^p = b3>;
   Append (~L, G);
   
   // G4, 35
   G := quo <F | Comms, a3^p =  b1^p = b2^p = b3^p = 1, a4^p = b3, a5^p = b3>;
   Append (~L, G);
   
   // G4, 36
   G := quo <F | Comms, a3^p =  b1^p = b2^p = b3^p = 1, a4^p = b3*b2, a5^p = b3>;
   Append (~L, G);
   
   // G4, 37
   G := quo <F | Comms, a3^p =  b1^p = b2^p = b3^p = 1, a4^p = b3*b1, a5^p = b3>;
   Append (~L, G);
   
   // G4, 38
   G := quo <F | Comms,  b1^p = b2^p = b3^p = 1, a3^p = b1, a4^p = b3, a5^p = b3>;
   Append (~L, G);
   
   // G4, 39
   G := quo <F | Comms, a5^p = b3, b1^p = b2^p = b3^p = 1, a3^p = b1, a4^p = b2*b3>;
   Append (~L, G);
   
   // G4, 40
   G := quo <F | Comms,  b1^p = b2^p = b3^p = 1, a3^p = b2, a4^p = b3, a5^p = b3>;
   Append (~L, G);
   
   // G4, 41
   G := quo <F | Comms,  b1^p = b2^p = b3^p = 1, a3^p = b2, a4^p = b1*b3, a5^p = b3>;
   Append (~L, G);
   
   return L;
end function;
   
Table3Phi4 := function(p)
   return My4A(p) cat My4B(p);
end function;
   
Check4 := function(L, p)
   
   w := PrimitiveRoot(p);
   
   Z := Integers ();
   nu := Z ! (NonQuadraticResidue (p)); // nu
   
   Glist := [];
   Tlist := [];
   Nlist := [];
   MuGlist := [];
   MuTlist := [];
   
   count := 0;
   
   // G(4, 2)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.6^(p)*F.7^(-1) ) >;
   Append(~Nlist, N1);
   
   // Q is phi_2(311)b
   Q := Group < a, a1, a2, ga | (a1, a) = a2, (a2, a)= 1,
               (a1, a2) = 1, (a, ga) = 1, (a1, ga) = 1, (a2, ga) = 1,
               a2^p = 1, a^(p) = 1, a1^p = 1, ga^(p^2) = a2>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, p^3 + p^2);
   Append(~MuTlist, p^4);
   
   // G(4, 8r)
   for r in [1..(p-1)] do
      count := count+1;
      F := L[count];
      Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7];
      G1, phi := pQuotient(F, p, 6);
      Append(~Glist, G1);
      N1 := sub<G1 | phi( F.6^(r*p)*F.7^(-1) ) >;
      Append(~Nlist, N1);
   
      // Q is phi_2(311)b
      Q := Group < a, a1, a2, ga | (a1, a) = a2, (a2, a)= 1,
                   (a1, a2) = 1, (a, ga) = 1, (a1, ga) = 1, (a2, ga) = 1,
                   a2^p = 1, a^(p) = 1, a1^p = 1, ga^(p^2) = a2>;
      B := pQuotient (Q, p, 5);
      Append(~Tlist, B);
   
      Append(~MuGlist, p^3 + p^2);
      Append(~MuTlist, p^4);
   end for;
   
   // G(4, 10)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.6^(p)*F.7^(-1) ) >;
   Append(~Nlist, N1);
   
   // Q is phi_2(311)b
   Q := Group < a, a1, a2, ga | (a1, a) = a2, (a2, a)= 1,
                (a1, a2) = 1, (a, ga) = 1, (a1, ga) = 1, (a2, ga) = 1,
                a2^p = 1, a^(p) = 1, a1^p = 1, ga^(p^2) = a2>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, p^3 + p^2);
   Append(~MuTlist, p^4);
   
   // G(4, 16)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7, F.8];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.6*F.7^(-1) ) >;
   Append(~Nlist, N1);
   
   // Q is phi_2(2111)b
   Q := Group < a, a1, a2, b, ga | (a1, a) = a2, (a2, a)= 1,
               (a1, a2) = 1, (b, ga) = 1, (a, ga) = 1, (a1, ga) = 1, 
               (a2, ga) = 1, (a, b) = 1, (a1, b) = 1, (a2, b) = 1, 
               (b, ga) = 1, a2^p = 1, a^(p) = 1, a1^p = 1, b^p = 1, ga^p = a2>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);

   Append(~MuGlist, 2*p^2 + p);
   Append(~MuTlist, p^3 + p);
   
   // G(4, 17)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7, F.8];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.6*F.7^(-1) ) >;
   Append(~Nlist, N1);
   
   // Q is phi_2(2111)b
   Q := Group < a, a1, a2, b, ga | (a1, a) = a2, (a2, a)= 1,
               (a1, a2) = 1, (b, ga) = 1, (a, ga) = 1, (a1, ga) = 1, 
               (a2, ga) = 1, (a, b) = 1, (a1, b) = 1, (a2, b) = 1, 
               (b, ga) = 1, a2^p = 1, a^(p) = 1, a1^p = 1, b^p = 1, ga^p = a2>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 2*p^2 + p);
   Append(~MuTlist, p^3 + p);
   
   // G(4, 21r)
   for r in [1..(p-3) div 2] do
      count := count+1;
      F := L[count];
      Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7, F.8];
      G1, phi := pQuotient(F, p, 6);
      Append(~Glist, G1);
      N1 := sub<G1 | phi( F.6^(w^r mod p)*F.7^(-1) ) >;
      Append(~Nlist, N1);
   
      // Q is phi_2(2111)b
      Q := Group < a, a1, a2, b, ga | (a1, a) = a2, (a2, a)= 1,
                  (a1, a2) = 1, (b, ga) = 1, (a, ga) = 1, (a1, ga) = 1, 
                  (a2, ga) = 1, (a, b) = 1, (a1, b) = 1, (a2, b) = 1, 
                  (b, ga) = 1, a2^p = 1, a^(p) = 1, a1^p = 1, b^p = 1, ga^p = a2>;
      B := pQuotient (Q, p, 5);
      Append(~Tlist, B);
   
      Append(~MuGlist, 2*p^2 + p);
      Append(~MuTlist, p^3 + p);
   end for;
   
   // G(4, 22)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7, F.8];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.7 ) >;
   Append(~Nlist, N1);
   
   // Q is phi_2(2111)b
   Q := Group < a, a1, a2, b, ga | (a1, a) = a2, (a2, a)= 1,
               (a1, a2) = 1, (b, ga) = 1, (a, ga) = 1, (a1, ga) = 1, 
               (a2, ga) = 1, (a, b) = 1, (a1, b) = 1, (a2, b) = 1, 
               (b, ga) = 1, a2^p = 1, a^(p) = 1, a1^p = 1, b^p = 1, ga^p = a2>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 2*p^2 + p);
   Append(~MuTlist, p^3 + p);
   
   // G(4, 27)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7, F.8];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.6*F.7^(-1) ) >;
   Append(~Nlist, N1);
   
   // Q is phi_2(221)c
   Q := Group < a, a1, a2, ga | (a1, a) = a2, (a2, a)= 1,
               (a1, a2) = 1, (a, ga) = 1, (a1, ga) = 1, (a2, ga) = 1,
               a2^p = 1, a^(p^2) = 1, a1^p = 1, ga^(p) = a2>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 3*p^2);
   Append(~MuTlist, p^3 + p^2);
   
   // G(4, 30r)
   for r in [1..(p-3) div 2] do
      count := count+1;
      F := L[count];
      Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7, F.8];
      G1, phi := pQuotient(F, p, 6);
      Append(~Glist, G1);
      N1 := sub<G1 | phi( F.6^(r)*F.7^(-1) ) >;
      Append(~Nlist, N1);
   
      // Q is phi_2(221)c
      Q := Group < a, a1, a2, ga | (a1, a) = a2, (a2, a)= 1,
                  (a1, a2) = 1, (a, ga) = 1, (a1, ga) = 1, (a2, ga) = 1, 
                  a2^p = 1, a^(p^2) = 1, a1^p = 1, ga^(p) = a2>;
      B := pQuotient (Q, p, 5);
      Append(~Tlist, B);
   
      Append(~MuGlist, 3*p^2);
      Append(~MuTlist, p^3 + p^2);
   end for;
   
   // G(4, 31)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7, F.8];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.7 ) >;
   Append(~Nlist, N1);
   
   // Q is phi_2(221)c
   Q := Group < a, a1, a2, ga | (a1, a) = a2, (a2, a)= 1,
               (a1, a2) = 1, (a, ga) = 1, (a1, ga) = 1, (a2, ga) = 1,
               a2^p = 1, a^(p^2) = 1, a1^p = 1, ga^(p) = a2>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 3*p^2);
   Append(~MuTlist, p^3 + p^2);
   
   // G(4, 35)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7, F.8];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.6^(-1)*F.8 ) >;
   Append(~Nlist, N1);
   
   // Q is phi_4(2111)c
   Q := Group < a, a1, a2, b1, b2 | (a1, a) = b1, (a2, a)= b2,
               (a1, a2) = 1, (b1, b2) = 1, (a, b1) = 1, (a, b2) = 1, 
               (a1, b1) = 1, (a1, b2) = 1, (a2, b1) = 1, (a2, b2) = 1, 
               b1^p = 1, b2^p = 1, a^p = 1, a1^p = 1, a2^p = b1>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 3*p^2);
   Append(~MuTlist, p^3 + p^2);
   
   // G(4, 36)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7, F.8];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.6*F.7*F.8 ) >;
   Append(~Nlist, N1);
   
   // Q is phi_4(221)b
   Q := Group < a, a1, a2, b1, b2 | (a1, a) = b1, (a2, a)= b2,
                (a1, a2) = 1, (b1, b2) = 1, (a, b1) = 1, (a, b2) = 1, 
                (a1, b1) = 1, (a1, b2) = 1, (a2, b1) = 1, (a2, b2) = 1, 
                b1^p = 1, b2^p = 1, a^p = b2, a1^p = 1, a2^p = b1>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 3*p^2);
   Append(~MuTlist, p^3 + p^2);
   
   // G(4, 37)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7, F.8];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.6*F.8^(-1) ) >;
   Append(~Nlist, N1);
   
   // Q is phi_4(2111)c
   Q := Group < a, a1, a2, b1, b2 | (a1, a) = b1, (a2, a)= b2, 
               (a1, a2) = 1, (b1, b2) = 1, (a, b1) = 1, (a, b2) = 1, 
               (a1, b1) = 1, (a1, b2) = 1, (a2, b1) = 1, (a2, b2) = 1, 
               b1^p = 1, b2^p = 1, a^p = 1, a1^p = 1, a2^p = b1>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 3*p^2);
   Append(~MuTlist, p^3 + p^2);
   
   // G(4, 38)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7, F.8];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.6*F.7^(-1)*F.8 ) >;
   Append(~Nlist, N1);
   
   // Q is phi_4(221)e
   // Q := Group < a, a1, a2, b1, b2 | (a1, a) = b1, (a2, a)= b2, 
   //             (a1, a2) = 1, (b1, b2) = 1, (a, b1) = 1, (a, b2) = 1, 
   //              (a1, b1) = 1, (a1, b2) = 1, (a2, b1) = 1, (a2, b2) = 1, 
   //             b1^p = 1, b2^p = 1, a^p = 1, a1^(4*p) = b2^(-1), a2^p = b1*b2>;

   // Q is G_46 (Girnat)
   Q := Group < g1, g2, g3, g4, g5 | (g2, g1) = g4*g5, (g3, g1)= g5,
               (g4, g1) = 1, (g5, g1) = 1, (g2, g3) = 1, (g2, g4) = 1,
               (g2, g5) = 1, (g3, g4) = 1, (g3, g5) = 1, (g4, g5) = 1,
               g1^p = 1, g2^p = g4, g3^p = g5, g4^p = 1, g5^p = 1>;
   
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 3*p^2);
   Append(~MuTlist, p^3 + p^2);
   
   // G(4, 39)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7, F.8];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.6*F.8 ) >;
   Append(~Nlist, N1);
   
   // Q is phi_4(221)e
   //Q := Group < a, a1, a2, b1, b2 | (a1, a) = b1, (a2, a)= b2, 
   //             (a1, a2) = 1, (b1, b2) = 1, (a, b1) = 1, (a, b2) = 1, 
   //             (a1, b1) = 1, (a1, b2) = 1, (a2, b1) = 1, (a2, b2) = 1, 
   //             b1^p = 1, b2^p = 1, a^p = 1, a1^(4*p) = b2^(-1), a2^p = b1*b2>;

   // Q is G_46 (Girnat)
   Q := Group < g1, g2, g3, g4, g5 | (g2, g1) = g4*g5, (g3, g1)= g5,
               (g4, g1) = 1, (g5, g1) = 1, (g2, g3) = 1, (g2, g4) = 1,
               (g2, g5) = 1, (g3, g4) = 1, (g3, g5) = 1, (g4, g5) = 1,
               g1^p = 1, g2^p = g4, g3^p = g5, g4^p = 1, g5^p = 1>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 3*p^2);
   Append(~MuTlist, p^3 + p^2);
   
   // G(4, 40)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7, F.8];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.6 ) >;
   Append(~Nlist, N1);
   
   // Q is phi_2(221)c
   Q := Group < a, a1, a2, ga | (a1, a) = a2, (a2, a)= 1, 
                (a1, a2) = 1, (a, ga) = 1, (a1, ga) = 1, (a2, ga) = 1, 
                a2^p = 1, a^(p^2) = 1, a1^p = 1, ga^(p) = a2>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 3*p^2);
   Append(~MuTlist, p^3 + p^2);
   
   // G(4, 41)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta:= [F.6, F.7, F.8];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.6 ) >;
   Append(~Nlist, N1);
   
   // Q is phi_2(221)c
   Q := Group < a, a1, a2, ga | (a1, a) = a2, (a2, a)= 1, 
                (a1, a2) = 1, (a, ga) = 1, (a1, ga) = 1, (a2, ga) = 1, 
                a2^p = 1, a^(p^2) = 1, a1^p = 1, ga^(p) = a2>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 3*p^2);
   Append(~MuTlist, p^3 + p^2);
   
   return Glist, Tlist, Nlist, MuGlist, MuTlist;
end function;

for p in PrimesInInterval (5, 7) do 
   "\nprocess p = ", p;
   L := Table3Phi4(p);

   Glist, Tlist, Nlist, MuGlist, MuTlist := Check4(L, p);

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
      assert Mu(P) lt Mu(T);
    end for;
end for;

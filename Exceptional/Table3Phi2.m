// exceptional groups from Phi2

My2C := function(p)
   F<a1, a2, a3, b1, b2> := FreeGroup (5);
   Alpha := [a1, a2, a3];
   Beta := [b1, b2];
   
   // common relations, typically commutators
   Comms := [
   (a2, a3) = a1, a1 = b2,
   (b1, b2) = 1] cat
   &cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..3]]: i in [1..2]]);
   
   L := [];
   
   // G2, 7
   G := quo <F | Comms, a2^p = a3^p = b1^(p^3) = b2^p = 1>;
   Append (~L, G);
   
   // G2, 8
   G := quo <F | Comms, a3^p = b1^(p^3) = b2^p = 1, a2^p = b2>;
   Append (~L, G);
   
   return L;
end function;
   
My2F := function(p)
   
   F<a1, a2, a3, b1, b2, b3> := FreeGroup (6);
   Alpha := [a1, a2, a3];
   Beta := [b1, b2, b3];
   
   // common relations, typically commutators
   Comms := [
   (a2, a3) = a1, a1 = b2] cat
   &cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..3]]: i in [1..3]])
   cat &cat([[(Beta[i], Beta[j]) = Id(F) : j in [i + 1..3]]: i in [1..3]]);
   
   L := [];
   
   // G2, 20
   G := quo <F | Comms, a2^p = a3^p = b1^(p^2) = b2^p = b3^p = 1>;
   Append (~L, G);
   
   // G2, 22
   G := quo <F | Comms,  a3^p = b1^(p^2) = b2^p = b3^p = 1, a2^p = b2>;
   Append (~L, G);
   
   // G2, 23
   G := quo <F | Comms,  a3^p = b1^(p^2) = b2^p = b3^p = 1, a2^p = b3>;
   Append (~L, G);
   
   // G2, 26
   G := quo <F | Comms,  b1^(p^2) = b2^p = b3^p = 1, a2^p = b2, a3^p = b3>;
   Append (~L, G);
   
   return L;
end function;
   
Table3Phi2 := function(p)
   return My2C(p) cat My2F(p);
end function;
   
Check2 := function(L, p)
   
   Glist := [];
   Tlist := [];
   Nlist := [];
   MuGlist := [];
   MuTlist := [];
   
   count := 0;
   
   // G(2,7)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3]; Beta:= [F.4, F.5];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.4^(p^2)*F.5^(-1) ) >;
   Append(~Nlist, N1);
   
   // Q is phi_2(311)b
   Q := Group < a, a1, a2, ga | (a1, a) = a2, (a2, a)= 1, (a1, a2) = 1, 
               (a, ga) = 1, (a1, ga) = 1, (a2, ga) = 1, a2^p = 1, 
               a^(p) = 1, a1^p = 1, ga^(p^2) = a2>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, p^3 + p^2);
   Append(~MuTlist, p^4);
   
   // G(2,8)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3]; Beta:= [F.4, F.5];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.4^(p^2)*F.5^(-1) ) >;
   Append(~Nlist, N1);
   
   // Q is phi_2(311)b
   Q := Group<a, a1, a2, ga | (a1, a) = a2, (a2, a)= 1, (a1, a2) = 1, 
             (a, ga) = 1, (a1, ga) = 1, (a2, ga) = 1, 
             a2^p = 1, a^(p) = 1, a1^p = 1, ga^(p^2) = a2>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, p^3 + p^2);
   Append(~MuTlist, p^4);
   
   // G(2,20)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3]; Beta:= [F.4, F.5, F.6];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.4^p*F.5^(-1) ) >;
   Append(~Nlist, N1);
   
   // Q is phi_2(2111)b
   Q := Group < a, a1, a2, b, ga | (a1, a) = a2, (a2, a)= 1, (a1, a2) = 1, 
                (b, ga) = 1, (a, ga) = 1, (a1, ga) = 1, (a2, ga) = 1, 
                (a, b) = 1, (a1, b) = 1, (a2, b) = 1, (b, ga) = 1, 
                a2^p = 1, a^(p) = 1, a1^p = 1, b^p = 1, ga^p = a2>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 2*p^2 + p);
   Append(~MuTlist, p^3 + p);
   
   // G(2,22)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3]; Beta:= [F.4, F.5, F.6];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.4^p*F.5^(-1) ) >;
   Append(~Nlist, N1);
   
   // Q is phi_2(2111)b
   
   Q := Group < a, a1, a2, b, ga | (a1, a) = a2, (a2, a)= 1, (a1, a2) = 1, 
                (b, ga) = 1, (a, ga) = 1, (a1, ga) = 1, (a2, ga) = 1, 
                (a, b) = 1, (a1, b) = 1, (a2, b) = 1, (b, ga) = 1, 
                a2^p = 1, a^(p) = 1, a1^p = 1, b^p = 1, ga^p = a2>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 2*p^2 + p);
   Append(~MuTlist, p^3 + p);
   
   // G(2,23)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3]; Beta:= [F.4, F.5, F.6];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.4^p*F.5^(-1) ) >;
   Append(~Nlist, N1);
   
   // Q is phi_2(221)c
   Q := Group < a, a1, a2, ga | (a1, a) = a2, (a2, a)= 1, (a1, a2) = 1, 
               (a, ga) = 1, (a1, ga) = 1, (a2, ga) = 1, a2^p = 1, 
               a^(p^2) = 1, a1^p = 1, ga^(p) = a2>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 3*p^2);
   Append(~MuTlist, p^3 + p^2);
   
   // G(2,26)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3]; Beta:= [F.4, F.5, F.6];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.4^p*F.5^(-1) ) >;
   Append(~Nlist, N1);
   
   // Q is phi_2(221)c
   Q := Group < a, a1, a2, ga | (a1, a) = a2, (a2, a)= 1, (a1, a2) = 1, 
               (a, ga) = 1, (a1, ga) = 1, (a2, ga) = 1, a2^p = 1, 
               a^(p^2) = 1, a1^p = 1, ga^(p) = a2>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 3*p^2);
   Append(~MuTlist, p^3 + p^2);
   
   return Glist, Tlist, Nlist, MuGlist, MuTlist;
end function;
   
for p in PrimesInInterval (5, 13) do 
   "\nprocess p = ", p;
   L := Table3Phi2(p);

   Glist, Tlist, Nlist, MuGlist, MuTlist := Check2(L, p);

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

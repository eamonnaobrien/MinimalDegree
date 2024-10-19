// exceptional groups from Phi3

NonQuadraticResidue := function (p)
   for x in GF (p) do
      if not IsPower (x, 2) then return x; end if;
   end for;
end function;

My3C := function(p)
   Z := Integers ();
   nu := Z ! (NonQuadraticResidue (p)); // nu
   
   F<a1, a2, a3, a4, b1, b2> := FreeGroup (6);
   Alpha := [a1, a2, a3, a4];
   Beta := [b1, b2];
   
   // common relations, typically commutators
   Comms := [
   (a2, a3) = 1, (a2, a4)= a1, (a3, a4) = a2, a1 = b2,
   (b1, b2) = 1] cat
   &cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..4]]: i in [1..2]]);
   
   L := [];
   
   // G3, 11
   G := quo <F | Comms, a2^p = a3^p = a4^p = b1^(p^2) = b2^p = 1>;
   Append (~L, G);
   
   // G3, 12
   G := quo <F | Comms, a2^p = a4^p = b1^(p^2) = b2^p = 1, a3^p = b1>;
   Append (~L, G);
   
   // G3, 15
   G := quo <F | Comms, a2^p = a3^p = b1^(p^2) = b2^p = 1, a4^p = b2>;
   Append (~L, G);
   
   // G3, 17
   G := quo <F | Comms, a2^p =  b1^(p^2) = b2^p = 1, a3^p = b1, a4^p = b2>;
   Append (~L, G);
   
   return L;
end function;
   
My3D := function(p)
   
   Z := Integers ();
   nu := Z ! (NonQuadraticResidue (p)); // nu
   
   F<a1, a2, a3, a4, b1, b2, b3> := FreeGroup (7);
   Alpha := [a1, a2, a3, a4];
   Beta := [b1, b2, b3];
   
   // common relations, typically commutators
   Comms := [
   (a2, a3) = 1, (a2, a4)= a1, (a3, a4) = a2, a1 = b1] cat
   &cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..4]]: i in [1..3]])
   cat &cat([[(Beta[i], Beta[j]) = Id(F) : j in [i + 1..3]]: i in [1..3]]);
   L := [];
   
   // G3, 20
   G := quo <F | Comms, a2^p = a4^p = b1^p = b2^p = b3^p = 1, a3^p = b2>;
   Append (~L, G);
   
   // G3, 23
   G := quo <F | Comms, a2^p =  b1^p = b2^p = b3^p = 1, a3^p = b2, a4^p = b1>;
   Append (~L, G);
   
   // G3, 25
   G := quo <F | Comms, a2^p =  b1^p = b2^p = b3^p = 1, a3^p = b3, a4^p = b2>;
   Append (~L, G);
   
   return L;
end function;

Table3Phi3 := function(p)
    return My3C(p) cat My3D(p);
end function;

Check3 := function(L, p)
   Glist := [];
   Tlist := [];
   Nlist := [];
   MuGlist := [];
   MuTlist := [];
   
   count := 0;
   
   // G(3,11)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4]; Beta:= [F.5, F.6];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.5^(p)*F.6^(-1) ) >;
   Append(~Nlist, N1);
   
   // Q is phi_3(2111)c
   Q := Group < a, a1, a2, a3, ga | (a1, a) = a2, (a2, a)= a3, (a1, a2) = 1, 
                (a, ga) = 1, (a1, ga) = 1, (a2, ga) = 1, (a, a3) = 1, 
                (a1, a3) = 1, (a2, a3) = 1, (a3, ga) = 1,
                a2^p = 1, a3^p = 1, a^p = 1, a1^(p) = 1, ga^p = a3>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 2*p^2);
   Append(~MuTlist, p^3);
   
   // G(3,12)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4]; Beta:= [F.5, F.6];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.5^(p)*F.6^(-1) ) >;
   Append(~Nlist, N1);
   
   // Q is phi_3(311)b_1
   Q := Group < a, a1, a2, a3 | (a1, a) = a2, (a2, a)= a3, (a1, a2) = 1, 
               (a, a3) = 1, (a1, a3) = 1, (a2, a3) = 1,
               a2^p = 1, a3^p = 1, a^p = 1, a1^(p^2) = a3>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, p^3 + p^2);
   Append(~MuTlist, p^4);
   
   // G(3,15)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4]; Beta:= [F.5, F.6];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.5^(p)*F.6^(-1) ) >;
   Append(~Nlist, N1);
   
   // Q is phi_3(2111)c
   Q := Group < a, a1, a2, a3, ga | (a1, a) = a2, (a2, a)= a3, (a1, a2) = 1, 
                (a, ga) = 1, (a1, ga) = 1, (a2, ga) = 1, (a, a3) = 1, 
                (a1, a3) = 1, (a2, a3) = 1, (a3, ga) = 1,
                a2^p = 1, a3^p = 1, a^p = 1, a1^(p) = 1, ga^p = a3>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 2*p^2);
   Append(~MuTlist, p^3);
   
   // G(3,17)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4]; Beta:= [F.5, F.6];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.5^(p)*F.6^(-1) ) >;
   Append(~Nlist, N1);
   
   // Q is phi_3(311)b_1
   Q := Group < a, a1, a2, a3 | (a1, a) = a2, (a2, a)= a3, (a1, a2) = 1, 
               (a, a3) = 1, (a1, a3) = 1, (a2, a3) = 1,
               a2^p = 1, a3^p = 1, a^p = 1, a1^(p^2) = a3>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, p^3 + p^2);
   Append(~MuTlist, p^4);
   
   // G(3,20)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4]; Beta:= [F.5, F.6, F.7];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.5*F.6^(-1) ) >;
   Append(~Nlist, N1);
   
   // Q is phi_3(2111)b_1
   Q := Group < a, a1, a2, a3, ga | (a1, a) = a2, (a2, a)= a3, (a1, a2) = 1, 
               (a, ga) = 1, (a1, ga) = 1, (a2, ga) = 1, (a, a3) = 1, 
               (a1, a3) = 1, (a2, a3) = 1, (a3, ga) = 1,
   a2^p = 1, a3^p = 1, a^p = 1, a1^(p) = a3, ga^p = 1>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 2*p^2 + p);
   Append(~MuTlist, p^3 + p);
   
   // G(3,23)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4]; Beta:= [F.5, F.6, F.7];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.5*F.6^(-1) ) >;
   Append(~Nlist, N1);
   
   // Q is phi_3(2111)b_1
   Q := Group < a, a1, a2, a3, ga | (a1, a) = a2, (a2, a)= a3, (a1, a2) = 1, 
               (a, ga) = 1, (a1, ga) = 1, (a2, ga) = 1, (a, a3) = 1, 
               (a1, a3) = 1, (a2, a3) = 1, (a3, ga) = 1,
               a2^p = 1, a3^p = 1, a^p = 1, a1^(p) = a3, ga^p = 1>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 2*p^2 + p);
   Append(~MuTlist, p^3 + p);
   
   // G(3, 25)
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4]; Beta:= [F.5, F.6, F.7];
   G1, phi := pQuotient(F, p, 6);
   Append(~Glist, G1);
   N1 := sub<G1 | phi( F.5^(-1)*F.7 ) >;
   Append(~Nlist, N1);
   
   // Q is phi_3(221)b_1
   Q := Group < a, a1, a2, a3 | (a1, a) = a2, (a2, a)= a3, (a1, a2) = 1, 
               (a, a3) = 1, (a1, a3) = 1, (a2, a3) = 1,
               a2^p = 1, a3^p = 1, a^(p^2) = 1, a1^p = a3>;
   B := pQuotient (Q, p, 5);
   Append(~Tlist, B);
   
   Append(~MuGlist, 3*p^2);
   Append(~MuTlist, p^3 + p^2);
   
   return Glist, Tlist, Nlist, MuGlist, MuTlist;
end function;

for p in PrimesInInterval (5, 13) do 
   "\nprocess p = ", p;
   L := Table3Phi3(p);

   Glist, Tlist, Nlist, MuGlist, MuTlist := Check3(L, p);

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

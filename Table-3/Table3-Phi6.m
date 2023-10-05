load "../setup-permrep.m";

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

// G6 with centre of type Cp^2 x Cp

// Groups G are listed in the list L.
// d(Z(L[i])) = 2 for i = 1 to p+1. 
// d(Z(L[i])) = 3 for i = p+2 to #L.G

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

// G6, 3

G := quo <F | Comms, a3^p = a4^p =  b1^(p^2) = b2^p = 1,
a5^p = b2>;
Append (~L, G);

// G6, 4

G := quo <F | Comms, a3^p = a5^p =  b1^(p^2) = b2^p = 1,
a4^p = b1>;
Append (~L, G);


// G6, 7r

for r in [1..(p-1)] do
G := quo <F | Comms, a3^p =   b1^(p^2) = b2^p = 1,
a4^p = b1^r, a5^p = b2>;
Append (~L, G);
end for;

return L;
end function;

// G6 with centre of type Cp x Cp X Cp

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
(a4, a5) = a3, (a3, a5) = a2, (a2, a5) = 1, a1 = b1,
a2 = b2] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..5]]: i in [1..3]])
cat &cat([[(Beta[i], Beta[j]) = Id(F) : j in [i + 1..3]]: i in [1..3]]);

L := [];

// G6, 9

G := quo <F | Comms, a3^p = a4^p =  b1^p = b2^p = b3^p = 1,
a5^p = b3>;
Append (~L, G);

// G6, 12r

for r in [1,nu] do
G := quo <F | Comms, a3^p =  b1^p = b2^p = b3^p = 1,
a4^p = b2^r, a5^p = b3>;
Append (~L, G);
end for;

// G6, 13

G := quo <F | Comms, a3^p =  b1^p = b2^p = b3^p = 1,
a4^p = b1, a5^p = b3>;
Append (~L, G);

return L;
end function;

TablePhi6 := function(p)
   return My6A(p) cat My6B(p);
end function;

// Checking of column "H"

Check6ACol3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 0;
H1 := [];
H2 := [];
MinDeg1 := [];

// G6, 3

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H1, sub<F | Alpha[3], Alpha[5]>);
Append (~H2, sub<F | Alpha[3], Alpha[4], Beta[1]>);
Append (~MinDeg1, p^3 + p^2);

// G6, 4

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H1, sub<F | Alpha[1], Alpha[3], Alpha[4]>);
Append (~H2, sub<F | Alpha[2], Alpha[3], Alpha[5]>);
Append (~MinDeg1, p^3 + p^2);

// G6, 7r

for r in [1..(p-1)] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7];
Append (~H1, sub<F | Alpha[1], Alpha[3], Alpha[4]>);
Append (~H2, sub<F | Alpha[2], Alpha[3], Alpha[5]>);
Append (~MinDeg1, p^3 + p^2);
end for;

return H1, H2, MinDeg1;
end function;

// H1, H2, MinDeg1 := Check6ACol3(L);

Check6BCol3 := function (L, p)

w := PrimitiveRoot(p);

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := p+1;
T1 := [];
T2 := [];
T3 := [];
MinDeg2 := [];

// following setup is done just to ensure that
// |L[i]: T1[i]| + |L[i]: T2[i]| + |L[i]: T3[i]| = MinDeg[i].

for r in [1..(p+1)] do
F := L[p+2]; // no particular reason of choosing L[p+2] here
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7, F.8];
Append (~T1, sub<F | Beta[3]^p>); // trivial subgroup
Append (~T2, sub<F | Beta[3]^p>); // trivial subgroup
Append (~T3, sub<F | Beta[3]^p>); // trivial subgroup
end for;

// G6, 9

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7, F.8];
Append (~T1, sub<F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~T2, sub<F | Alpha[3], Alpha[4], Beta[3]>);
Append (~T3, sub<F | Alpha[3], Alpha[5]>);
Append (~MinDeg2, 3*p^2);

// G6, 12r

for r in [1,nu] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7, F.8];
Append (~T1, sub<F | Alpha[3], Alpha[4]>);
Append (~T2, sub<F | Alpha[3], Alpha[5]>);
Append (~T3, sub<F | Alpha[5]*Alpha[4], 
Alpha[5]^(-1)*Alpha[4]^(-1)>);
Append (~MinDeg2, 3*p^2);
end for;

// G6, 13

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; Beta := [F.6, F.7, F.8];
Append (~T1, sub<F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~T2, sub<F | Alpha[3], Alpha[4], Beta[3]>);
Append (~T3, sub<F | Alpha[3], Alpha[5]>);
Append (~MinDeg2, 3*p^2);

return T1, T2, T3, MinDeg2;
end function;

MAX := 7^6;

for p in PrimesInInterval (5, 11) do 
  "\n process prime ", p;
  L := TablePhi6(p);
  H1, H2, MinDeg1 := Check6ACol3(L, p);
  T1, T2, T3, MinDeg2 := Check6BCol3(L, p);
  MinDeg := MinDeg1 cat MinDeg2;

  for i in [1..(p+1)] do
     G := L[i];
     Q, phi := pQuotient(G, p, 10);
     A := phi (H1[i]);
     B := phi (H2[i]);
     m1 := Index(Q, A);
     m2 := Index(Q, B);
     m := m1 + m2;
     C1 := Core(Q, A);
     C2 := Core(Q, B);
     C := C1 meet C2;
     assert #C eq 1;
     phiA := CosetAction (Q, A);
     phiB := CosetAction (Q, B);
     pi := PermutationRepresentationSumH (Q, [phiA, phiB]);
     J := Image (pi);
     assert #J eq #Q;
     if #J le MAX then assert IsIsomorphic (J, Q); end if;
     assert Degree (J) eq m;
     assert Degree (J) eq MinDeg[i];
  end for;

  for i in [(p+2)..#L] do
     G := L[i];
     Q, phi := pQuotient(G, p, 10);
     A := phi(T1[i]);
     B := phi(T2[i]);
     C := phi(T3[i]);
     m1 := Index(Q, A);
     m2 := Index(Q, B);
     m3 := Index(Q, C);
     m := m1 + m2 + m3;
     C1 := Core(Q, A);
     C2 := Core(Q, B);
     C3 := Core(Q, C);
     CI := C1 meet C2 meet C3;
     assert #CI eq 1;
     phiA := CosetAction (Q, A);
     phiB := CosetAction (Q, B);
     phiC := CosetAction (Q, C);
     pi := PermutationRepresentationSumH (Q, [phiA, phiB, phiC]);
     J := Image (pi);
     assert #J eq #Q;
     if #J le MAX then assert IsIsomorphic (J, Q); end if;
     assert Degree (J) eq m;
     assert Degree (J) eq MinDeg[i];
  end for;
end for;

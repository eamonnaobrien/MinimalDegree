load "../setup-permrep.m";

// G2 with centre of order cyclic of order p^4

My2A := function(p)

F<a1, a2, a3, b1> := FreeGroup (4);
Alpha := [a1, a2, a3];

// common relations, typically commutators
Comms := [
(a2, a3) = a1, a1 = b1^(p^3)]
cat
[(b1, Alpha[j]) = Id(F) : j in [1..3]];

L := [];

// G2, 1

G := quo <F | Comms, a2^p = a3^p = b1^(p^4) = 1>;
Append (~L, G);

// G2, 2

G := quo <F | Comms,  a3^p = b1^(p^4) = 1, 
a2^p = b1>;
Append (~L, G);

return L;
end function;

// G2 with centre of type Cp^3 x Cp, case 1

My2B := function(p)

F<a1, a2, a3, b1, b2> := FreeGroup (5);
Alpha := [a1, a2, a3];
Beta := [b1, b2];

// common relations, typically commutators
Comms := [
(a2, a3) = a1, a1 = b1^(p^2),
(b1, b2) = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..3]]: i in [1..2]]);

L := [];

// G2, 3

G := quo <F | Comms, a2^p = a3^p = b1^(p^3) = b2^p = 1>;
Append (~L, G);

// G2, 4

G := quo <F | Comms,  a3^p = b1^(p^3) = b2^p = 1,
a2^p = b2>;
Append (~L, G);

// G2, 5

G := quo <F | Comms,  a3^p = b1^(p^3) = b2^p = 1,
a2^p = b1>;
Append (~L, G);

// G2, 6

G := quo <F | Comms,  b1^(p^3) = b2^p = 1,
a2^p = b1, a3^p = b2>;
Append (~L, G);

return L;
end function;

// G2 with centre of type Cp^3 x Cp, case 2

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

G := quo <F | Comms,  a3^p = b1^(p^3) = b2^p = 1,
a2^p = b2>;
Append (~L, G);

// G2, 9

G := quo <F | Comms,  a3^p = b1^(p^3) = b2^p = 1,
a2^p = b1>;
Append (~L, G);

// G2, 10

G := quo <F | Comms,  b1^(p^3) = b2^p = 1,
a2^p = b2, a3^p = b1>;
Append (~L, G);

return L;
end function;

// G2 with centre of type Cp^2 x Cp^2

My2D := function(p)

F<a1, a2, a3, b1, b2> := FreeGroup (5);
Alpha := [a1, a2, a3];
Beta := [b1, b2];

// common relations, typically commutators
Comms := [
(a2, a3) = a1, a1 = b2^p,
(b1, b2) = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..3]]: i in [1..2]]);

L := [];

// G2, 11

G := quo <F | Comms, a2^p = a3^p = b1^(p^2) = b2^(p^2) = 1>;
Append (~L, G);

// G2, 12

G := quo <F | Comms, a3^p = b1^(p^2) = b2^(p^2) = 1,
a2^p = b2>;
Append (~L, G);

// G2, 13

G := quo <F | Comms, a3^p = b1^(p^2) = b2^(p^2) = 1,
a2^p = b1>;
Append (~L, G);

// G2, 14

G := quo <F | Comms, b1^(p^2) = b2^(p^2) = 1,
a2^p = b1, a3^p =  b2>;
Append (~L, G);

return L;
end function;

// G2 with centre of type Cp^2 x Cp X Cp, Case 1

My2E := function(p)

F<a1, a2, a3, b1, b2, b3> := FreeGroup (6);
Alpha := [a1, a2, a3];
Beta := [b1, b2, b3];

// common relations, typically commutators
Comms := [
(a2, a3) = a1, a1 = b1^p] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..3]]: i in [1..3]])
cat &cat([[(Beta[i], Beta[j]) = Id(F) : j in [i + 1..3]]: i in [1..3]]);

L := [];

// G2, 15

G := quo <F | Comms, a2^p = a3^p = b1^(p^2) = b2^p = b3^p = 1>;
Append (~L, G);

// G2, 16

G := quo <F | Comms,  a3^p = b1^(p^2) = b2^p = b3^p = 1,
a2^p = b1>;
Append (~L, G);

// G2, 17

G := quo <F | Comms,  a3^p = b1^(p^2) = b2^p = b3^p = 1,
a2^p = b2>;
Append (~L, G);

// G2, 18

G := quo <F | Comms,  b1^(p^2) = b2^p = b3^p = 1,
a2^p = b2, a3^p = b1>;
Append (~L, G);

// G2, 19

G := quo <F | Comms,  b1^(p^2) = b2^p = b3^p = 1,
a2^p = b3, a3^p = b2>;
Append (~L, G);

return L;
end function;

// G2 with centre of type Cp^2 x Cp X Cp, Case 2

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

// G2, 21

G := quo <F | Comms,  a3^p = b1^(p^2) = b2^p = b3^p = 1,
a2^p = b1>;
Append (~L, G);

// G2, 22

G := quo <F | Comms,  a3^p = b1^(p^2) = b2^p = b3^p = 1,
a2^p = b2>;
Append (~L, G);

// G2, 23

G := quo <F | Comms,  a3^p = b1^(p^2) = b2^p = b3^p = 1,
a2^p = b3>;
Append (~L, G);


// G2, 24

G := quo <F | Comms,  b1^(p^2) = b2^p = b3^p = 1,
a2^p = b1, a3^p = b2>;
Append (~L, G);

// G2, 25

G := quo <F | Comms,  b1^(p^2) = b2^p = b3^p = 1,
a2^p = b1, a3^p = b3>;
Append (~L, G);

// G2, 26

G := quo <F | Comms,  b1^(p^2) = b2^p = b3^p = 1,
a2^p = b2, a3^p = b3>;
Append (~L, G);

return L;
end function;

// G2 with centre of type Cp x Cp X Cp x Cp

My2G := function(p)

F<a1, a2, a3, b1, b2, b3, b4> := FreeGroup (7);
Alpha := [a1, a2, a3];
Beta := [b1, b2, b3, b4];

// common relations, typically commutators
Comms := [
// EOB correction 
// (a2, a3) = a1, a1 = b2] cat
(a2, a3) = a1, a1 = b1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..3]]: i in [1..4]])
cat &cat([[(Beta[i], Beta[j]) = Id(F) : j in [i + 1..4]]: i in [1..4]]);

L := [];

// G2, 27

G := quo <F | Comms, a2^p = a3^p = b1^p = b2^p = b3^p = b4^p = 1>;
Append (~L, G);

// G2, 28

G := quo <F | Comms, a3^p = b1^p = b2^p = b3^p = b4^p = 1,
a2^p = b1>;
Append (~L, G);

// G2, 29

G := quo <F | Comms, a3^p = b1^p = b2^p = b3^p = b4^p = 1,
a2^p = b2>;
Append (~L, G);

// G2, 30

G := quo <F | Comms, b1^p = b2^p = b3^p = b4^p = 1,
a2^p = b2, a3^p = b1>;
Append (~L, G);

// G2, 31

G := quo <F | Comms, b1^p = b2^p = b3^p = b4^p = 1,
a2^p = b3, a3^p = b2>;
Append (~L, G);

return L;
end function;

Table1Phi2 := function(p)
   return My2A(p) cat My2B(p) cat My2C(p)
      cat My2D(p) cat My2E(p) cat My2F(p) cat My2G(p);
end function;

Check2A := function (L, p)

count := 0;
H := [];
MinDeg1 := [];

// G2, 1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta := F.4;
Append (~H, sub< F | Alpha[3]>);
Append (~MinDeg1, p^5);

// G2, 2

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta := F.4;
Append (~H, sub< F | Alpha[3]>);
Append (~MinDeg1, p^5);

return H, MinDeg1;
end function;

Check2BCD := function (L, p)

count := 2;
H1 := [];
H2 := [];
MinDeg2 := [];

for r in [1..2] do
F := L[3]; // no particular reason of choosing 5 here
Alpha := [F.1, F.2, F.3]; Beta := [F.4, F.5];
Append (~H1, sub<F | Beta[2]^p>); // trivial subgroup
Append (~H2, sub<F | Beta[2]^p>); // trivial subgroup
end for;

// G2, 3

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta := [F.4, F.5];
Append (~H1, sub<F | Alpha[1], Alpha[2],
Alpha[3], Beta[1]>);
Append (~H2, sub<F | Alpha[3], Beta[2]>);
Append (~MinDeg2, p^4 + p);

// G2, 4

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta := [F.4, F.5];
Append (~H1, sub<F |  Alpha[2] >);
Append (~H2, sub<F | Alpha[3], Beta[1]>);
Append (~MinDeg2, p^4 + p^2);

// G2, 5

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta := [F.4, F.5];
Append (~H1, sub<F | Alpha[1], Alpha[2],
Alpha[3], Beta[1]>);
Append (~H2, sub<F | Alpha[3], Beta[2]>);
Append (~MinDeg2, p^4 + p);

// G2, 6

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta := [F.4, F.5];
Append (~H1, sub<F |  Alpha[2] >);
Append (~H2, sub<F | Alpha[3]>);
Append (~MinDeg2, p^4 + p^2);

// G2, 7

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta := [F.4, F.5];
Append (~H1, sub<F | Alpha[2], Alpha[3], Beta[2]>);
Append (~H2, sub<F | Alpha[3], Beta[1]>);
Append (~MinDeg2, p^3 + p^2);

// G2, 8

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta := [F.4, F.5];
Append (~H1, sub<F | Alpha[2], Alpha[3], Beta[2]>);
Append (~H2, sub<F | Alpha[3], Beta[1]>);
Append (~MinDeg2, p^3 + p^2);

// G2, 9

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta := [F.4, F.5];
Append (~H1, sub<F | Alpha[2]>);
Append (~H2, sub<F | Alpha[3], Beta[2]>);
Append (~MinDeg2, p^4 + p^2);

// G2, 10

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta := [F.4, F.5];
Append (~H1, sub<F |  Alpha[2] >);
Append (~H2, sub<F | Alpha[3], Beta[1]>);
Append (~MinDeg2, p^4 + p^2);

// G2, 11

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta := [F.4, F.5];
Append (~H1, sub<F | Alpha[2], Alpha[3], Beta[2]>);
Append (~H2, sub<F | Alpha[3], Beta[1]>);
Append (~MinDeg2, p^3 + p^2);

// G2, 12

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta := [F.4, F.5];
Append (~H1, sub<F | Alpha[2], Alpha[3], Beta[2]>);
Append (~H2, sub<F | Alpha[3], Beta[1]>);
Append (~MinDeg2, p^3 + p^2);

// G2, 13

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta := [F.4, F.5];
Append (~H1, sub<F | Alpha[2], Beta[1]>);
Append (~H2, sub<F | Alpha[3], Beta[2]>);
Append (~MinDeg2, 2*p^3);

// G2, 14

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta := [F.4, F.5];
Append (~H1, sub<F | Alpha[2], Beta[1]>);
Append (~H2, sub<F | Alpha[3], Beta[2]>);
Append (~MinDeg2, 2*p^3);

return H1, H2, MinDeg2;
end function;

Check2EF := function (L, p)

count := 14;
T1 := [];
T2 := [];
T3 := [];
MinDeg3 := [];


// following setup is done just to ensure that
// |L[i]: T1[i]| + |L[i]: T2[i]| + |L[i]: T3[i]| = MinDeg[i].

for r in [1..14] do
F := L[15]; // no particular reason of choosing L[15] here
Alpha := [F.1, F.2, F.3]; Beta := [F.4, F.5, F.6];
Append (~T1, sub<F | Beta[3]^p>); // trivial subgroup
Append (~T2, sub<F | Beta[3]^p>); // trivial subgroup
Append (~T3, sub<F | Beta[3]^p>); // trivial subgroup
end for;

// G2, 15

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta := [F.4, F.5, F.6];
Append (~T1, sub<F | Alpha[2], Alpha[3], 
Beta[1], Beta[2]>);
Append (~T2, sub<F | Alpha[2], Alpha[3], 
Beta[1], Beta[3]>);
Append (~T3, sub<F | Alpha[3], 
Beta[2], Beta[3]>);
Append (~MinDeg3, p^3 + 2*p);

// G2, 16

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta := [F.4, F.5, F.6];
Append (~T1, sub<F | Alpha[2], Alpha[3], 
Beta[1], Beta[2]>);
Append (~T2, sub<F | Alpha[2], Alpha[3], 
Beta[1], Beta[3]>);
Append (~T3, sub<F | Alpha[3], 
Beta[2], Beta[3]>);
Append (~MinDeg3, p^3 + 2*p);

// G2, 17

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta := [F.4, F.5, F.6];
Append (~T1, sub<F | Alpha[2], Alpha[3], 
Beta[1], Beta[2]>);
Append (~T2, sub<F | Alpha[3], 
Beta[1], Beta[3]>);
Append (~T3, sub<F | Alpha[2], 
Beta[2], Beta[3]>);
Append (~MinDeg3, p^3 + p^2 + p);

// G2, 18

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta := [F.4, F.5, F.6];
Append (~T1, sub<F | Alpha[2], Alpha[3], 
Beta[1], Beta[2]>);
Append (~T2, sub<F | Alpha[3], 
Beta[1], Beta[3]>);
Append (~T3, sub<F | Alpha[2], 
Beta[2], Beta[3]>);
Append (~MinDeg3, p^3 + p^2 + p);

// G2, 19

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta := [F.4, F.5, F.6];
Append (~T1, sub<F | Alpha[2], Beta[1], Beta[3]>);
Append (~T2, sub<F | Alpha[3], Beta[1], Beta[2]>);
Append (~T3, sub<F | Alpha[3], Beta[2], Beta[3]>);
Append (~MinDeg3, p^3 + 2*p^2);

// G2, 20

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta := [F.4, F.5, F.6];
Append (~T1, sub<F | Alpha[2], Alpha[3], 
Beta[1], Beta[2]>);
Append (~T2, sub<F | Alpha[2], Alpha[3], 
Beta[2], Beta[3]>);
Append (~T3, sub<F | Alpha[3], Beta[1], Beta[3]>);
Append (~MinDeg3, 2*p^2 + p);

// G2, 21

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta := [F.4, F.5, F.6];
Append (~T1, sub<F | Alpha[2], Alpha[3], 
Beta[1], Beta[2]>);
Append (~T2, sub<F | Alpha[2], Beta[1], Beta[3]>);
Append (~T3, sub<F | Alpha[3], Beta[2], Beta[3]>);
Append (~MinDeg3, p^3 + p^2 + p);

// G2, 22

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta := [F.4, F.5, F.6];
Append (~T1, sub<F | Alpha[2], Alpha[3], 
Beta[1], Beta[2]>);
Append (~T2, sub<F | Alpha[2], Alpha[3], 
Beta[2], Beta[3]>);
Append (~T3, sub<F | Alpha[3], Beta[1], Beta[3]>);
Append (~MinDeg3, 2*p^2 + p);

// G2, 23

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta := [F.4, F.5, F.6];
Append (~T1, sub<F | Alpha[2], Alpha[3], 
Beta[2], Beta[3]>);
Append (~T2, sub<F | Alpha[3], Beta[1], Beta[2]>);
Append (~T3, sub<F | Alpha[2], Beta[1], Beta[3]>);
Append (~MinDeg3, 3*p^2);

// G2, 24

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta := [F.4, F.5, F.6];
Append (~T1, sub<F | Alpha[2], Alpha[3], 
Beta[1], Beta[2]>);
Append (~T2, sub<F | Alpha[2], Beta[1], Beta[3]>);
Append (~T3, sub<F | Alpha[3], Beta[2], Beta[3]>);
Append (~MinDeg3, p^3 + p^2 + p);

// G2, 25

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta := [F.4, F.5, F.6];
Append (~T1, sub<F | Alpha[2], Beta[1], Beta[2]>);
Append (~T2, sub<F | Alpha[3], Beta[1], Beta[3]>);
Append (~T3, sub<F | Alpha[3], Beta[2]>);
Append (~MinDeg3, p^3 + 2*p^2);

// G2, 26

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta := [F.4, F.5, F.6];
Append (~T1, sub<F | Alpha[2], Alpha[3], 
Beta[2], Beta[3]>);
Append (~T2, sub<F | Alpha[2], Beta[1], Beta[2]>);
Append (~T3, sub<F | Alpha[3], Beta[1], Beta[3]>);
Append (~MinDeg3, 3*p^2);

return T1, T2, T3, MinDeg3;
end function;

Check2G := function (L, p)

count := 26;
S1 := [];
S2 := [];
S3 := [];
S4 := [];
MinDeg4 := [];


for r in [1..26] do
F := L[27]; // no particular reason of choosing L[15] here
Alpha := [F.1, F.2, F.3]; Beta := [F.4, F.5, F.6, F.7];
Append (~S1, sub<F | Beta[3]^p>); // trivial subgroup
Append (~S2, sub<F | Beta[3]^p>); // trivial subgroup
Append (~S3, sub<F | Beta[3]^p>); // trivial subgroup
Append (~S4, sub<F | Beta[3]^p>); // trivial subgroup
end for;

// G2, 27

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta := [F.4, F.5, F.6, F.7];
Append (~S1, sub<F | Alpha[2], Alpha[3], 
Beta[1], Beta[2], Beta[3]>);
Append (~S2, sub<F | Alpha[2], Alpha[3], 
Beta[1], Beta[2], Beta[4]>);
Append (~S3, sub<F | Alpha[2], Alpha[3], 
Beta[1], Beta[3], Beta[4]>);
Append (~S4, sub<F | Alpha[3], 
Beta[2], Beta[3], Beta[4]>);
Append (~MinDeg4, p^2 + 3*p);

// G2, 28

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta := [F.4, F.5, F.6, F.7];
Append (~S1, sub<F | Alpha[2], Alpha[3], 
Beta[1], Beta[2], Beta[3]>);
Append (~S2, sub<F | Alpha[2], Alpha[3], 
Beta[1], Beta[2], Beta[4]>);
Append (~S3, sub<F | Alpha[2], Alpha[3], 
Beta[1], Beta[3], Beta[4]>);
Append (~S4, sub<F | Alpha[3], 
Beta[2], Beta[3], Beta[4]>);
Append (~MinDeg4, p^2 + 3*p);

// G2, 29

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta := [F.4, F.5, F.6, F.7];
Append (~S1, sub<F | Alpha[2], Alpha[3], 
Beta[1], Beta[2], Beta[3]>);
Append (~S2, sub<F | Alpha[2], Alpha[3], 
Beta[1], Beta[2], Beta[4]>);
Append (~S3, sub<F | Alpha[3], 
Beta[1], Beta[3], Beta[4]>);
Append (~S4, sub<F | Alpha[2], 
Beta[2], Beta[3], Beta[4]>);
Append (~MinDeg4, 2*p^2 + 2*p);

// G2, 30

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta := [F.4, F.5, F.6, F.7];
Append (~S1, sub<F | Alpha[2], Alpha[3], 
Beta[1], Beta[2], Beta[3]>);
Append (~S2, sub<F | Alpha[2], Alpha[3], 
Beta[1], Beta[2], Beta[4]>);
Append (~S3, sub<F | Alpha[3], 
Beta[1], Beta[3], Beta[4]>);
Append (~S4, sub<F | Alpha[2], 
Beta[2], Beta[3], Beta[4]>);
Append (~MinDeg4, 2*p^2 + 2*p);

// G2, 31

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta := [F.4, F.5, F.6, F.7];
Append (~S1, sub<F | Alpha[2], Alpha[3], 
Beta[1], Beta[2], Beta[3]>);
Append (~S2, sub<F | Alpha[3], 
Beta[1], Beta[2], Beta[4]>);
Append (~S3, sub<F | Alpha[2], 
Beta[1], Beta[3], Beta[4]>);
Append (~S4, sub<F | Alpha[2], 
Beta[2], Beta[3], Beta[4]>);
Append (~MinDeg4, 3*p^2 + p);

return S1, S2, S3, S4, MinDeg4;
end function;

MAX := 7^6;

for p in PrimesInInterval (5, 11) do 
   "\n process prime ", p;
   L := Table1Phi2(p);
   "# of groups is ", #L;
   H, MinDeg1 := Check2A(L, p);
   H1, H2, MinDeg2 := Check2BCD(L, p);
   T1, T2, T3, MinDeg3 := Check2EF(L, p);
   S1, S2, S3, S4, MinDeg4 := Check2G(L, p);
   MinDeg := MinDeg1 cat MinDeg2 cat MinDeg3 cat MinDeg4;

   for i in [1..2] do
     G := L[i];
     Q, phi := pQuotient(G, p, 10);
     A := phi (H[i]);
     m := Index(Q, A);
     C := Core(Q, A);
     assert #C eq 1;
     phiA := CosetAction (Q, A);
     J := Image (phiA);
     assert #J eq #Q;
     assert Degree (J) eq MinDeg[i];
  end for;

   for i in [3..14] do
     G := L[i];
     Q,phi := pQuotient(G, p, 10);
     A := phi (H1[i]);
     B := phi (H2[i]);
     m1 := Index(Q,A);
     m2 := Index(Q,B);
     m := m1 + m2;
     C1 := Core(Q,A);
     C2 := Core(Q,B);
     C := C1 meet C2;
     assert #C eq 1;
     phiA := CosetAction (Q,A);
     phiB := CosetAction (Q,B);
     pi := PermutationRepresentationSumH (Q,[phiA, phiB]);
     J := Image (pi);
     assert #J eq #Q;
     if #J le MAX then assert IsIsomorphic (J, Q); end if;
     assert Degree (J) eq m;
     assert Degree (J) eq MinDeg[i];
  end for;

   for i in [15..26] do
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

   for i in [27..#L] do
     G := L[i];
     Q, phi := pQuotient(G, p, 10);
     A := phi(S1[i]);
     B := phi(S2[i]);
     C := phi(S3[i]);
     D := phi(S4[i]);
     m1 := Index(Q, A);
     m2 := Index(Q, B);
     m3 := Index(Q, C);
     m4 := Index(Q, D);
     m := m1 + m2 + m3 + m4;
     C1 := Core(Q, A);
     C2 := Core(Q, B);
     C3 := Core(Q, C);
     C4 := Core(Q, D);
     CI := C1 meet C2 meet C3 meet C4;
     assert #CI eq 1;
     phiA := CosetAction (Q, A);
     phiB := CosetAction (Q, B);
     phiC := CosetAction (Q, C);
     phiD := CosetAction (Q, D);
     pi := PermutationRepresentationSumH (Q, [phiA, phiB, phiC, phiD]);
     J := Image (pi);
     assert #J eq #Q;
     if #J le MAX then assert IsIsomorphic (J, Q); end if;
     assert Degree (J) eq m;
     assert Degree (J) eq MinDeg[i];
  end for;
end for;

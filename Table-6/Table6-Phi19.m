load "../setup-permrep.m";

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

//Phi19 with center Cp X Cp

My19 := function(p)

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
&cat([[(Beta[i], Alpha[j]) = Id(F) : j
 in [1..4]]: i in [1..2]]);

L := [];

// (2211)c_rs

for r in [1,nu] do
for s in [2..(p-1)] do
G := quo <F | Comms, a^p = b^p  = 1,
a1^p = b1*b2^r, a2^p = b2^s>;
Append (~L, G);
end for;
end for;

// (2211)d_000

G := quo <F | Comms, a^p = b^p  = 1,
a1^p = b2^nu, a2^p = b1^(-nu)>;
Append (~L, G);

// (2211)d_r0t

 for r in [1,nu] do
    for t in [1..(p-1)] do
       if (1+4*r*t) mod p ne 0 and IsPower(K!(1+4*r*t),2) eq true then
          G := quo <F | Comms, a^p = b^p  = 1,
                        a1^p = b1*b2^r, a2^p = b1^t>;
          Append (~L, G);
       end if;
    end for;
 end for;

// (2211)d_rst

 for r in [1,nu] do
      for s in [1..p-1] do
         for t in [0..(p-1) div 2] do
            k := w^t mod p;
            flaphi := false;
            if (k mod p) ne (r*s) mod p and ((1-k)^2+4*r*s) mod p ne 0 
               and IsPower(K!((1-k)^2+4*r*s),2) eq true then
               flaphi := true;
               if r eq nu and k in [1,p-1] and IsPower(K!(-s),2) then
                  flaphi := false;
               end if;
            end if;
            if flaphi eq true then
               G := quo <F | Comms, a^p = b^p  = 1,
                             a1^p = b1*b2^r, a2^p = b1^s*b2^k>;
               Append (~L, G);
           end if;
        end for;
    end for;
end for;

// (2211)f_r0

for r in [1,nu] do
    for t in [0..(p-1)] do
       if (1+4*r*t) mod p eq 0 then
          G := quo <F | Comms, a^p = b^p  = 1, a1^p = b1*b2^r, a2^p = b1^t>;
          Append (~L, G);
       end if;
   end for;
end for;

// (2211)f_rs

for r in [1,nu] do
   for s in [1..(p-3) div 2] do
      for t in [0..(p-1) ] do
         k := w^s mod p;
         if (4*r*t + (1-k)^2) mod p eq 0 then
            G := quo <F | Comms, a^p = b^p  = 1, a1^p = b1*b2^r, a2^p = b1^t*b2^k>;
            Append (~L, G);
         end if;
      end for;
   end for;
end for;

// (2211)g_r00

for r in [1,nu] do
   G := quo <F | Comms, a^p = b^p  = 1, a1^p = b2, a2^p = b1^r>;
   Append (~L, G);
end for;

// (2211)g_r0t

for r in [1,nu] do
   for t in [1..(p-1)] do
      if IsPower(K!(1+4*r*t),2) eq false then
          G := quo <F | Comms, a^p = b^p  = 1, a1^p = b1*b2^r, a2^p = b1^t>;
          Append (~L, G);
      end if;
   end for;
end for;

// (2211)g_rst

for r in [1,nu] do
   for s in [1..p-1] do
      for t in [0..(p-1) div 2] do
         k := w^t mod p;
         flaphi := false;
         if (k mod p) ne (r*s) mod p and
            IsPower(K!((1-k)^2+4*r*s),2) eq false then
            flaphi := true;
            if r eq nu and k in [1,p-1] and IsPower(K!(-s) ,2) then
               flaphi := false;
            end if;
         end if;
         if flaphi eq true then
            G := quo <F | Comms, a^p = b^p  = 1, a1^p = b1*b2^r, a2^p = b1^s*b2^k>;
            Append (~L, G);
         end if;
      end for;
   end for;
end for;

// (2211)e_r

for r in [1,nu] do
   G := quo <F | Comms, a^p = b^p  = 1, a1^p = b1*b2^r, a2^p = b2>;
   Append (~L, G);
end for;

// (2211)h_r

for r in [1..(p-1)] do
   G := quo <F | Comms, a^p = b1, b^p  = 1, a1^p = b2^r, a2^p = b2>;
   Append (~L, G);
end for;

// (2211)i

G := quo <F | Comms, a^p = b1, b^p  = 1, a1^p = 1, a2^p = b2>;
Append (~L, G);

// (2211)j_r

for r in [1..(p-1) div 2] do
   G := quo <F | Comms, a^p = b1*b2, b^p  = 1, a1^p = b1^r, a2^p = b2^r>;
   Append (~L, G);
end for;

// (2211)k_rs

for r in [1..p-1] do
   for s in [0..(p-1) div 2] do
     if (s-r) mod p ne 0 and (2*r-s) mod p ne 0 then
        G := quo <F | Comms, a^p = b1*b2, b^p  = 1, a1^p = b1^r, a2^p = b2^(s-r)>;
        Append (~L, G);
     end if;
   end for;
end for;

// (2211)l_r

for r in [1..p-1] do
   G := quo <F | Comms, a^p = b1*b2, b^p  = 1, a1^p = b1^r, a2^p = 1>;
   Append (~L, G);
end for;

// (2211)m_r

for r in [1,nu] do
   G := quo <F | Comms, a^p = b1, b^p  = 1, a1^p = b2^r, a2^p = 1>;
   Append (~L, G);
end for;

// (21^4)b_r

for r in [1,nu] do
   G := quo <F | Comms, a^p = b^p  = 1, a1^p = b1*b2^r, a2^p = 1>;
   Append (~L, G);
end for;

// (21^4)c_r

for r in [1,nu] do
   G := quo <F | Comms, a^p = b^p  = 1, a1^p = b1, a2^p = b1^r>;
   Append (~L, G);
end for;

// (21^4)d_rs

for r in [1,nu] do
      for s in [0..(p-3) div 2] do
         gg := w^s mod p;
         for u in [1..p-1] do
            if (r*u) mod p eq 1 then
               if not (p mod 4 eq 3 and r eq nu and s eq 0) then 
                  G := quo <F | Comms, a^p = b^p  = 1,
                       a1^p = b1*b2^r, a2^p = b1^(u*gg mod p)*b2^gg>;
                  Append (~L, G);
               end if;
            end if;
         end for;
      end for;
end for;

// (21^4)e_r

for r in [1,nu] do
   G := quo <F | Comms, a^p = b^p  = 1, a1^p = b2^r, a2^p = 1>;
   Append (~L, G);
end for;

// (21^4)f_r

for r in [1,nu] do
 for u in [1..p-1] do
    if (r*u) mod p eq 1 then
       G := quo <F | Comms, a^p = b^p  = 1, a1^p = b1*b2^r, a2^p = b1^-u*b2^-1>;
       Append (~L, G);
    end if;
  end for;
end for;

// (21^4)g

G := quo <F | Comms, a^p = b1, b^p  = 1, a1^p = 1, a2^p = 1>;
Append (~L, G);

// (21^4)h

G := quo <F | Comms, a^p = b1*b2, b^p  = 1, a1^p = 1, a2^p = 1>;
Append (~L, G);

// (1^6)

G := quo <F | Comms, a^p = 1, b^p  = 1, a1^p = 1, a2^p = 1>;
Append (~L, G);

return L;
end function;

Check19 := function(L, p)

K := GF(p);

w := PrimitiveRoot(p);

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 0;

PFlist := []; // lists the group G
PRlist := []; // lists the subgroup R
PNlist := []; // lists kernel of non-linear irr char. from R
PSlist := []; // lists the subgroup R
PMlist := []; // lists kernel of non-linear irr char. from S
MinDeg := []; //Mu(G) from table

// (2211)c_rs

for r in [1,nu] do
for s in [2..(p-1)] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2^p)>;
GPN := sub<GPR | phi(F.1), phi(F.3), phi(F.4), phi(F.6)>;
GPS := sub<GPF | phi(F.1), phi(F.3^p), phi(F.4), phi(F.2^p)>;
GPM := sub<GPS  | phi(F.1), phi(F.4), phi(F.2^p)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, p^3 + p^2);
end for;
end for;

// (2211)d_000

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2^p), 
phi(F.5), phi(F.6)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.6)>;
GPS := sub<GPF | phi(F.1), phi(F.3^p), phi(F.4), phi(F.2), 
phi(F.5), phi(F.6)>;
GPM := sub<GPS  | phi(F.1), phi(F.4), phi(F.5)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, 2*p^3);

// (2211)d_r0t

for r in [1,nu] do
      for t in [1..(p-1)] do
         if (1+4*r*t) mod p ne 0 and IsPower(K!(1+4*r*t),2) eq true then
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2^p), 
phi(F.5), phi(F.6)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.6)>;
GPS := sub<GPF | phi(F.1), phi(F.3^p), phi(F.4), phi(F.2), 
phi(F.5), phi(F.6)>;
GPM := sub<GPS  | phi(F.1), phi(F.4), phi(F.5)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, 2*p^3);
end if;
end for;
end for;

// (2211)d_rst

 for r in [1,nu] do
      for s in [1..p-1] do
         for t in [0..(p-1) div 2] do
            k := w^t mod p;
            flaphi := false;
            if (k mod p) ne (r*s) mod p and ((1-k)^2+4*r*s) mod p ne 0 
               and IsPower(K!((1-k)^2+4*r*s),2) eq true then
               flaphi := true;
               if r eq nu and k in [1,p-1] and IsPower(K!(-s),2) then
                  flaphi := false;
               end if;
            end if;
            if flaphi eq true then
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2^p), 
phi(F.5), phi(F.6)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.6)>;
GPS := sub<GPF | phi(F.1), phi(F.3^p), phi(F.4), phi(F.2), 
phi(F.5), phi(F.6)>;
GPM := sub<GPS  | phi(F.1), phi(F.4), phi(F.5)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, 2*p^3);
end if;
end for;
end for;
end for;


// (2211)f_r0

for r in [1,nu] do
      for t in [0..(p-1)] do
         if (1+4*r*t) mod p eq 0 then
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2^p), 
phi(F.5), phi(F.6)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.6)>;
GPS := sub<GPF | phi(F.1), phi(F.3^p), phi(F.4), phi(F.2), 
phi(F.5), phi(F.6)>;
GPM := sub<GPS  | phi(F.1), phi(F.4), phi(F.5)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, 2*p^3);
end if;
end for;
end for;

// (2211)f_rs

for r in [1,nu] do
      for s in [1..(p-3) div 2] do
         for t in [0..(p-1) ] do
            k := w^s mod p;
            if (4*r*t + (1-k)^2) mod p eq 0 then
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2^p), 
phi(F.5), phi(F.6)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.6)>;
GPS := sub<GPF | phi(F.1), phi(F.3^p), phi(F.4), phi(F.2), 
phi(F.5), phi(F.6)>;
GPM := sub<GPS  | phi(F.1), phi(F.4), phi(F.5)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, 2*p^3);
end if;
end for;
end for;
end for;

// (2211)g_r00

for r in [1,nu] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2^p), 
phi(F.5), phi(F.6)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.6)>;
GPS := sub<GPF | phi(F.1), phi(F.3^p), phi(F.4), phi(F.2), 
phi(F.5), phi(F.6)>;
GPM := sub<GPS  | phi(F.1), phi(F.4), phi(F.5)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, 2*p^3);
end for;


// (2211)g_r0t

for r in [1,nu] do
for t in [1..(p-1)] do
         if IsPower(K!(1+4*r*t),2) eq false then
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2^p), 
phi(F.5), phi(F.6)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.6)>;
GPS := sub<GPF | phi(F.1), phi(F.3^p), phi(F.4), phi(F.2), 
phi(F.5), phi(F.6)>;
GPM := sub<GPS  | phi(F.1), phi(F.4), phi(F.5)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, 2*p^3);
end if;
end for;
end for;

// (2211)g_rst

for r in [1,nu] do
      for s in [1..p-1] do
         for t in [0..(p-1) div 2] do
            k := w^t mod p;
            flaphi := false;
            if (k mod p) ne (r*s) mod p and
               IsPower(K!((1-k)^2+4*r*s),2) eq false then
               flaphi := true;
               if r eq nu and k in [1,p-1] and IsPower(K!(-s) ,2) then
                  flaphi := false;
               end if;
            end if;
            if flaphi eq true then
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2^p), 
phi(F.5), phi(F.6)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.6)>;
GPS := sub<GPF | phi(F.1), phi(F.3^p), phi(F.4), phi(F.2), 
phi(F.5), phi(F.6)>;
GPM := sub<GPS  | phi(F.1), phi(F.4), phi(F.5)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, 2*p^3);
end if;
end for;
end for;
end for;

// (2211)e_r

for r in [1,nu] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2^p)>;
GPN := sub<GPR | phi(F.1), phi(F.3), phi(F.4), phi(F.6)>;
GPS := sub<GPF | phi(F.1), phi(F.3^p), phi(F.4), phi(F.2^p)>;
GPM := sub<GPS  | phi(F.1), phi(F.4), phi(F.2^p)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, p^3 + p^2);
end for;

// (2211)h_r

for r in [1..(p-1)] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4)>;
GPN := sub<GPR | phi(F.3), phi(F.4), phi(F.6)>;
GPS := sub<GPF | phi(F.1), phi(F.4), phi(F.2)>;
GPM := sub<GPS  | phi(F.1), phi(F.4), phi(F.5)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, 2*p^3);
end for;

// (2211)i

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4)>;
GPN := sub<GPR | phi(F.3), phi(F.4), phi(F.6)>;
GPS := sub<GPF | phi(F.1), phi(F.3^p), phi(F.4), phi(F.2)>;
GPM := sub<GPS  | phi(F.1), phi(F.2), phi(F.4), phi(F.5)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, p^3 + p^2);

// (2211)j_r

for r in [1..(p-1) div 2] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2^p), 
phi(F.5), phi(F.6)>;
GPN := sub<GPR | phi(F.3), phi(F.4), phi(F.6)>;
GPS := sub<GPF | phi(F.1), phi(F.3^p), phi(F.4), phi(F.2), 
phi(F.5), phi(F.6)>;
GPM := sub<GPS  | phi(F.2), phi(F.4), phi(F.5)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, 2*p^3);
end for;

// (2211)k_rs

for r in [1..p-1] do
      for s in [0..(p-1) div 2] do
         if (s-r) mod p ne 0 and (2*r-s) mod p ne 0 then
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4)>;
GPN := sub<GPR | phi(F.3), phi(F.4), phi(F.6)>;
GPS := sub<GPF | phi(F.1), phi(F.4), phi(F.2)>;
GPM := sub<GPS  | phi(F.2), phi(F.4), phi(F.5)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, 2*p^3);
end if;
end for;
end for;

// (2211)l_r

for r in [1..p-1] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.6)>;
GPN := sub<GPR | phi(F.3), phi(F.4), phi(F.6)>;
GPS := sub<GPF | phi(F.1), phi(F.4), phi(F.2)>;
GPM := sub<GPS  | phi(F.2), phi(F.4), phi(F.5)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, 2*p^3);
end for;

// (2211)m_r

for r in [1, nu] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.2^p)>;
GPN := sub<GPR | phi(F.3), phi(F.4), phi(F.6)>;
GPS := sub<GPF | phi(F.1), phi(F.4), phi(F.2)>;
GPM := sub<GPS  | phi(F.1), phi(F.4), phi(F.5)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, 2*p^3);
end for;

// (21^4)b_r

for r in [1, nu] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.5), phi(F.6)>;
GPN := sub<GPR | phi(F.1), phi(F.3), phi(F.4), phi(F.6)>;
GPS := sub<GPF | phi(F.1), phi(F.4), phi(F.2), phi(F.5)>;
GPM := sub<GPS  | phi(F.1), phi(F.4), phi(F.5)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, p^3 + p^2);
end for;

// (21^4)c_r

for r in [1, nu] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.6)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.6)>;
GPS := sub<GPF | phi(F.1), phi(F.4), phi(F.2), phi(F.6)>;
GPM := sub<GPS  | phi(F.1), phi(F.4), phi(F.2)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, p^3 + p^2);
end for;

// (21^4)d_rs

for r in [1,nu] do
      for s in [0..(p-3) div 2] do
         for u in [1..p-1] do
            if (r*u) mod p eq 1 then
               if not (p mod 4 eq 3 and r eq nu and s eq 0) then 
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.6)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.6)>;
GPS := sub<GPF | phi(F.1), phi(F.4), phi(F.2), phi(F.5)>;
GPM := sub<GPS  | phi(F.1), phi(F.4), phi(F.5)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, 2*p^3);
end if;
end if;
end for;
end for;
end for;

// (21^4)e_r

for r in [1, nu] do
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.5), phi(F.6)>;
GPN := sub<GPR | phi(F.1), phi(F.3), phi(F.4), phi(F.6)>;
GPS := sub<GPF | phi(F.1), phi(F.4), phi(F.2), phi(F.5)>;
GPM := sub<GPS  | phi(F.1), phi(F.4), phi(F.5)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, p^3 + p^2);
end for;

// (21^4)f_r

for r in [1, nu] do
for u in [1..p-1] do
         if (r*u) mod p eq 1 then
count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.6)>;
GPN := sub<GPR | phi(F.1), phi(F.4), phi(F.6)>;
GPS := sub<GPF | phi(F.1), phi(F.4), phi(F.2), phi(F.5), phi(F.6)>;
GPM := sub<GPS  | phi(F.1), phi(F.4), phi(F.5)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, 2*p^3);
end if;
end for;
end for;

// (21^4)g

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.6)>;
GPN := sub<GPR | phi(F.3), phi(F.4), phi(F.6)>;
GPS := sub<GPF | phi(F.1), phi(F.4), phi(F.2), phi(F.6)>;
GPM := sub<GPS  | phi(F.1), phi(F.2), phi(F.4), phi(F.5)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, p^3 + p^2);

// (21^4)h

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.6)>;
GPN := sub<GPR | phi(F.3), phi(F.4), phi(F.6)>;
GPS := sub<GPF | phi(F.1), phi(F.4), phi(F.2), phi(F.5)>;
GPM := sub<GPS  | phi(F.2), phi(F.4), phi(F.5)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, 2*p^3);

// (1^6)

count := count+1;
F := L[count];
GPF, phi := pQuotient(F, p, 10);
Append(~PFlist, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.5), phi(F.6)>;
GPN := sub<GPR | phi(F.1), phi(F.3), phi(F.4), phi(F.6)>;
GPS := sub<GPF | phi(F.1), phi(F.4), phi(F.2), phi(F.5), phi(F.6)>;
GPM := sub<GPS  | phi(F.1), phi(F.2), phi(F.4), phi(F.5)>;
Append(~PRlist, GPR);
Append(~PNlist, GPN);
Append(~PSlist, GPS);
Append(~PMlist, GPM);
Append(~MinDeg, 2*p^2);

return PFlist, PRlist, PNlist, PSlist, PMlist, MinDeg;
end function;

MAX := 11^6;

for p in PrimesInInterval (5, 11) do 
   "\nprocess p = ", p;
   L := My19(p);
   "#L is ", #L;
   PFlist, PRlist, PNlist, PSlist, PMlist, MinDeg := Check19(L, p);
   for i in [1..#L] do
      PF := PFlist[i];
      PR := PRlist[i];
      PN := PNlist[i];
      PS := PSlist[i];
      PM := PMlist[i];
      Mu_value := MinDeg[i];
      Int := Core(PF, PN) meet Core(PF, PM);
      assert #Int eq 1;
      phiN := CosetAction (PF, PN);
      phiM := CosetAction (PF, PM);
      pi := PermutationRepresentationSumH (PF, [phiN, phiM]);
      J := Image (pi);
      assert #J eq #PF;
      // if #J le MAX then assert IsIsomorphic (J, PF); end if;
      assert Degree (J) eq Mu_value;

      // Irreducibility checks for X_G 
      QPRN, f := quo<PR | PN>;
      linQP := LinearCharacters(QPRN);
      for j in [1..#linQP] do
         if IsFaithful(linQP[j]) eq true then
            chi := linQP[j];
            break;
         end if;
      end for;
      chi_bar := LiftCharacter(chi, f, PR);
      psi := Induction(chi_bar, PF);
      assert IsIrreducible(psi);

      QPSM, h := quo<PS | PM>;
      linQPM := LinearCharacters (QPSM);
      for j in [1..#linQPM] do
         if IsFaithful(linQPM[j]) eq true then
            lambda := linQPM[j];
            break;
         end if;
      end for;
      lambda_bar := LiftCharacter(lambda, h, PS);
      eta := Induction(lambda_bar, PF);
      assert IsIrreducible(eta);

   end for;
end for;

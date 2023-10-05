// Example 3.1: construct minimal degree perm rep for G_(3, 23)

load "setup-permrep.m";

SetEchoInput (true);

F:=FreeGroup (7);
G := quo<F |
    ($.2, $.3) = Id($),
    ($.2, $.4) = $.1,
    ($.3, $.4) = $.2,
    $.1 = $.5,
    ($.5, $.1) = Id($),
    ($.5, $.2) = Id($),
    ($.5, $.3) = Id($),
    ($.5, $.4) = Id($),
    ($.6, $.1) = Id($),
    ($.6, $.2) = Id($),
    ($.6, $.3) = Id($),
    ($.6, $.4) = Id($),
    ($.7, $.1) = Id($),
    ($.7, $.2) = Id($),
    ($.7, $.3) = Id($),
    ($.7, $.4) = Id($),
    ($.5, $.6) = Id($),
    ($.5, $.7) = Id($),
    ($.6, $.7) = Id($),
    $.2^7 = Id($),
    $.5^7 = Id($),
    $.6^7 = Id($),
    $.7^7 = Id($),
    $.3^7 = $.6,
    $.4^7 = $.5 >
;

p := 7;
Q, phi := pQuotient (G, p, 10);

H := sub <G | [G.i: i in [1..6]]>;

ImH:=phi (H);

H1 := sub<ImH | [phi (G.i): i in [4,2]]>;
H2 := sub<ImH | [phi (G.i): i in [3,2]]>;
Core (ImH, H1) meet Core (ImH, H2);
tau1 := CosetAction (ImH, H1);
tau2 := CosetAction (ImH, H2);
tau := PermutationRepresentationSumH (ImH, [tau1, tau2]);
I := Image (tau);
#I;
IsIsomorphic (I, ImH);

I, S := DetermineMinRep (G, Q, ImH, [H1, H2], phi);

// check S 
&meet[Core (Q, s): s in S];

assert IsIsomorphic (I, Q);

// alternative to set it directly 
K:=sub< G | [G.i: i in [7]]>;   
K := phi (K);
phi1 := CosetAction (Q, sub< Q |  H1, K>);
phi2 := CosetAction (Q, sub< Q | H2, K>);
phi3 := CosetAction (Q, ImH);
phi :=PermutationRepresentationSumH (Q, [phi1, phi2, phi3]);
J := Image (phi);


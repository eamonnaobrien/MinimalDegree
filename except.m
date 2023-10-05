// is G having minimal degree mu exceptional?

IsExceptional := function (G, mu)
   N:=NormalSubgroups (G);
   N := [x`subgroup: x in N];
   N := [x: x in N | #x gt 1 and #x lt #G];
   for i in [1..#N] do 
     Q := quo < G | N[i]>;
     m := Mu (Q);
     if m gt mu then return true, N[i]; end if;
   end for;
   return false;
end function;


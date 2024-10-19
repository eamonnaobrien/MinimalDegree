
FindDifferent := function (S)

    if #S eq 0 then return S; end if;

    Different := [ S[1] ];

    for i in [2..#S] do
      j := 1; new := true;
      repeat
          new := not (IsIdenticalPresentation (S[i], Different [j]));
          j := j + 1;
      until (new eq false) or (j gt #Different);
      if new then Append (~Different, S[i]); end if;
    end for;

    return Different;

end function;


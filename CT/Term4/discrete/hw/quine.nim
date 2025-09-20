import strutils
proc p1() =
  let (s1, s2) = ("import strutils\x0Aproc p1() =\x0A  let (s1, s2) = (", ")\x0A  echo s1 & escape(s1) & \", \" & escape(s2) & s2\x0Ap1()")
  echo s1 & escape(s1) & ", " & escape(s2) & s2
p1()

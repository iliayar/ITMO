import strutils
let (s1, s2) = ("import strutils\x0Alet (s1, s2) = (", ")\x0Aecho s1 & escape(s1) & \", \" & escape(s2) & s2")
echo s1 & escape(s1) & ", " & escape(s2) & s2

import strutils
proc p1() =
  let flag = true
  let (s1, s2, s3, s4, s5) = ("import strutils\x0Aproc p", "() =\x0A  let flag = ", "\x0A  let (s1, s2, s3, s4, s5) = (", ")\x0A  echo s1 & (if flag: \"2\" else: \"1\") & s2 & (if flag: \"false\" else: \"true\") & s3 & escape(s1) & \", \"  & escape(s2) & \", \" & escape(s3) & \", \" & escape(s4) & \", \" & escape(s5) & s4 & (if flag: \"2\" else: \"1\") & s5\x0Ap", "()")
  echo s1 & (if flag: "2" else: "1") & s2 & (if flag: "false" else: "true") & s3 & escape(s1) & ", "  & escape(s2) & ", " & escape(s3) & ", " & escape(s4) & ", " & escape(s5) & s4 & (if flag: "2" else: "1") & s5
p1()

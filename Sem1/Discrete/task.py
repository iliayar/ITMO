import sys

filename = "lzw"

with open(filename + ".in", "r") as inp:
    a = inp.readline()[:-1];
    inp.close()
res = []
d = {}
for i in range(26):
    d[chr(i + ord('a'))] = i
t = ''
for c in a:
    try:
        d[t+c]
        t += c
        print(t)
    except:
        res += [str(d[t])]
        d[t+c] = len(d)
        t = c
res += [str(d[t])]
with open(filename + ".out", "w") as out:
    out.write(' '.join(res))
    out.close()

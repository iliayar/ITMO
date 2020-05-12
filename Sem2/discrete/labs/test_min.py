#!/usr/bin/python

import random

n = random.randint(1,10)
m = random.randint(1, 2*n)
k = random.randint(1, n)

print(n, m, k)

acc = [False]*(n + 1)

while k != 0:
    while True:
        i = random.randint(1, n)
        if not acc[i]:
            break
    print(i, end=' ')
    acc[i] = True
    k -= 1
print()

to = [{} for i in range(n + 1)]

while m != 0:
    while True:
        u = random.randint(1, n)
        v = random.randint(1, n)
        c = chr(random.randint(ord('a'), ord('z')))
        if c not in to[u]:
            break
    print(u, v, c)
    to[u][c] = v
    m -= 1


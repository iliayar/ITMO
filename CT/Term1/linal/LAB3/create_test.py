import random

inp = open("gen_input.txt", "r").readlines()

out = open("input.txt", "w")

out.write(inp[0])
out.write(inp[1])
out.write(inp[2])
out.write(inp[3])
out.write(inp[4])
out.write(inp[5])
out.write(inp[6])
out.write(inp[7])

n = int(inp[7]);

x_min, x_max = map(float,inp[8].split())
y_min, y_max = map(float,inp[9].split())
z_min, z_max = map(float,inp[10].split())

for i in range(n):
    for j in range(3):
        out.write(str(random.random()*100 % x_max + x_min) + " ")
        out.write(str(random.random()*100 % y_max + y_min) + " ")
        out.write(str(random.random()*100 % z_max + z_min))
        out.write("\n")

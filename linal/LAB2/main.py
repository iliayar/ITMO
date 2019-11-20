#!/usr/bin/python3
from typing import NewType
import datetime
import math


class Vector3:
    x = 0
    y = 0
    z = 0

    def __init__(self ,x: float, y: float , z: float):
        self.x = x
        self.y = y
        self.z = z

    def sub(self, v):
        return self.mul(-1).add(v)

    def add(self, v):
        nx = self.x + v.x
        ny = self.y + v.y
        nz = self.z + v.z
        return Vector3(nx,ny,nz)

    def mul(self, c: float):
        nx = self.x * c
        ny = self.y * c
        nz = self.z * c
        return Vector3(nx,ny,nz)

    def dot(self, v):
        return abs(v.x*self.x + v.y*self.y + v.z*self.z)

    def cross(self,vect):
        nx = self.y * vect.z - self.z * vect.y
        ny = self.z * vect.x - self.x * vect.z
        nz = self.x * vect.y - self.y * vect.x
        return Vector3(nx,ny,nz)

    def magnitude(self):
        return math.sqrt(self.x**2 + self.y**2 + self.z**2) 

    def __str__(self):
        return "(%f, %f, %f)" % (self.x, self.y, self.z)

    @staticmethod
    def angle(v1, v2):
        try:
            cos = (v1.x*v2.x + v1.y*v2.y + v1.z*v2.z)/(v1.magnitude()*v2.magnitude())
            return cos
            # if cos < 0:
            #     return -math.acos(cos)
            # else:
            #     return math.acos(cos)
        except ZeroDivisionError:
            return 0.0

def log(*args):
    print("["+str(datetime.datetime.now())+"]", *args)


def sign(x):
    if(x < 0):
        return -1
    elif(x > 0):
        return 1
    else:
        return 0

def toDegrees(angle):
    res =  angle/math.pi*180

    # if(res > 90):
    #     res = -(res - 90)

    # if(angle < 0):
    #     res = -res
    return res

inp = open("input.txt", "r")
out = open("output.txt", "w")

def print_file(d):
    out.write(str(d) + "\n")

x, y, z = map(float,inp.readline().split())
pos = Vector3(x,y,z)
x, y, z = map(float,inp.readline().split())
direction = Vector3(x,y,z)
x, y, z = map(float,inp.readline().split())
vPos = Vector3(x,y,z)
x, y, z = map(float,inp.readline().split())
enemyPos = Vector3(x,y,z)

hCos = Vector3.angle(direction.mul(-1), enemyPos.sub(pos))
hSin = Vector3.angle(direction.cross(Vector3(0,0,1)), enemyPos.sub(pos))

canon = enemyPos.sub(pos)

# log(hSin, hCos)
hAngle = toDegrees(math.asin(hSin))
side = 1
if hAngle < 0:
    side = -1

if hSin > 0 and hCos <= 0:
    hAngle = hAngle - 90
if hSin >= 0 and hCos > 0:
    hAngle = 90 - hAngle
if hSin <= 0 and hCos < 0:
    hAngle = -(hAngle + 90)
if hSin < 0 and hCos >= 0:
    hAngle = hAngle + 90


# log(hAngle)


vCos = Vector3.angle(vPos, canon)

# log(vCos)
vAngle = -toDegrees(math.asin(vCos))

vAngle = round(vAngle,2)
hAngle = round(hAngle,2)

# log(hAngle)
# log(vAngle)

if abs(hAngle) >= 60 or abs(vAngle) >= 60:
    print_file(0)
    print_file(0)
    print_file(0)
    print_file("Bye")
else:
    print_file(side)
    print_file(hAngle)
    print_file(vAngle)
    print_file("Bye")

inp.close()
out.close()
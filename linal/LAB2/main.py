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

x, y = map(float,inp.readline().split())
pos = Vector3(x,y,0)
x, y = map(float,inp.readline().split())
direction = Vector3(x,y,0)
x, y = map(float,inp.readline().split())
vPos = Vector3(x,y,1)
x, y = map(float,inp.readline().split())
enemyPos = Vector3(x,y,0)

cos = Vector3.angle(direction.cross(Vector3(0,0,1)), pos.sub(enemyPos));
sin = Vector3.angle(direction, pos.sub(enemyPos));


# log(cos, sin)
side = 0
if(sign(sin) != sign(cos)):
    side = -1
    if(cos < 0):
        side = 1
        # sin = -cos
    angle = math.asin(sin)
else:
    side = -1
    if(cos < 0):
        side = 1
        # sin = cos
    angle = math.asin(sin)
angle = toDegrees(angle)


vCos = Vector3.angle(Vector3(0,0,1), vPos)
vAngle = toDegrees(math.acos(vCos))

vCos = Vector3.angle(direction.cross(Vector3(0,0,1)), vPos)
if sign(vCos) == side:
    vAngle = - vAngle

log(vCos)

angle = round(angle,2)
vAngle = round(vAngle, 2)

if vAngle == 0:
    vAngle = 0

# log(vAngle)
# log(angle)

if abs(angle) >= 60 or abs(vAngle) >= 60:
    print_file(0)
    print_file(0)
    print_file(0)
    print_file("Bye")
else:
    print_file(side)
    print_file(angle)
    print_file(vAngle)
    print_file("Bye")

inp.close()
out.close()
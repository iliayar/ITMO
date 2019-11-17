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

def toDegrees(angle):
    res =  math.acos(angle)/math.pi*180

    if(res > 90):
        res = -(res - 90)

    if(angle < 0):
        res = -res
    return res

x, y, z = map(float,input().split())
pos = Vector3(x,y,z)
x, y, z = map(float,input().split())
direction = Vector3(x,y,z)
x, y, z = map(float,input().split())
vPos = Vector3(x,y,z)
x, y, z = map(float,input().split())
enemyPos = Vector3(x,y,z)

hAngle = Vector3.angle(direction, pos.sub(enemyPos));
log(hAngle, toDegrees(hAngle))

horizont = Vector3(vPos.x, vPos.y, 0)
vAngle = Vector3.angle(horizont, vPos)
log(vAngle, toDegrees(vAngle))
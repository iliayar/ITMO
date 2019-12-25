import math
import datetime



class Vector3:
    x = 0
    y = 0
    z = 0

    def __init__(self ,x: float, y: float , z: float):
        self.x = x
        self.y = y
        self.z = z

    @classmethod
    def fromstring(cls, s: str):
        s = list(map(float,s.split()))
        x = s[0]
        y = s[1]
        z = s[2]
        return cls(x,y,z)

    def sub(self, v):
        return self.add(v.mul(-1))

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
        return Vector3(nx,ny,nz).mul(-1)

    def magnitude(self):
        return math.sqrt(self.x**2 + self.y**2 + self.z**2) 

    def __str__(self):
        return "Vector3 (%f, %f, %f)" % (self.x, self.y, self.z)

    def __add__(self, v):
        return self.add(v)

    def __sub__(self, v):
        return self.sub(v)

def angle(cls, v1, v2):
    try:
        cos = (v1.x*v2.x + v1.y*v2.y + v1.z*v2.z)/(v1.magnitude()*v2.magnitude())
        return cos
    except ZeroDivisionError:
        return 0.0

class Plane:
    points = []

    def __init__(self, *points):
        self.points = points

        a = points[1] - points[0]
        b = points[2] - points[0]

        self.n = b.cross(a)
        self.n = self.n.mul(1/self.n.magnitude())

        self.d = -(self.n.x*points[0].x + self.n.y*points[0].y + self.n.z*points[0].z) 

    def __str__(self):
        res = "Plane (\n"
        res += "    " + str(self.points[0]) + ",\n"
        res += "    " + str(self.points[1]) + ",\n"
        res += "    " + str(self.points[2]) + ";\n"
        res += "    %.2fx + %.2fy + %.2fz + %.2f = 0\n" % (self.n.x, self.n.y, self.n.z, self.d)
        res += ")"
        return res

    def getPoint(self, **axis):
        n = self.n
        d = self.d
        if('x' in axis and 'y' != None):
            if n.z == 0:
                return None
            return Vector3(axis['x'], axis['y'], -(n.x*axis['x'] + n.y*axis['y'] + d)/n.z)
        elif('y' in axis and 'z' in axis):
            if n.x == 0:
                return None
            return Vector3(-(n.z*axis['z'] + n.y*axis['y'] + d)/n.x, axis['y'], axis['z'])
        elif('z' in axis and 'x' in axis):
            if n.y == 0:
                return None
            return Vector3(axis['x'], -(n.x*axis['x'] + n.z*axis['z'] + d)/n.y, axis['z'])    



class Line:

    def __init__(self, v, p):
        self.s = v.mul(1/v.magnitude())
        # self.s = v
        self.p0 = p;

    def __str__(self):
        res = "Line (\n"
        res += "    (x - %f)/%f = (y - %f)/%f = (z - %f)/%f\n" % (self.p0.x, self.s.x, self.p0.y, self.s.y, self.p0.z, self.s.z)
        res += ")"
        return res

    def getPoint(self, **axis):
        p0 = self.p0
        s = self.s
        if('x' in axis):
            if s.x == 0:
                return None
            return Vector3(axis['x'], (axis['x'] - p0.x)/s.x*s.y + p0.y, (axis['x'] - p0.x)/s.x*s.z + p0.z)
        elif('y' in axis):
            if s.y == 0:
                return None
            return Vector3((axis['y'] - p0.y)/s.y*s.x + p0.x, axis['y'], (axis['y'] - p0.y)/s.y*s.z + p0.z)
        elif('z' in axis):
            if s.z == 0:
                return None
            return Vector3((axis['z'] - p0.z)/s.z*s.x + p0.x, (axis['z'] - p0.z)/s.z*s.y + p0.y, axis['z'])    

def dist(p1, p2):
    return math.sqrt((p1.x - p2.x)**2 + (p1.y - p2.y)**2 + (p1.z - p2.z)**2)

def intersect(line, plane):
    X = line.p0
    A = plane.points[0]

    v = A - X

    d = plane.n.dot(v)

    e = plane.n.dot(line.s)

    res = None

    if e != 0:
        res = Vector3(X.x + line.s.x*d/e, 
                        X.y + line.s.y*d/e,
                        X.z + line.s.z*d/e)
    
    return res

def reflect(v,n):
    return v - n.mul(n.dot(v)*2)

def inTriangle(p, plane):
    
    A = plane.points[0]
    B = plane.points[1]
    C = plane.points[2]

    a1 = (A - p).cross(B - p).magnitude()
    a2 = (B - p).cross(C - p).magnitude()
    a3 = (C - p).cross(A - p).magnitude()
    a4 = (B - A).cross(C - A).magnitude()

    if a1 + a2 + a3 - 1e-4 <= a4:
        return True
    return False

def log(*args):
    print("["+str(datetime.datetime.now())+"]", *args)

def toDegrees(angle):
    res =  angle/math.pi*180

    return res

EPS = 0.01

inp = open("input.txt", "r")

A = Vector3.fromstring(inp.readline());
B = Vector3.fromstring(inp.readline());
C = Vector3.fromstring(inp.readline());
D = A + C - B
C1 = Vector3.fromstring(inp.readline());
B1 = B + C1 - C
A1 = A + B1 - B
D1 = A1 + D - A
direction = Vector3.fromstring(inp.readline());
entry = Vector3.fromstring(inp.readline())
power = int(inp.readline())
n = int(inp.readline());

mirrors = []

for i in range(n):
    p1 = Vector3.fromstring(inp.readline())
    p2 = Vector3.fromstring(inp.readline())
    p3 = Vector3.fromstring(inp.readline())
    plane = Plane(p1,p2,p3)
    mirrors += [plane]

ray = Line(direction, entry)

print(mirrors[0])

# exit()

#############_DRAWING_######################
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
import matplotlib.pyplot as plt
import numpy as np
#############_DRAWING_######################


fig = plt.figure()
ax = Axes3D(fig)

def draw_line(p1,p2, edgecolor="yellow", linewidths=2, alpha=0.8):
    x = [p1.x, p2.x]
    y = [p1.y, p2.y]
    z = [p1.z, p2.z]
    verts = [list(zip(x,y,z))]
    ax.add_collection3d(Poly3DCollection(verts, alpha=alpha, linewidths=linewidths, edgecolor=edgecolor))

def draw_point(p, linewidths=10, edgecolor="r"):
    x = [p.x + EPS, p.x, p.x]
    y = [p.y, p.y + EPS, p.y]
    z = [p.z, p.z, p.z + EPS]
    verts = [list(zip(x,y,z))]
    ax.add_collection3d(Poly3DCollection(verts, linewidths=linewidths, edgecolor=edgecolor))


x = [A.x, B.x, C.x, D.x]
y = [A.y, B.y, C.y, D.y]
z = [A.z, B.z, C.z, D.z]
verts = [list(zip(x,y,z))]
ax.add_collection3d(Poly3DCollection(verts, alpha=0.1, linewidths=2, facecolor='b',edgecolor='black'))

x = [A.x, A1.x, B1.x, B.x]
y = [A.y, A1.y, B1.y, B.y]
z = [A.z, A1.z, B1.z, B.z]
verts = [list(zip(x,y,z))]
ax.add_collection3d(Poly3DCollection(verts, alpha=0.1, linewidths=2, facecolor='b',edgecolor='black'))

x = [A.x, A1.x, D1.x, D.x]
y = [A.y, A1.y, D1.y, D.y]
z = [A.z, A1.z, D1.z, D.z]
verts = [list(zip(x,y,z))]
ax.add_collection3d(Poly3DCollection(verts, alpha=0.1, linewidths=2, facecolor='b',edgecolor='black'))

x = [C.x, C1.x, B1.x, B.x]
y = [C.y, C1.y, B1.y, B.y]
z = [C.z, C1.z, B1.z, B.z]
verts = [list(zip(x,y,z))]
ax.add_collection3d(Poly3DCollection(verts, alpha=0.1, linewidths=2, facecolor='b',edgecolor='black'))

x = [C.x, C1.x, D1.x, D.x]
y = [C.y, C1.y, D1.y, D.y]
z = [C.z, C1.z, D1.z, D.z]
verts = [list(zip(x,y,z))]
ax.add_collection3d(Poly3DCollection(verts, alpha=0.1, linewidths=2, facecolor='b',edgecolor='black'))

x = [A1.x, B1.x, C1.x, D1.x]
y = [A1.y, B1.y, C1.y, D1.y]
z = [A1.z, B1.z, C1.z, D1.z]
verts = [list(zip(x,y,z))]
ax.add_collection3d(Poly3DCollection(verts, alpha=0.1, linewidths=2, facecolor='b',edgecolor='black'))

for c in mirrors:
    x = []
    y = []
    z = []
    for j in range(3):
        x += [c.points[j].x]
        y += [c.points[j].y]
        z += [c.points[j].z]
    verts = [list(zip(x,y,z))]
    ax.add_collection3d(Poly3DCollection(verts, alpha=0.5, linewidths=2, facecolor='r',edgecolor='black'))

for i in range(2):
    test_plane = mirrors[i]

    p = intersect(ray, test_plane)

    print(p)
    print(inTriangle(p,test_plane))
    if(p != None and inTriangle(p,test_plane)):
        draw_line(ray.getPoint(x=entry.x), ray.getPoint(x=p.x))

        draw_point(p)

        test_r = Line(reflect(ray.s, test_plane.n), p)
        n_line = Line(test_plane.n, p)
        yaba = draw_line(n_line.getPoint(x=entry.x), n_line.getPoint(x=p.x), edgecolor="cyan")
        # print(test_r)
        # draw_line(test_r.getPoint(x=entry.x), test_r.getPoint(y=p.y))

        ray = test_r
        entry = p


plt.show()
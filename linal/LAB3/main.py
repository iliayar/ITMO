import math
import datetime
import sys


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
        return v.x*self.x + v.y*self.y + v.z*self.z

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

class Polygon:
    points = []

    def __init__(self, *points):
        self.points = points

        a = points[1] - points[0]
        b = points[2] - points[0]

        self.n = b.cross(a)
        self.n = self.n.mul(1/self.n.magnitude())

        self.d = -(self.n.x*points[0].x + self.n.y*points[0].y + self.n.z*points[0].z) 

    def __str__(self):
        res = "Polygon (\n"
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

    def containsPoint(self, p):
        return -EPS <= self.n.x*p.x + self.n.y*p.y + self.n.z*p.z + self.d <= EPS


class Line:

    def __init__(self, v, p):
        # self.s = v.mul(1/v.magnitude())
        self.s = v
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

def angle(cls, v1, v2):
    try:
        cos = (v1.x*v2.x + v1.y*v2.y + v1.z*v2.z)/(v1.magnitude()*v2.magnitude())
        return cos
    except ZeroDivisionError:
        return 0.0

def distance(p1, p2):
    return math.sqrt((p1.x - p2.x)**2 + (p1.y - p2.y)**2 + (p1.z - p2.z)**2)

def intersect(line, polygon):
    X = line.p0
    A = polygon.points[0]

    v = A - X

    d = polygon.n.dot(v)

    e = polygon.n.dot(line.s)

    res = None

    if e != 0:
        res = Vector3(X.x + line.s.x*d/e, 
                        X.y + line.s.y*d/e,
                        X.z + line.s.z*d/e)
    
    return res

def reflect(v,n):
    return v - n.mul(n.dot(v)*2)

def inPolygon(p, polygon):
    side = []
    for i in range(len(polygon.points)):
        t0 = polygon.points[(i+1)%len(polygon.points)] - polygon.points[i]
        t1 = p - polygon.points[i]

        side += [t0.cross(t1).dot(polygon.n)]

    test1 = [1 for c in side if c <= 0]
    test2 = [1 for c in side if c >= 0]

    if (len(test1) == len(side)) and polygon.containsPoint(p):
        return True

    return False


# def inTriangle(p, polygon):
    
#     A = polygon.points[0]
#     B = polygon.points[1]
#     C = polygon.points[2]

#     a1 = (A - p).cross(B - p).magnitude()
#     a2 = (B - p).cross(C - p).magnitude()
#     a3 = (C - p).cross(A - p).magnitude()
#     a4 = (B - A).cross(C - A).magnitude()

#     if a1 + a2 + a3 - 1e-4 <= a4:
#         return True
#     return False

def log(*args):
    print("["+str(datetime.datetime.now())+"]", *args)

def toDegrees(angle):
    res =  angle/math.pi*180

    return res

DRAWING = "LOCAL" in sys.argv

DRAW_EPS = 0.01
EPS = 1e-9

inp = open("input.txt", "r")
out = open("output.txt", "w")

A = Vector3.fromstring(inp.readline());
B = Vector3.fromstring(inp.readline());
C = Vector3.fromstring(inp.readline());
C1 = Vector3.fromstring(inp.readline());
D = A + C - B
B1 = B + C1 - C
A1 = A + B1 - B
D1 = A1 + D - A
direction = Vector3.fromstring(inp.readline());
entry = Vector3.fromstring(inp.readline())
power = int(inp.readline())
n = int(inp.readline());

mirrors = []
cube = [Polygon(A,B,C,D),Polygon(A,A1,B1,B),Polygon(A,A1,D1,D),
        Polygon(C,C1,B1,B),Polygon(C,C1,D1,D),Polygon(A1,B1,C1,D1)]

for i in range(n):
    p1 = Vector3.fromstring(inp.readline())
    p2 = Vector3.fromstring(inp.readline())
    p3 = Vector3.fromstring(inp.readline())
    polygon = Polygon(p1,p2,p3)
    mirrors += [polygon]

ray = Line(direction, entry)


#############_DRAWING_BEGIN_######################
if DRAWING:
    from mpl_toolkits.mplot3d import Axes3D
    from mpl_toolkits.mplot3d.art3d import Poly3DCollection
    import matplotlib.pyplot as plt
    import numpy as np


    fig = plt.figure()
    ax = Axes3D(fig)

    def draw_polygon(polygon, alpha=0.1, linewidths=2, facecolor='b', edgecolor='black'):
        x = []
        y = []
        z = []
        for c in polygon.points:
            x += [c.x]
            y += [c.y]
            z += [c.z]
        verts = [list(zip(x,y,z))]
        ax.add_collection3d(Poly3DCollection(verts, alpha=alpha, linewidths=linewidths, 
                    facecolor=facecolor,edgecolor=edgecolor))

    def draw_line(p1,p2, edgecolor="yellow", linewidths=2, alpha=1):
        x = [p1.x, p2.x]
        y = [p1.y, p2.y]
        z = [p1.z, p2.z]
        verts = [list(zip(x,y,z))]
        ax.add_collection3d(Poly3DCollection(verts, alpha=alpha, linewidths=linewidths, edgecolor=edgecolor))

    def draw_point(p, linewidths=10, edgecolor="r"):
        x = [p.x + DRAW_EPS, p.x, p.x]
        y = [p.y, p.y + DRAW_EPS, p.y]
        z = [p.z, p.z, p.z + DRAW_EPS]
        verts = [list(zip(x,y,z))]
        ax.add_collection3d(Poly3DCollection(verts, linewidths=linewidths, edgecolor=edgecolor, facecolor=edgecolor))


    for c in cube:
        draw_polygon(c)

    for c in mirrors:
        draw_polygon(c,alpha=0.5,facecolor='r')
#############_DRAWING_END_######################

while True:
    if power <= 0:
        if DRAWING:
            draw_point(ray.p0, edgecolor='b')
            plt.show()
        out.write(str(0) + "\n")
        out.write("%f %f %f" % (ray.p0.x, ray.p0.y, ray.p0.z) + "\n")
        exit(0)
        
    
    m = 1e10
    mi = -1

    for i, mirror in enumerate(mirrors):
        if inPolygon(ray.p0, mirror):
            continue
        p = intersect(ray,mirror)

        if p != None and inPolygon(p,mirror)  and ray.s.dot(p - ray.p0) >= 0:
            if distance(p, ray.p0) < m:
                m = distance(p, ray.p0)
                mi = i

    for side in cube:
        if inPolygon(ray.p0, side):
            continue

        p = intersect(ray,side)


        if p != None and inPolygon(p,side) and ray.s.dot(p - ray.p0) >= 0:

            if distance(p, ray.p0) < m:
                out.write(str(1) + "\n")
                out.write(str(power) + "\n")
                out.write("%f %f %f" % (p.x, p.y, p.z) + "\n")
                out.write("%f %f %f" % (ray.s.x, ray.s.y, ray.s.z) + "\n")

                if DRAWING:
                    draw_polygon(side, facecolor="cyan")
                    draw_line(ray.p0,ray.getPoint(x=p.x))
                    draw_point(p, edgecolor="black")
                    plt.show()

                exit()

    p = intersect(ray,mirrors[mi])

    if DRAWING:
        draw_point(p)
        draw_line(ray.p0,ray.getPoint(x=p.x))

    power -= 1
    ray = Line(reflect(ray.s, mirrors[mi].n),p)



#############_DRAWING_FINAL_######################
if DRAWING:
    plt.show()

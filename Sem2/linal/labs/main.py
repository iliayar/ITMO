#!/usr/bin/python

import math
import datetime
import sys

DRAWING = "LOCAL" in sys.argv

DRAW_EPS = 0.01
EPS = 1e-9
PREC = 3


def angle(cls, v1, v2):
    try:
        cos = (v1.x*v2.x + v1.y*v2.y + v1.z*v2.z)/(v1.magnitude()*v2.magnitude())
        return cos
    except ZeroDivisionError:
        return 0.0

def distance(p1, p2):
    return math.sqrt((p1.x - p2.x)**2 + (p1.y - p2.y)**2 + (p1.z - p2.z)**2)


def log(*args):
    print("["+str(datetime.datetime.now())+"]", *args)

def toDegrees(angle):
    res =  angle/math.pi*180

    return res

class Vector3:

    def __init__(self ,x: float, y: float , z: float):
        self.x = 0.0 if x == 0 else x
        self.y = 0.0 if y == 0 else y
        self.z = 0.0 if z == 0 else z

    @classmethod
    def from_string(cls, s: str):
        s = list(map(float,s.split()))
        x = s[0]
        y = s[1]
        z = s[2]
        return cls(x,y,z)

    def sub(self, v):
        return self.add(v.mul(-1.0))

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
        return round(v.x*self.x + v.y*self.y + v.z*self.z, PREC)

    def cross(self,vect):
        nx = self.y * vect.z - self.z * vect.y
        ny = self.z * vect.x - self.x * vect.z
        nz = self.x * vect.y - self.y * vect.x
        return Vector3(nx,ny,nz)

    def magnitude(self):
        return math.sqrt(self.x**2 + self.y**2 + self.z**2) 

    def __str__(self):
        return "Vector3 (%f, %f, %f)\n" % (self.x, self.y, self.z)

    def __add__(self, v):
        return self.add(v)

    def __sub__(self, v):
        return self.sub(v)

    def __eq__(self, other):
        if(other == None):
            return False
        return (round(self.x, 2) == round(other.x, 2)
    and round(self.y, 2) == round(other.y, 2)
    and round(self.z, 2) == round(other.z, 2))

    def __hash__(self):
        return int(round(self.x, 2)*1337269**4 + round(self.y, 2)*1337269**3 + round(self.z, 2)*1337269**2) % 1337269

    def __ne__(self, other):
        return not self.__eq__(other)

class Line:


    def __init__(self, v, r):
        # self.s = v.mul(1/v.magnitude())
        self.intersects = []
        self.s = v
        self.r = r;

    def __str__(self):
        res = "Line (\n"
        res += "  r: " + str(self.r)
        res += "  s: " + str(self.s)
        res += "  intersects ( \n    " + '    '.join([str(i) for i in self.intersects]) + "  )\n"
        res += ")\n"
        return res

    def filterIntersects(self):
        m_dist = 0.0
        res = []
        for p1 in self.intersects:
            for p2 in self.intersects:
                if(p1 == p2):
                    continue
                if(round(distance(p1, p2), PREC) > m_dist):
                    m_dist = round(distance(p1, p2), PREC)
                    res = [p1, p2]
        self.intersects = res



    def getPoint(self, **axis):
        r = self.r
        s = self.s
        if('x' in axis):
            if s.x == 0:
                return None
            return Vector3(axis['x'], (axis['x'] - r.x)/s.x*s.y + r.y, (axis['x'] - r.x)/s.x*s.z + r.z)
        elif('y' in axis):
            if s.y == 0:
                return None
            return Vector3((axis['y'] - r.y)/s.y*s.x + r.x, axis['y'], (axis['y'] - r.y)/s.y*s.z + r.z)
        elif('z' in axis):
            if s.z == 0:
                return None
            return Vector3((axis['z'] - r.z)/s.z*s.x + r.x, (axis['z'] - r.z)/s.z*s.y + r.y, axis['z'])
        return None

    def intersect(self, plane):
        X = self.r
        A = plane.r

        v = A - X

        d = plane.n.dot(v)

        e = plane.n.dot(self.s)

        res = None

        if e != 0.0:
            res = Vector3(X.x + self.s.x*d/e,
                            X.y + self.s.y*d/e,
                            X.z + self.s.z*d/e)

        return res

class Plane:

    def __init__(self, n: Vector3, r: Vector3):
        self.n = n
        self.r = r
        self.d = -n.dot(r)

    @classmethod
    def from_string(cls, s: str):
        ns = list(map(float, s.split()))
        return cls(Vector3(ns[0], ns[1], ns[2]), Vector3(ns[3], ns[4], ns[5]))

    def __str__(self):
        res = "Plane (\n"
        res += "  r: " + str(self.r)
        res += "  n: " + str(self.n)
        res += ")\n"
        return res

    def intersect(self, other):
        s = self.n.cross(other.n)

        if(round(s.magnitude(), PREC) == 0.0):
            return None

        r = (s.cross(other.n).mul(self.d) + self.n.cross(s).mul(other.d)).mul(1/s.magnitude()**2);

        return Line(s, r);

    def getPoint(self, **axis):
        n = self.n
        d = self.d
        if('x' in axis and 'y' in axis):
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
        return -2*EPS <= self.n.x*p.x + self.n.y*p.y + self.n.z*p.z + self.d <= 2*EPS



def inFigure(figure, p):
    # log("inFigure " + str(p)[:-1])
    for plane in figure:
        # log(plane.n.dot(p - plane.r))
        if(plane.n.dot(p - plane.r) > 0):
            return False

    return True

inp = open("input.txt", "r")
out = open("output.txt", "w")


planes = []


m = int(inp.readline())

for i in range(m):
    planes += [Plane.from_string(inp.readline())]

inp.close()
#############_DRAWING_BEGIN_######################
if DRAWING:
    from mpl_toolkits.mplot3d import Axes3D
    from mpl_toolkits.mplot3d.art3d import Poly3DCollection
    import matplotlib.pyplot as plt
    import numpy as np

    MAX_COORD = 1

    fig = plt.figure()
    ax = Axes3D(fig)


    def draw_plane(plane, alpha=0.1, linewidths=2, facecolor='b', edgecolor='black'):
        points = [ plane.getPoint(x = 0, y = MAX_COORD)
                 , plane.getPoint(x = MAX_COORD, y = 0)
                 , plane.getPoint(x = MAX_COORD, z = 0)
                 , plane.getPoint(x = 0, z = MAX_COORD)
                 , plane.getPoint(y = 0, z = MAX_COORD)
                 , plane.getPoint(y = MAX_COORD, z = 0) ]
        draw_polygon(points, alpha, linewidths, facecolor, edgecolor)

    def draw_polygon(polygon, alpha=0.1, linewidths=2, facecolor='b', edgecolor='black'):
        x = []
        y = []
        z = []
        for c in polygon:
            if(c == None):
                continue
            x += [c.x]
            y += [c.y]
            z += [c.z]
        verts = [list(zip(x,y,z))]
        ax.add_collection3d(Poly3DCollection(verts, alpha=alpha, linewidths=linewidths, 
                    facecolor=facecolor,edgecolor=edgecolor))

    def draw_line(p1,p2, edgecolor="r", linewidths=2, alpha=1):
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
#############_DRAWING_END_######################

edges = []

for i in range(len(planes)):
    for j in range(i + 1, len(planes)):
        p1 = planes[i]
        p2 = planes[j]
        l = p1.intersect(p2)
        if(l == None):
            continue
        for p3 in planes:
            if(p1 == p3 or p2 == p3):
                continue
            intersection = l.intersect(p3);
            if(intersection == None):
                continue
            if(inFigure(planes, intersection)):
                l.intersects += [intersection]
        l.filterIntersects()
        if(len(l.intersects) == 2):
            edges += [l]
log(*edges)

F = len(planes)
E = len(edges)
v = []
for e in edges:
    v += [e.intersects[0]]
    v += [e.intersects[1]]
log(*set(v))
V = len(set(v))

log(F, V, E)

if DRAWING:
    for p in planes:
        draw_plane(p)
    for e in edges:
        int1 = e.intersects[0]
        int2 = e.intersects[1]
        draw_line(int1, int2)
    plt.show()


if F + V - E != 2:
    out.write("0\n")
    out.close()
    exit(0)


out.write(str(len(edges)) + '\n')
for e in edges:
    int1 = e.intersects[0]
    int2 = e.intersects[1]
    out.write(str(round(int1.x,PREC)) + ' ' + str(round(int1.y,PREC)) + ' ' + str(round(int1.z,PREC)) + ' ' +
              str(round(int2.x,PREC)) + ' ' + str(round(int2.y,PREC)) + ' ' + str(round(int2.z,PREC)) + '\n')

out.close()
exit(0)
#############_DRAWING_FINAL_######################
if DRAWING:
    plt.show()

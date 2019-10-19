class Matrix(object):
    def __init__(self,matrix,matrixType):
        self.matrix = matrix
        self.matrixType = matrixType
    
    def __add__(self, b):
        assert( Matrix.canSum(self,b) ), "Invalid"

        res = [len(self.matrix[0])*[0] for i in range(len(self.matrix))]

        for i in range(len(self.matrix)):
            for j in range(len(self.matrix[0])):
                res[i][j] = self.matrix[i][j] + b.matrix[i][j]

        return Matrix(res,self.matrixType)

    def __str__(self):
        s = ""

        for i in range(self.shape()[0]):
            for j in range(self.shape()[1]):
              s += str(self.matrix[i][j]) + " "
            # s = s[:-1] + "\n"

        return s[:-1]  

    def multiply_const(self,c):
        res = [len(self.matrix[0])*[0] for i in range(len(self.matrix))]

        for i in range(len(self.matrix)):
            for j in range(len(self.matrix[0])):
                res[i][j] = c*self.matrix[i][j];

        return Matrix(res,self.matrixType)

    def multiply_matrix(self,b):
        assert ( Matrix.canMultiply(self,b) )

        res = [len(b.matrix[0])*[0] for i in range(len(self.matrix))]
        for i in range(len(self.matrix)):
            for j in range(len(b.matrix[0])):
                s = 0
                for q in range(len(b.matrix)):
                    s += self.matrixType(self.matrix[i][q]) * self.matrixType(b.matrix[q][j])
                res[i][j] = s

        return Matrix(res,self.matrixType)

    def __mul__(self,c):
        if type(c) == Matrix:
            return self.multiply_matrix(c)
        else:
            return self.multiply_const(c)

    def transpose(self):
        res = [len(self.matrix)*[0] for i in range(len(self.matrix[0]))]

        for i in range(len(self.matrix)):
            for j in range(len(self.matrix[0])):
                res[j][i] = self.matrix[i][j];
        
        return Matrix(res,self.matrixType)

    def shape(self):
        return (len(self.matrix),len(self.matrix[0]))

    @staticmethod
    def parseMatrix(n,m,string,type):
        lst = list(map(type,string.split()))

        return Matrix([lst[i:i+m] for i in range(0,n*m,m)],type)

    @staticmethod
    def canMultiply(a,b):
        if a.shape()[1] != b.shape()[0]:
            return False
        return True

    @staticmethod
    def canSum(a,b):
        if ( a.shape() != b.shape() ):
            return False
        return True



with open("input.txt","r") as inp:
    def readMatrix(n,m):
        s = inp.readline()
        # while(len(s.split()) < n*m):
        #     s += " " + inp.readline()
        return s

    a, b = map(float,inp.readline().split())

    na, ma = map(int,inp.readline().split())
    A = Matrix.parseMatrix(na,ma,readMatrix(na,ma),float)

    nb, mb = map(int,inp.readline().split())
    B = Matrix.parseMatrix(nb,mb,readMatrix(nb,mb),float)

    nc, mc = map(int,inp.readline().split())
    C = Matrix.parseMatrix(nc,mc,readMatrix(nc,mc),float)

    nd, md = map(int,inp.readline().split())
    D = Matrix.parseMatrix(nd,md,readMatrix(nd,md),float)

    nf, mf = map(int,inp.readline().split())
    F = Matrix.parseMatrix(nf,mf,readMatrix(nf,mf),float)

    # print(C*(A*a + B.transpose()*b)*D)

    try:
        res = C*(A*a + B.transpose()*b).transpose()*D + F*(-1)
        with open("output.txt","w") as out:
            out.write("1\n")            
            out.write(str(res.shape()[0]) + " " + str(res.shape()[1]) + "\n")
            out.write(str(res) + "\n")
    except:
        with open("output.txt","w") as out:
            out.write("0\n")            
    

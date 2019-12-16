

def fact(n):
    res = 1;
    for i in range(1, n + 1):
        res *= i
    return res

def C(n , k):
    return fact(n)/fact(k)/fact(n-k)


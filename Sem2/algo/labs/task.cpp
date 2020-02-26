
// Generated at 2020-02-24 04:29:06.958539 
// By iliayar
#include <iostream>
#include <vector>
#include <chrono>
#include <algorithm>
#include <cstdio>


using namespace std;

#define ON 1
#define OFF 0

#define int long long
#define vint vector<int>
#ifdef LOCAL
#define DBG(x) cout << "DBG: " << x << endl;
#else
#define DBG(x)
#endif

//##################CODE BEGIN#############
#define FILE_IO ON
#define FILENAME "crypto"
#undef int

class Matrix {
public:
    int a[2][2];
    Matrix(int, int, int, int);
    Matrix operator*(Matrix m);
};


Matrix::Matrix(int a11, int a12, int a21, int a22) {
    this->a[0][0] = a11;
    this->a[0][1] = a12;
    this->a[1][0] = a21;
    this->a[1][1] = a22;
}


int MOD;

Matrix Matrix::operator* (Matrix m) {
    Matrix res(0,0,0,0);
    res.a[0][0] = (this->a[0][0]*m.a[0][0]%MOD + this->a[0][1]*m.a[1][0]%MOD) % MOD;
    res.a[1][0] = (this->a[1][0]*m.a[0][0]%MOD + this->a[1][1]*m.a[1][0]%MOD) % MOD;
    res.a[0][1] = (this->a[0][0]*m.a[0][1]%MOD + this->a[0][1]*m.a[1][1]%MOD) % MOD;
    res.a[1][1] = (this->a[1][0]*m.a[0][1]%MOD + this->a[1][1]*m.a[1][1]%MOD) % MOD;
    return res;
}

Matrix I(1,0,0,1);

vector<Matrix> tree;

void set(int i, Matrix x, int v, int lx, int rx) {
    if(rx - lx == 1) {
        tree[v] = x;
        return;
    }
    int m = (lx + rx)/2;
    if(i < m)
        set(i,x,v*2+1, lx, m);
    else
        set(i,x, v*2 + 2, m, rx);
    tree[v] = tree[v*2 + 1]*tree[v*2 + 2];
}

Matrix mult(int l, int r, int v, int lx, int rx) {
    if(r <= l) {
        return I;
    }
    if(l == lx && rx == r) {
        return tree[v];
    }

   int m = (lx + rx)/2;
   return mult(l,min(r,m),v*2+1, lx,m)*
       mult(max(l,m),r,v*2 + 2,m, rx);
}

//entry
void sol() {
    int n, m;
    cin >> MOD >> n >> m;
    tree.resize(n*4,I);
    for(int i = 0; i < n; ++i) {
        int a11, a12, a21, a22;
        cin >> a11 >> a12 >> a21 >> a22;
        set(i, Matrix(a11,a12, a21, a22), 0, 0, n);
    }
    for(int i = 0; i < m; ++i) {
        int l ,r;
        cin >> l >> r; l--;
        Matrix t = mult(l,r,0,0,n);
        cout << t.a[0][0] << " " << t.a[0][1] << endl;
        cout << t.a[1][0] << " " << t.a[1][1] << endl << endl;
    }

}

//##################CODE END###############
#ifdef LOCAL
#undef FILE_IO
#undef FILENAME
#define FILE_IO ON
#define FILENAME "local"
#endif

signed main() {
    ios_base::sync_with_stdio(0);
    cin.tie(0);
    #if FILE_IO == ON
    freopen(FILENAME".in", "r", stdin);
    freopen(FILENAME".out", "w", stdout);
    #endif
    #ifdef LOCAL
    auto start = std::chrono::high_resolution_clock::now();
    #endif

    sol();

    #ifdef LOCAL
    auto stop = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start);
    cout << duration.count() << " microseconds" << endl;
    #endif
}

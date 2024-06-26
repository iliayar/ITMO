
// Generated at 2022-03-07 00:48:21.166034 
// By iliayar
#pragma comment(linker, "/STACK:36777216")
#include <iostream>
#include <vector>
#include <chrono>
#include <algorithm>
#include <cmath>
#include <cstdio>
#include <map>
#include <unordered_set>
#include <ctime>
#include <cstdlib>
#include <queue>
#include <set>
#include <deque>
#include <list>
#include <sstream>


using namespace std;

#define ON 1
#define OFF 0

#define int long long
#ifdef LOCAL
#define DBG(x) cout << "DBG: " << x << endl
#define DBG_CODE(x) x
#else
#define DBG(x)
#define DBG_CODE(x)
#endif

#define INF 1e+18

using vint = vector<int>;
using vint2 = vector<vint>;

template<typename T>
class Join {
  T& v;
  string& separator;
  
public:
  
  Join(T v, string separator)
    : v(v), separator(separator)
  {}

  friend ostream& operator<<(ostream& out, Join<T> join) {
    for(auto it = join.v.cbegin(); it != join.v.cend(); ++it) {
      if(it != join.v.cbegin()) out << join.separator;
      out << *it;
    }
    return out;
  }
};

template<typename T>
ostream& operator<<(ostream& out, vector<T> v) {
  out << Join(v, " ") << endl;
  return out;
}

template<typename T, typename K>
ostream& operator<<(ostream& out, pair<T, K> p) {
  out << "(" << p.first << ", " << p.second << ")";
  return out;
}

//##################CODE BEGIN#############

struct Res {
    double micro;
    double macro;
    double F;
};

//entry
void sol() {
    
    int K; cin >> K;

    vector<vint> CM;
    vint nc(K, 0);
    int nca = 0;

    for (int i = 0; i < K; ++i) {
        vint v;
        for (int j = 0; j < K; ++j) {
            int n; cin >> n;
            v.push_back(n);
            nc[i] += n;
            nca += n;
        }
        CM.push_back(v);
    }

    Res res{0, 0, 0};

    double PrecW = 0, RecW = 0;
    double TPW = 0, FPW = 0, FNW = 0;

    for (int c = 0; c < K; ++c) {
        int TP = 0, TN = 0, FP = 0, FN = 0;
        for (int i = 0; i < K; ++i) {
            for (int j = 0; j < K; ++j) {
                if (i == c && j == c) {
                    TP += CM[i][j]; 
                }
                if (i != c && j == c) {
                    FP += CM[i][j]; 
                }
                if (i == c && j != c) {
                    FN += CM[i][j]; 
                }
                if (i != c && j != c) {
                    TN += CM[i][j]; 
                }
            }
        }
        DBG("Class: " << c);
        DBG("TP: " << TP << endl << "     TN: " << TN << endl << "     FP: " << FP << endl << "     FN: " << FN);
        double Prec = TP + FP == 0 ? 0 : (double)TP / (TP + FP);
        // DBG(Prec);
        double Rec = TP + FN == 0 ? 0 : (double)TP / (TP + FN);
        // DBG(Rec);
        double F = Prec + Rec == 0 ? 0 : 2. * (Prec * Rec) / (Prec + Rec);
        // DBG(F);
        res.F += F * nc[c];

        PrecW += Prec * nc[c];
        RecW += Rec * nc[c];

        TPW += TP * nc[c];
        FPW += FP * nc[c];
        FNW += FN * nc[c];
    }
    PrecW /= nca;
    RecW /= nca;
    res.macro = 2. * (PrecW * RecW) / (PrecW + RecW);

    TPW /= nca;
    FPW /= nca;
    FNW /= nca;

    double Prec = TPW + FPW == 0 ? 0 : (double)TPW / (TPW + FPW);
    double Rec = TPW + FNW == 0 ? 0 : (double)TPW / (TPW + FNW);
    double F = Prec + Rec == 0 ? 0 : 2. * (Prec * Rec) / (Prec + Rec);
    res.micro = F;

    cout << res.micro << endl;
    cout << res.macro << endl;
    cout << res.F / nca << endl;

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
    cin.tie(0); cout.tie(0);
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

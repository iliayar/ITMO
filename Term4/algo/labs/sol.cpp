#include "template.cpp"

vint2 A;
vint2 B;

// entry
void sol() {

    int n, m; cin >> n >> m;
    A.resize(n, vint());
    B.resize(m, vint());

    for (int i = 0; i < n; ++i) {
      int u;
      while(true) {
          cin >> u;
          if(u == 0) break;
          u--;
          A[i].push_back(u);
          B[u].push_back(i);
      }
    }

    DBG(A);
    DBG(B);
}

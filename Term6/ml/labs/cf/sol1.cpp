#include "template.cpp"
#include <algorithm>

//entry
void sol() {
    cout << fixed;
    cout.precision(17);
    int K; cin >> K;
    vint ls;
    for (int i = 0; i < K; ++i) {
        int t; cin >> t;
        ls.push_back(t);
    }
    int alpha; cin >> alpha;
    int N; cin >> N;
    vector<map<string, int>> c(K);
    vint cc(K);
    set<string> ww;
    for (int i = 0; i < N; ++i) {
        int C; cin >> C; C--;
        int L; cin >> L;
        set<string> tw;
        for (int j = 0; j < L; ++j) {
            string w; cin >> w;
            ww.insert(w);
            tw.insert(w);
        }
        for (auto const& w : tw) {
            c[C][w] += 1;
        }
        cc[C] += 1;
    }

    // DBG(c);
    // DBG(cc);

    
    int M; cin >> M;
    for (int i = 0; i < M; ++i) {
        int L; cin >> L;
        set<string> ws;
        for (int j = 0; j < L; ++j) {
            string w; cin >> w;
            ws.insert(w);
        }

        vector<double> r;
        for (int j = 0; j < K; ++j) {
          double res = log(cc[j]) - log(N) + log(ls[j]);
          for (auto& w : ww) {
              double a = c[j][w] + alpha;
              double b = cc[j] + 2 * alpha;
              // DBG("Class: " << j << "\tWord: " << w << "\t" << make_pair(a, b));
              if (ws.find(w) != ws.end()) {
                  res += log(a) - log(b);
              } else {
                res += log(b - a) - log(b);
              }
          }
          r.push_back(res);
        }
        double mv = *max_element(r.begin(), r.end());
        double st = 0;
        for (auto v : r) {
            st += exp(v - mv);
        }
        st = log(st) + mv;
        for (auto v : r) {
            cout << exp(v - st) << " ";
        }
        cout << endl;
    }
}

#include "template.cpp"

//entry
void sol() {
    int n, m; cin >> n >> m;
    vector<vector<double>> A(m, vector<double>(n));
    vector<double> b(m);
    vector<double> c(n);
    for (int i = 0; i < m; ++i) {
        for (int j = 0; j < n; ++j) {
            cin >> A[i][j];
        }
        cin >> b[i];
    }
    for (int i = 0; i < n; ++i) {
        cin >> c[i];
    }

    for (int i = 0; i < m; ++i) {
        double s = 0;
        for (int j = 0; j < n; ++j) {
            s += 
        }
    }
}

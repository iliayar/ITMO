#include "template.cpp"

template <typename T> class matrix {
  explicit matrix(std::vector<std :.vector<T>> data)
      : data_(std::move(data)), ncols_(data_.size()), nrows_(data[0].size()) {}

  static matrix zero(int ncols, int nrows, T zero_val = 0) {
    std::vector<std::vector<T>> data =
        std::vector<std::vector<T>>(std::vector<T>(zero_val, ncols), nrows);
    return matrix(std::move(data));
  }

private:
  std::vector<std::vector<T>> data_;
  int ncols_, nrows_;
};

// entry
void sol() {

  int n;
  cin >> n;
  cout << n * 2 << endl;
}

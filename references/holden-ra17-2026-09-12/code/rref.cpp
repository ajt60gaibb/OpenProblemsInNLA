// Exact reduced row echelon form over Q, using GMP rationals.
// Compile: g++ -std=c++17 -O2 rref.cpp -lgmpxx -lgmp -o rref
// Input: m n, followed by m*n integer or rational entries.
// Output: rank n; pivot columns; the nonzero rows of the RREF.
#include <gmpxx.h>
#include <algorithm>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <vector>

int main(int argc, char** argv) {
    try {
        if (argc != 3) throw std::runtime_error("usage: rref INPUT OUTPUT");
        std::ifstream in(argv[1]);
        if (!in) throw std::runtime_error("cannot open input file");
        int m = 0, n = 0;
        if (!(in >> m >> n) || m <= 0 || n <= 0 || m > 10000 || n > 10000)
            throw std::runtime_error("invalid matrix dimensions");
        std::vector<std::vector<mpq_class>> a(m, std::vector<mpq_class>(n));
        for (auto& row : a) for (auto& q : row) {
            if (!(in >> q)) throw std::runtime_error("missing/invalid matrix entry");
            if (q.get_den() == 0) throw std::runtime_error("zero denominator");
            q.canonicalize();
        }
        int row = 0;
        std::vector<int> pivots;
        for (int j = 0; j < n && row < m; ++j) {
            int pivot_row = -1;
            size_t best_size = 0;
            for (int i = row; i < m; ++i) if (a[i][j] != 0) {
                size_t size = mpz_sizeinbase(a[i][j].get_num().get_mpz_t(), 2)
                            + mpz_sizeinbase(a[i][j].get_den().get_mpz_t(), 2);
                if (pivot_row < 0 || size < best_size) {
                    pivot_row = i; best_size = size;
                }
            }
            if (pivot_row < 0) continue;
            std::swap(a[pivot_row], a[row]);
            mpq_class pivot = a[row][j];
            for (int k = j + 1; k < n; ++k) a[row][k] /= pivot;
            a[row][j] = 1;
            for (int i = 0; i < m; ++i) if (i != row && a[i][j] != 0) {
                mpq_class factor = a[i][j]; a[i][j] = 0;
                for (int k = j + 1; k < n; ++k)
                    if (a[row][k] != 0) a[i][k] -= factor * a[row][k];
            }
            pivots.push_back(j); ++row;
        }
        std::ofstream out(argv[2]);
        if (!out) throw std::runtime_error("cannot open output file");
        out << row << ' ' << n << '\n';
        for (int j : pivots) out << j << ' '; out << '\n';
        for (int i = 0; i < row; ++i) {
            for (const auto& q : a[i]) out << q << ' '; out << '\n';
        }
        if (!out) throw std::runtime_error("failed while writing output");
        std::cout << "exact RREF rank " << row << " of " << m << " x " << n << '\n';
    } catch (const std::exception& e) {
        std::cerr << "rref: " << e.what() << '\n'; return 1;
    }
}

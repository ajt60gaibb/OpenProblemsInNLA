// Independent-language check of the supplied n=7 integer CSV certificate.
// No JSON library or optimization solver. Optional; the Python verifier suffices.
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
using Matrix = std::vector<std::vector<std::int64_t>>;
void require(bool ok, const std::string& message) {
    if (!ok) throw std::runtime_error(message);
}
Matrix read_csv(const std::string& path) {
    std::ifstream stream(path);
    require(bool(stream), "Cannot open " + path);
    Matrix out;
    std::string line;
    while (std::getline(stream, line)) {
        require(!line.empty(), "Empty CSV row");
        std::istringstream fields(line);
        std::vector<std::int64_t> row;
        std::string field;
        while (std::getline(fields, field, ',')) {
            std::size_t used = 0;
            const auto value = std::stoll(field, &used);
            require(used == field.size(), "Noninteger CSV field");
            row.push_back(value);
        }
        out.push_back(row);
    }
    return out;
}
int main(int argc, char** argv) {
    try {
        require(argc == 2, "usage: verify_csv DATA_DIRECTORY");
        const std::string dir = argv[1];
        const Matrix W = read_csv(dir + "/W_n7.csv");
        const Matrix H = read_csv(dir + "/H_scaled_n7.csv");
        const Matrix denominators = read_csv(dir + "/column_denominators_n7.csv");
        require(W.size() == 128 && H.size() == 127, "Wrong factor heights");
        require(denominators.size() == 1 && denominators[0].size() == 128, "Wrong denominator shape");
        for (const auto& row : W) {
            require(row.size() == 127, "Wrong W width");
            for (auto x : row) require(0 <= x && x <= 2, "W entry outside [0,2]");
        }
        for (const auto& row : H) {
            require(row.size() == 128, "Wrong H width");
            for (auto x : row) require(0 <= x && x <= 36, "H entry outside [0,36]");
        }
        for (auto d : denominators[0]) require(1 <= d && d <= 36, "Invalid denominator");
        // All products are at most 127*2*36=9144; int64_t cannot overflow.
        for (unsigned a = 0; a < 128; ++a) for (unsigned b = 0; b < 128; ++b) {
            std::int64_t actual = 0;
            for (unsigned k = 0; k < 127; ++k) actual += W[a][k] * H[k][b];
            const std::int64_t x = 1 - __builtin_popcount(a & b);
            require(actual == x*x*denominators[0][b],
                    "Incorrect entry (" + std::to_string(a) + "," + std::to_string(b) + ")");
        }
        std::cout << "PASS: C++ CSV check of all 16384 integer-scaled entries.\n"
                  << "PASS: all factor entries nonnegative; denominators positive; 127 < 128.\n";
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "FAIL: " << e.what() << '\n';
        return 1;
    }
}

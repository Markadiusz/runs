#include "runs_expos.hpp"

map<int, vector<int>> rules;

vector<int> ab_to_01(string s) {
    vector<int> ret;
    for (auto& c : s) {
        ret.emplace_back(c - 'a');
    }
    return ret;
}

string transform(int x) {
    if (x == 0) {
        return "ababa";
    }
    if (x == 1) {
        return "ababbaba";
    }
    string ret;
    for (auto t : rules[x]) {
        ret += transform(t);
    }
    return ret;
}

int main() {
    cout << setprecision(10) << fixed;

    rules[2] = {0, 1, 0, 0, 1, 0, 1};
    rules[3] = {0, 1, 0, 0, 1, 0, 1, 1};
    rules[4] = {0, 1, 0, 0, 1, 0, 1, 1, 0, 1};
    rules[5] = {4, 3, 2, 4, 2};
    rules[6] = {4, 3, 2, 4, 2, 3, 2};
    rules[7] = {4, 3, 2, 4, 2, 3, 2, 4, 2};
    rules[8] = {7, 6, 5};
    rules[9] = {7, 6, 5, 6};
    rules[10] = {7, 6, 5, 7, 6};
    rules[11] = {8, 9, 10};
    rules[12] = {8, 9, 10, 9};
    rules[13] = {8, 9, 10, 9, 10};
    rules[14] = {12, 11};
    rules[15] = {12, 11, 13};
    rules[16] = {14, 15, 15, 15};
    rules[17] = {14, 15, 15, 15, 15};
    rules[18] = {16, 17};
    rules[19] = {16, 17, 17};
    rules[20] = {18, 19, 19, 18, 19, 19, 19, 18, 19, 19, 18, 19, 19, 19, 18, 19, 19, 18, 19, 19};

    vector<int> x_20 = ab_to_01(transform(20));
    cout << "Exp(x_20): " << calc_exp(x_20) << "n" << endl;
}

#include <bits/stdc++.h>
using namespace std;

using LL=long long;
#define FOR(i,l,r)for(int i=(l);i<=(r);++i)
#define REP(i,n)FOR(i,0,(n)-1)
#define ssize(x)int(x.size())

using D = double;
using V = vector<int>;
using Run = tuple<int, int, int>; // {period, left, right}

constexpr bool prove_general = true; // general or binary alphabet
const D target = 2.3;
const int exploration_limit = 10;
int INITIAL_SIZE = 10'000;
const int CORES = 12;

constexpr D eps = 1e-9;
bool equal(D a, D b) {
    return abs(a - b) < eps;
}
bool leq(D a, D b) {
    return equal(a, b) or a < b;
}
bool lth(D a, D b) {
    return not equal(a, b) and a < b;
}

int get_ord(int a, int b) {
    assert(a != b);
    return a < b ? 0 : 1;
}
bool cmp(int type, int a, int b) {
    if (type == 0)
        return a < b;
    if (type == 1)
        return a > b;
    assert(false);
}

bool compare_substrings_lth(const V& v, int a, const int b, int c, const int d, const int ord) {
    while (a <= b and c <= d) {
        if (cmp(ord, v[a], v[c]))
            return true;
        if (cmp(ord, v[c], v[a]))
            return false;
        ++a, ++c;
    }
    return c <= d;
}

array<V, 2> get_lyn(const V& v) {
    const int n = ssize(v);
    array<V, 2> lyn = {V(n, 1), V(n, 1)};
    REP(ord, 2) {
        for (int i = n - 1; i >= 0; --i) {
            int j = i + 1;
            while (j < n and compare_substrings_lth(v, i, j - 1, j, j + lyn[ord][j] - 1, ord)) {
                lyn[ord][i] = lyn[ord][i] + lyn[ord][j];
                j = j + lyn[ord][j];
            }
        }
    }
    return lyn;
}

vector<V> expand_right(V v) {
    if constexpr (prove_general) {
        vector<V> ret;
        const int M = *max_element(v.begin(), v.end());
        ret.reserve(M + 1);
        FOR(i, 0, M + 1) {
            auto h = v;
            h.emplace_back(i);
            ret.emplace_back(h);
        }
        return ret;
    }
    else {
        auto zero = v;
        zero.emplace_back(0);
        auto one = zero;
        one.back() = 1;
        return {zero, one};
    }
}

vector<V> expand_left(V v) {
    reverse(v.begin(), v.end());
    auto ret = expand_right(v);
    for (auto& h : ret)
        reverse(h.begin(), h.end());
    return ret;
}

D get_bound(const V& v, int left, int right) {
    const int n = ssize(v);

    const auto lyn = get_lyn(v);

    auto get_lroots = [&](Run r, const auto& ord) -> vector<int> {
        const auto [p, i, j] = r;
        vector<int> ret;
        ret.reserve((j - i + 1) / p - 1);

        int k = i + 1;
        while (lyn[ord][k] != p)
            ++k;
        while (k <= j - p + 1) {
            ret.emplace_back(k);
            k += p;
        }
        return ret;
    };

    auto extend_with_period = [&](int l, int r) {
        const int p = r - l + 1;
        while (l > 0 and v[l - 1] == v[l - 1 + p])
            --l;
        while (r < n - 1 and v[r + 1] == v[r + 1 - p])
            ++r;
        return pair(l, r);
    };

    vector<bool> considered(n);
    D ret = 0;

    auto mark_and_eval = [&](Run run, const auto& ord) -> pair<D, int> {
        const auto& [p, i, j] = run;
        const auto lroots = get_lroots(run, ord);
        vector<int> inside;
        for (auto x : lroots) {
            if (x >= left and x <= right) {
                inside.emplace_back(x);
                considered[x] = true;
            }
        }
        if (inside.empty())
            return {0, 0};
        int l, r;
        if (inside[0] == lroots[0]) {
            l = i > 0 ? i : inside[0] - p;
        }
        else {
            l = inside[0];
        }
        if (inside.back() == lroots.back()) {
            r = j < n - 1 ? j : inside.back() + 2 * p - 2;
        }
        else {
            r = inside.back() + p - 1;
        }
        return {D(r - l + 1) / D(p), ssize(inside)};
    };

    const auto get_runs = [&]() -> vector<Run> {
        vector<Run> runs;
        runs.reserve(n);
        vector<uint64_t> seen(n);
        auto add_run = [&seen, &runs](int p, int i, int j) {
            assert(p < 64);
            if ((seen[i] >> p) & 1)
                return;
            seen[i] |= (1ull << p);
            runs.emplace_back(p, i, j);
        };
        FOR(k, 1, n - 1) {
            const int p = v[k] == v[k - 1] ? 1 : lyn[get_ord(v[k], v[k - 1])][k];
            const auto [l, r] = extend_with_period(k, k + p - 1);
            if (r - l + 1 >= 2 * p) {
                add_run(p, l, r);
            }
        }
        return runs;
    };

    for (const auto& run : get_runs()) {
        const auto& [p, i, j] = run;
        if (j < n - 1 or p == 1) {
            auto ord = p == 1 and j == n - 1 ? 0 : get_ord(v[j + 1], v[j + 1 - p]);
            ret += mark_and_eval(run, ord).first;
        }
        else {
            D value = 0;
            auto [bound_inc, cnt_inc] = mark_and_eval(run, 0);
            auto [bound_dec, cnt_dec] = mark_and_eval(run, 1);
            value = max(value, bound_inc + cnt_dec * 3);
            value = max(value, bound_dec + cnt_inc * 3);
            ret += value;
        }
    }

    FOR(i, left, right) {
        if (considered[i])
            continue;
        [&]() {
            if (i > 0) {
                const int p = lyn[get_ord(v[i], v[i - 1])][i];
                const int j = i + p - 1;
                auto [l, r] = extend_with_period(i, j);
                if (l > 0 and r < n - 1 and r - l + 1 < 2 * p) {
                    return;
                }
            }
            ret += 3;
        }();
    }

    ret /= D(right - left + 1);
    return ret;
}

V reverse_ordering(V v) {
    const int m = *max_element(v.begin(), v.end());
    for (auto& x : v)
        x = m - x;
    return v;
}

D get_expected_bound(const V& v, int left, int right) {
    const int n = ssize(v);
    D ret = 0;
    LL orderings = 0;
    const int m = *max_element(v.begin(), v.end());
    vector<int> permutation(m + 1);
    iota(permutation.begin(), permutation.end(), 0);
    do {
        V h(n);
        REP(i, n) {
            h[i] = permutation[v[i]];
        }
        // skip if prec_0 > prec_1
        if (h > reverse_ordering(h))
            continue;
        ++orderings;
        ret += get_bound(h, left, right);
    } while (next_permutation(permutation.begin(), permutation.end()));
    ret /= D(orderings);
    return ret;
}

bool can_be_bounded(const V& v) {
    set<tuple<D, int, int, V>> s;
    s.emplace(get_expected_bound(v, 0, ssize(v) - 1), 0, 0, v);
    REP(i, exploration_limit) {
        {
            int cnt = 0;
            for (const auto& [b, _, _2, _3] : s) {
                cnt += lth(target, b);
            }
            // we cannot improve the bound within the exploration_limit
            if (cnt > exploration_limit - i)
                return false;
        }
        auto [bound, left, right, h] = *prev(s.end());
        // check if bound is already good enough
        if (leq(bound, target))
            return true;
        s.erase(prev(s.end()));
        auto get_descendants = [&](const vector<V>& children, int l, int r) {
            D value = 0;
            vector<pair<D, V>> ret;
            ret.reserve(ssize(children));
            for (const auto& c : children) {
                D cur = get_expected_bound(c, l, ssize(c) - 1 - r);
                value = max(value, cur);
                ret.emplace_back(cur, c);
            }
            return pair(pair(value, max(l, r)), ret);
        };
        auto [max_left, v_left] = get_descendants(expand_left(h), left + 1, right);
        auto [max_right, v_right] = get_descendants(expand_right(h), left, right + 1);
        if (max_left <= max_right) {
            for (auto [c_bound, c] : v_left) {
                s.emplace(c_bound, left + 1, right, c);
            }
        }
        else {
            for (auto [c_bound, c] : v_right) {
                s.emplace(c_bound, left, right + 1, c);
            }
        }
    }
    const auto bound = get<0>(*prev(s.end()));
    return leq(bound, target);
}

atomic<LL> leaves;

void prove_bound(const V& v) {
    if (can_be_bounded(v)) {
        ++leaves;
        return;
    }
    for (const auto& h : expand_right(v)) {
        prove_bound(h);
    }
}

mutex mut;
vector<V> strings;
int done = 0;
using Time = chrono::time_point<chrono::high_resolution_clock>;
Time start;

void work() {
    while (true) {
        mut.lock();
        if (strings.empty()) {
            mut.unlock();
            break;
        }
        const auto v = strings.back();
        strings.pop_back();
        mut.unlock();

        prove_bound(v);

        // estimates remaining time
        mut.lock();
        ++done;
        const Time current = chrono::high_resolution_clock::now();
        const auto elapsed_seconds = chrono::duration_cast<chrono::seconds>(current - start).count();
        const int prediction = int(D(INITIAL_SIZE - done) * D(elapsed_seconds) / D(done));
        cerr << "\rDONE " << done << " / " << INITIAL_SIZE << ", ESTIMATED FINISH IN " << prediction << " SECONDS\t\t" << flush;
        mut.unlock();
    }
}

void generate_initial_trie() {
    // {length, node}
    set<pair<int, V>> s;
    s.emplace(1, V{0});
    while (ssize(s) and ssize(s) < INITIAL_SIZE) {
        auto [d, v] = *s.begin();
        s.erase(s.begin());
        for (auto h : expand_right(v)) {
            if (can_be_bounded(h)) {
                ++leaves;
            }
            else {
                s.emplace(d + 1, h);
            }
        }
    }
    INITIAL_SIZE = max(INITIAL_SIZE, ssize(s));

    for (auto [_, v] : s)
        strings.emplace_back(v);
    shuffle(strings.begin(), strings.end(), mt19937(0));
}

int main() {
    generate_initial_trie();

    cout << "FINISHED INITIAL TRIE GENERATION" << endl;

    // multithreading setup
    start = chrono::high_resolution_clock::now();
    vector<thread> threads;
    REP(i, CORES) {
        threads.emplace_back(work);
    }
    REP(i, CORES) {
        threads[i].join();
    }

    cout << endl;
    cout << "FINISHED PROOF" << endl;
    cout << "LEAVES: " << leaves << endl;
}

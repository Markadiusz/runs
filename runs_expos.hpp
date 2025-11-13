// Portions of this file are taken/adapted from acmlib (Tomasz Nowak, 2019) — MIT License

#ifndef __RUNS_EXPOS_HPP__
#define __RUNS_EXPOS_HPP__

#include "headers.hpp"

struct RMQ {
    vector<vector<int>> st;
    RMQ(const vector<int> &a) {
        int n = ssize(a), lg = 0;
        while((1 << lg) < n) lg++;
        st.resize(lg + 1, a);
        FOR(i, 1, lg) REP(j, n) {
            st[i][j] = st[i - 1][j];
            int q = j + (1 << (i - 1));
            if(q < n) st[i][j] = min(st[i][j], st[i - 1][q]);
        }
    }
    int query(int l, int r) {
        int q = __lg(r - l + 1), x = r - (1 << q) + 1;
        return min(st[q][l], st[q][x]);
    }
};

void induced_sort(const vector<int> &vec, int alpha, vector<int> &sa,
        const vector<bool> &sl, const vector<int> &lms_idx) {
    vector<int> l(alpha), r(alpha);
    for (int c : vec) {
        if (c + 1 < alpha)
            ++l[c + 1];
        ++r[c];
    }
    partial_sum(l.begin(), l.end(), l.begin());
    partial_sum(r.begin(), r.end(), r.begin());
    fill(sa.begin(), sa.end(), -1);
    for (int i = ssize(lms_idx) - 1; i >= 0; --i)
        sa[--r[vec[lms_idx[i]]]] = lms_idx[i];
    for (int i : sa)
        if (i >= 1 and sl[i - 1])
            sa[l[vec[i - 1]]++] = i - 1;
    fill(r.begin(), r.end(), 0);
    for (int c : vec)
        ++r[c];
    partial_sum(r.begin(), r.end(), r.begin());
    for (int k = ssize(sa) - 1, i = sa[k]; k >= 1; --k, i = sa[k])
        if (i >= 1 and not sl[i - 1])
            sa[--r[vec[i - 1]]] = i - 1;
}
vector<int> sa_is(const vector<int> &vec, int alpha) {
    const int n = ssize(vec);
    vector<int> sa(n), lms_idx;
    vector<bool> sl(n);
    for (int i = n - 2; i >= 0; --i) {
        sl[i] = vec[i] > vec[i + 1] or (vec[i] == vec[i + 1] and sl[i + 1]);
        if (sl[i] and not sl[i + 1])
            lms_idx.emplace_back(i + 1);
    }
    reverse(lms_idx.begin(), lms_idx.end());
    induced_sort(vec, alpha, sa, sl, lms_idx);
    vector<int> new_lms_idx(ssize(lms_idx)), lms_vec(ssize(lms_idx));
    for (int i = 0, k = 0; i < n; ++i)
        if (not sl[sa[i]] and sa[i] >= 1 and sl[sa[i] - 1])
            new_lms_idx[k++] = sa[i];
    int cur = sa[n - 1] = 0;
    REP (k, ssize(new_lms_idx) - 1) {
        int i = new_lms_idx[k], j = new_lms_idx[k + 1];
        if (vec[i] != vec[j]) {
            sa[j] = ++cur;
            continue;
        }
        bool flag = false;
        for (int a = i + 1, b = j + 1;; ++a, ++b) {
            if (vec[a] != vec[b]) {
                flag = true;
                break;
            }
            if ((not sl[a] and sl[a - 1]) or (not sl[b] and sl[b - 1])) {
                flag = not (not sl[a] and sl[a - 1] and not sl[b] and sl[b - 1]);
                break;
            }
        }
        sa[j] = (flag ? ++cur : cur);
    }
    REP (i, ssize(lms_idx))
        lms_vec[i] = sa[lms_idx[i]];
    if (cur + 1 < ssize(lms_idx)) {
        vector<int> lms_sa = sa_is(lms_vec, cur + 1);
        REP (i, ssize(lms_idx))
            new_lms_idx[i] = lms_idx[lms_sa[i]];
    }
    induced_sort(vec, alpha, sa, sl, new_lms_idx);
    return sa;
}
vector<int> suffix_array(const vector<int> &s) {
    int alpha = *max_element(s.begin(), s.end()) + 1;
    vector<int> vec(ssize(s) + 1);
    REP(i, ssize(s))
        vec[i] = s[i] + 1;
    vector<int> ret = sa_is(vec, alpha + 2);
    return ret;
}
pair<vector<int>, vector<int>> get_lcp_rank(const vector<int> &s) {
    const vector<int> sa = suffix_array(s);
    int n = ssize(s), k = 0;
    vector<int> lcp(n), rank(n);
    REP (i, n)
        rank[sa[i + 1]] = i;
    for (int i = 0; i < n; i++, k ? k-- : 0) {
        if (rank[i] == n - 1) {
            k = 0;
            continue;
        }
        int j = sa[rank[i] + 2];
        while (i + k < n and j + k < n and s[i + k] == s[j + k])
            k++;
        lcp[rank[i]] = k;
    }
    lcp.pop_back();
    lcp.insert(lcp.begin(), 0);
    return {lcp, rank};
}

using D = double;
using Run = tuple<int, int, int>; // {p, i, j}
using S = vector<int>;
S operator+(S a, const S& b) {
    a.insert(a.end(), b.begin(), b.end());
    return a;
}

vector<Run> get_runs(S v) {
    if (v.empty())
        return {};
    const int n = ssize(v);
    vector<Run> runs;

    auto rev = v;
    reverse(rev.begin(), rev.end());

    auto [lcp, rank_p] = get_lcp_rank(v);
    RMQ rmq_p(lcp);
    auto [lcs, rank_s] = get_lcp_rank(rev);
    RMQ rmq_s(lcs);

    auto query_pref = [&](int i, int j) {
        if (max(i, j) >= n)
            return 0;
        assert(i != j);
        i = rank_p[i];
        j = rank_p[j];
        if (i > j)
            swap(i, j);
        return rmq_p.query(i + 1, j);
    };
    auto query_suff = [&](int i, int j) {
        if (min(i, j) < 0)
            return 0;
        assert(i != j);
        i = n - 1 - i;
        j = n - 1 - j;
        i = rank_s[i];
        j = rank_s[j];
        if (i > j)
            swap(i, j);
        return rmq_s.query(i + 1, j);
    };

    auto consider = [&](int i, int j) {
        const int p = j - i + 1;
        int right = query_pref(i, j + 1);
        int left = query_suff(i - 1, j);
        const int new_i = i - left;
        const int new_j = j + right;
        if (2 * p <= new_j - new_i + 1) {
            runs.emplace_back(p, new_i, new_j);
        }
    };

    auto check = [&](int a, int b, int c, int d) {
        REP(k, n) {
            if (c + k > d)
                return false;
            if (a + k > b)
                return true;
            if (v[a + k] < v[c + k])
                return true;
            if (v[a + k] > v[c + k])
                return false;
        }
        assert(false);
    };

    auto work = [&]() {
        vector<int> lyn(n);
        for (int i = n - 1; i >= 0; --i) {
            lyn[i] = 1;
            int j = i + 1;
            while (j < n and check(i, j - 1, j, j + lyn[j] - 1)) {
                lyn[i] += lyn[j];
                j += lyn[j];
            }
        }
        FOR(i, 1, n - 1) {
            consider(i, i + lyn[i] - 1);
        }
    };
    work();
    const int alpha = *max_element(v.begin(), v.end()) + 1;
    for (auto& x : v)
        x = alpha - 1 - x;
    work();
    sort(runs.begin(), runs.end());
    runs.erase(unique(runs.begin(), runs.end()), runs.end());
    return runs;
}

pair<int, D> get_expos(S v) {
    auto runs = get_runs(v);

    int cnt_runs = 0;
    D expos = 0;
    for (auto [p, i, j] : runs) {
        cnt_runs += 1;
        expos += D(j - i + 1) / D(p);
    }
    return {cnt_runs, expos};
}

D calc_exp(const S& v) {
    return get_expos(v).second / D(ssize(v));
}

#endif // __RUNS_EXPOS_HPP__

Upper bound compilation:

g++ prove_upper_bound.cpp -std=c++20 -O3


Lower bound compilation:

g++ prove_lower_bound.cpp -std=c++20 -O3


prove_upper_bound parameters:

INITIAL_SIZE is the size of the initial trie. Because the generation of this initial trie is single-threaded, it is advisable to decrease this parameter when proving larger targets.

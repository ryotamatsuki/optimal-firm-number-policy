# Observed session output (2026-11-17 JST)
The direct-cell implementation was executed in Python in the review session. The separate first attempt used too few periodic copies for a singleton and failed the mass check; widened copies to -2..2, then all tests passed. This is a code correction, not a model change. The committed script consolidates the executed cells (loop-local variable names changed to avoid shadowing the welfare witness); the combined file has not separately been rerun from GitHub.
pairs=68 thresholds=3486 exists=3486 outside_common=2991 local_disjoint=325 qualifying_window_disjoint=154 uniform_pairs=3
Counts of local and qualifying cases overlap; not summed as independent tests.
Intro A H,T,K=(3/10,1/2,3/5), B=(3/10,1/2,13/20).
At 1/5 both only all four shares (1/4,3/20,1/4,7/20).
At 2/5 both only {1,3,4}, A=(7/20,3/10,7/20), B=(13/40,13/40,7/20).
At 3/5 A has {1,3,4},{1,4},{2,4}; B has {1,3,4},{2,4}; common {2,4} shares (1/2,1/2).
Exact finite-menu known-state costs U=285003/2000000 C=330001/2000000; deterministic minimax=17101/1000000; randomized minimax=384755399/39600000000 with support 0 and 21/40, probability on 0=22499/39600. All 42 actions have common signal, 1/2 disjoint. U optimum all menu thresholds <=19/40; C optimum only 21/40; deterministic optimum all low thresholds.
At 0 or 19/40 costs U=285003/2000000 C=364203/2000000; at 1/2 U=307253/2000000 C=346653/2000000; at 21/40 U=C=330001/2000000; at 3 U=C=2.
Interior overlap at .4: retained {1,2}, both shares=(1/2,1/2).
Blind A={0,3} both optimally choose 0, costs as above.
Strict witness gamma=801/80000 Delta=599/80000.
Quadratic t=1: U optimal 21/40,23/40,5/8,27/40,29/40; C only 21/40; common optimum 21/40. Thus same fixed-cost welfare conflict not portable.
Density .5+x: U full shares (1999503/8000000,301101/1600000,399699/1600000,2496497/8000000); C (2599103/8000000,261021/1600000,359779/1600000,2296897/8000000). Nonuniform density breaks baseline equivalence.

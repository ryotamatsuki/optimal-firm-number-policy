# S03 — canonical model and proposition register
Checkpoint: 2026-11-17 JST. The model is not frozen for manuscript development; strategic primitives are fixed for the bounded Stage 4 reopening.

## Primitives and timing
Unit circle, unit mass of uniformly distributed consumers. Distinct fixed candidate locations z_i. Each of N firms simultaneously chooses active/inactive; common price p and marginal cost c, margin m=p-c>0; common real fixed cost F>0; t>0 linear geodesic transport disutility. Consumer utility v-p-t*d(x,z_i), outside option 0. Assume v sufficiently high for full coverage when any firm active (v-p>t/2 suffices). No active firms -> welfare 0. Each active firm receives uniform lump-sum transfer s in R (negative s is tax). Inactive payoff zero. Neutral financing, no distortionary tax cost. No endogenous price/location or firm-specific policy. Nash equilibrium, including independent mixed strategies when expressly stated.

## Accounting and benchmark
For nonempty S sorted around circle with gaps d_k, sum d_k=1. For |S|>=2, q_i=(d_left+d_right)/2; for singleton q_i=1. Transport cost T=t*sum(d_k^2)/4, singleton gap 1. CS=v-p-T; PS=m-|S|F+|S|s; government balance=-|S|s. W=v-c-|S|F-T; W(empty)=0. Cost C=|S|F+T, with C(empty)=v-c for comparable ranking. Planner selects any subset of fixed candidate sites. This is a fixed-location constrained first best, NOT unrestricted first best. Pure optimistic restricted-instrument optimum maximizes W over (s,S in pure NE(s)); maximin over all NE (including mixed) maximizes worst expected welfare.

## P1: weak pure equilibrium implementability
theta=2(F-s)/m. For a nonempty proper set with >=2 active firms, H=min active adjacent-gap sum; G=max length of occupied-by-inactive-candidate gap. Pure NE iff G<=theta<=H; possible for some real s iff G<=H. Bound on s: F-mH/2 <=s<= F-mG/2. Singleton H=2, G=1 if inactive candidates exist; all active no lower bound; empty NE iff theta>=2. Weak inequalities permit ties and multiple NE. This is a specialization of elementary binary incentive inequalities, not an independent novelty claim. A feasible set need not be uniquely implemented.

## P2: nonimplementation and numerical example
z=(0,.12,.24,.62,.63), F=.005, t=1, v-c=2; label A,B,C,D,E. Margin .1 in historical enumeration; theta absorbs margin. Exact all 32 subsets:
| S | Cost | Pure implementability |
|---|---:|---|
| ABCD | .09940 | no, G=.38>H=.24 |
| ABCE | .09945 | no, G=.39>H=.24 |
| ACD | .10160 | yes |
| ACE | .10165 | yes |
| ABCDE | .10255 | yes |
| ACDE | .10475 | yes |
ABCD is unique constrained optimum. A mixed NE cannot attain this exact welfare: equality requires probability 1 on ABCD, which is not a NE for any common transfer. Do not assert an optimal optimistic mixed policy is characterized. Stage 4A printed a conservative 93.46% probability bound and .00000327 expected welfare gap; see code/log; ancillary result only, not core, re-audit before use.

## P3: central surviving contribution
In the above example the best pure implementable subset has 3 firms (ACD); the unique constrained planner optimum has 4 (ABCD). Best implementable four-set is ACDE; its cost exceeds ACD by .00315. This is existential within the fixed-price spatial model, not universal. Strict inequalities yield local robustness where the relevant feasibility and ranking inequalities remain strict; general structural conditions remain to be derived and independently audited.

## P4: Stage 7 evidence, additional certification required
theta=.30 -> ACDE; theta=.385 -> ACD. Strict dominance elimination in archived script yields unique NE including independent mixed at each of these policies. All theta regimes in this five-site example have a pure NE (enumerated exact boundary/interval representatives); hence maximin value over mixed-inclusive NE <= best implementable pure welfare. theta=.385 achieves this bound. No favorable selection needed for this particular comparison. Do not generalize to arbitrary N/site geometry. All pure and mixed characterization not claimed. No optimistic mixed optimum result.
At fixed geometry t=1, archived Stage 7 reports constrained ABCD optimum for .00185<F<.0072 and robust ACD optimum for .004525<F<.0384; claimed overlap .004525<F<.0072. Recheck breakpoints and quantifiers before promotion. Government feasibility permits taxes as well as subsidies; not a nonnegative-subsidy result.

## Next theorem target (not yet proved)
A non-knife-edge structural sufficient condition in geometry and relative fixed cost F/t under unchanged primitives, not simply a new example or a restatement of the general incentive condition. State which planner and equilibrium selection benchmark is proved. Analyze cases/boundaries, natural falsifiers, exact counterexamples and generality. Reopen Stage 4A/6 for any stronger result. No claim of genericity or unrestricted price competition; no author sign-off or formal proof yet.

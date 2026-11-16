# Stage 7.5A — durable formal verification certificate supplement
2026-11-17 JST. This supplements STAGE_075A_2026-11-17.md (blob 5177aa12df5b2c8acd45f6e0fe6d784944d810c5), superseding ONLY its previous incomplete formal-verification state. The Stage 7.5A author intellectual-contribution checkpoint remains OPEN; no Stage 8 freeze. Verified again via GitHub connector: run 43970310321 completed success, exact tested PR head c8bff78c20af069e421bf20166173b3a02bb1b03. Prior PR body retained below as evidence, including all explicit hypotheses/scope exclusions. The PR is still draft and unmerged. This is an AI-prepared documentation supplement, not a human review.
# RC01 R1 — Stage 7.5A proof-critical Lean certification
Status: **FORMAL VERIFICATION PASS — selected proof-critical core.** Run 43970310321 completed SUCCESS, clean `lake build --wfail` (8,656 Lake jobs) and `AXIOM AUDIT PASS: 53 declarations`. Stage 7.5A author intellectual-contribution checkpoint remains OPEN; no Stage 8 freeze.

- Exact candidate commit: c8bff78c20af069e421bf20166173b3a02bb1b03
- Source blob: 7486e06aa76d03e694a20ac5a2a14a0aebb10bde
- [Source and exact signatures](https://github.com/ryotamatsuki/optimal-firm-number-policy/blob/c8bff78c20af069e421bf20166173b3a02bb1b03/formal/rc01/RC01Proof.lean)
- [Successful final run](https://github.com/ryotamatsuki/optimal-firm-number-policy/actions/runs/43970310321), job 133660426177, [retained audit artifact](https://github.com/ryotamatsuki/optimal-firm-number-policy/actions/runs/43970310321/artifacts/14278695972) (7-day retention).
- [First failed build](https://github.com/ryotamatsuki/optimal-firm-number-policy/actions/runs/43968983418); syntax and warning fixes.
- [Second failed build](https://github.com/ryotamatsuki/optimal-firm-number-policy/actions/runs/43969566067); local reserved identifier / two redundant tactic warnings. Retained as negative evidence.
- [Third failed build](https://github.com/ryotamatsuki/optimal-firm-number-policy/actions/runs/43969966061): parser ambiguity in finite_probe_in_intersection, repaired without changing scope.
- Lean 4.32.1, mathlib v4.32.1 locked at 520045ab14e26149ee970e2e617ca04b09bde5d6, inherited dependencies pinned in lake-manifest.json; ordinary public Ubuntu runner.
- Reproduce from clean checkout: cd formal/rc01; lake exe cache get; lake build --wfail; lake env lean RC01Proof.lean 2>&1 | tee lean-audit.log; python3 audit.py.

## Statement-fidelity target ledger (analytic economic inputs explicitly supplied)
| Claim | Formal target | Assumption boundary / encoded conclusion |
|---|---|---|
| E | binary_equilibrium_iff; delete_preserves_noentry; exists_equilibrium_below; exists_pure_equilibrium | For arbitrary finite label set and doubled-share payoff table, all unilateral binary deviations iff weak participation constraints. Given local merged-gap payoff law (analytically derived for circle including empty/singleton), finite deletion proves a pure equilibrium exists at every real threshold. No general uniqueness claim. |
| P1/P2 | two_step_difference; even_step_difference; odd_period_identifies; cycle_parity_sums; compatible_gap_differs_everywhere; zero_window_uniform; finite_probe_in_intersection | Adjacent-sum equality and periodic endpoint/total arc encode exact full-market shares. Prove parity/odd recovery and strict finite dyadic reach into both cutoffs given H<T and H<K; triple_min_above_H supplies latter from positive gaps and attained triple min. Full empirical order and share derivation not mechanized. |
| P4a | even_arc_invariant; parity_measure_invariant; family_parity_data_invariant; family_common_below; outside_window_family; missed_window; shared_observer_exists; same_history | For arbitrary state family with compatible adjacent sums, economic entry data on subsets of retained parity expressed by even arcs/constant (analytic geometry), and parity no-entry bound at T, existence of a single common pure outcome across family for theta<=H or theta>=T. Shared observer exists on menus missing open interval; identical finite histories given same deterministic rule (condition on any random seed analytically). Does not equate entire equilibrium correspondence or every selector. |
| P4b | junction_exists; triple_signal_changes; isolated_from_triple_bound; interior_signal_separation; interior_window_certificate | For any pure profile satisfying local stay/idle, full-share min and parity-max witnesses, adjacent-omission gap lower bounds and local measured triple share identities, H<theta<T and theta<K imply separation of one retained labeled share for every such profile. P4 sufficient H<theta<T with T<=K implies theta<K. Same active profile in candidate worlds; if active sets differ signal already differs. Does not assume K necessary. |
| P3/P5 | transfer_cancel; merge_linear; split_saving_bound; isolated_removal_bound; split_path_gain; removal_path_gain; positive_path_gain; empty_welfare_bound; perturbed_share_bounds; perturbed_triple_bound; perturbation_menu | Exact fiscal-neutral accounting, local gap-add/remove gain bounds, finite edit sequences, nonempty and empty cost comparison, perturbation signs and strict menu exclusion. Allocation/cost path existence and endpoints from analytically derived ordered gap geometry; not formalized continuous integration or complete circle topology. |
| P5 decision | robust_welfare_from_profiles; deterministic_regret; no_common_optimum; randomized_regret; witness_bounds | Given attained worst costs and attained optima on same menu (finite nonempty in model) and analytically established profile-wise bounds, derive distinct optimal actions and deterministic and randomized worst pure regret lower bounds, exact positive numeric witness. No claim of fixed persistent selector realized regret, mixed policy equilibria, exact general minimax value. |

The economic interface hypotheses are given assumptions, not proof escapes. The code encodes the mathematical steps from the local circle allocation relations to equilibrium existence, parity invariance, junction signal change, finite probe, and welfare decision bounds. Exact Voronoi consumer measure/integration, full combinatorial indexing of every circular profile, geometric feasibility of each edit sequence, construction of the attained extrema and full adaptive randomized process remain analytically certified outside Lean. Those exclusions are deliberate: target the highest-risk proof implications without representing a continuous consumer measure theory or the entire economic model as kernel-verified. The previous Stage 4A numerical and analytic counterexamples and Stage 7.5A portability limitations remain governing. No substantive changes to model or article claims. No external human/author verification provided. The tested source has 53 theorem declarations and 53 dependency queries, no banned proof escape tokens in source. CI directly checked all declarations; only propext, Classical.choice and Quot.sound appeared in the dependency audit. No project-specific assumptions disguised as added axioms; supplied economic assumptions are explicit in signatures. No proof gaps. Statement-fidelity audit of the selected components complete; full economic derivation remains analytic, not kernel verified. AI constructed and audited the encoding, FORMAL kernel + COMPUTATION audit independently establish encoded propositions, no AUTHOR/EXTERNAL HUMAN verification. If the model, theorem scope or certified code changes, invalidate or rerun this certificate and all affected gates. Stage 7.5A remains conditional solely pending actual author-accountability evidence. No Stage 8 freeze, manuscript changes, merge, or submission.


## Directly retrieved final CI evidence excerpt (unaltered lines)
```text
2026-11-16T22:30:07.7962581Z Lean (version 4.32.1, x86_64-unknown-linux-gnu, commit f054605aea4b840552cca2e725580bffd1e1b704, Release)
2026-11-16T22:30:17.7897410Z Build completed successfully (8656 jobs).
2026-11-16T22:30:24.1645200Z AXIOM AUDIT PASS: 53 declarations
2026-11-16T22:30:23.9481208Z 'RC01.binary_equilibrium_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9481938Z 'RC01.delete_preserves_noentry' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9482434Z 'RC01.exists_equilibrium_below' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9483101Z 'RC01.exists_pure_equilibrium' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9483549Z 'RC01.common_equilibrium_below' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9483982Z 'RC01.arc_two' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9484404Z 'RC01.even_arc_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9484892Z 'RC01.compatible_gap_differs_everywhere' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9485364Z 'RC01.triple_signal_changes' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9485790Z 'RC01.parity_sum_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9486192Z 'RC01.parity_upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9486590Z 'RC01.window_order' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9486992Z 'RC01.junction_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9487428Z 'RC01.interior_signal_separation' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9487875Z 'RC01.isolated_from_triple_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9488324Z 'RC01.missed_window' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9488674Z 'RC01.same_history' depends on axioms: [propext]
2026-11-16T22:30:23.9489156Z 'RC01.perturbation_menu' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9489775Z 'RC01.transfer_cancel' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9490178Z 'RC01.merge_linear' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9490571Z 'RC01.merge_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9491001Z 'RC01.split_saving_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9491430Z 'RC01.isolated_removal_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9491854Z 'RC01.cumulative_saving' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9492278Z 'RC01.deterministic_regret' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9492851Z 'RC01.no_common_optimum' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9493317Z 'RC01.randomized_regret' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9493726Z 'RC01.witness_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9494130Z 'RC01.two_step_difference' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9494549Z 'RC01.even_step_difference' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9495235Z 'RC01.odd_period_identifies' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9495665Z 'RC01.pair_sum_arc' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9496045Z 'RC01.arc_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9496427Z 'RC01.cycle_parity_sums' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9496829Z 'RC01.lower_sum_eq_all' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9497361Z 'RC01.zero_window_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9497807Z 'RC01.parity_measure_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9498267Z 'RC01.family_parity_data_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9498703Z 'RC01.family_common_below' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9499136Z 'RC01.outside_window_family' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9499528Z 'RC01.shared_observer_exists' depends on axioms: [Classical.choice]
2026-11-16T22:30:23.9499945Z 'RC01.interior_window_certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9500370Z 'RC01.pow_two_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9500763Z 'RC01.finite_dyadic_probe' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9501184Z 'RC01.perturbed_share_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9501632Z 'RC01.robust_welfare_from_profiles' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9502076Z 'RC01.triple_min_above_H' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9502524Z 'RC01.finite_probe_in_intersection' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9543246Z 'RC01.split_path_gain' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9543671Z 'RC01.removal_path_gain' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9544080Z 'RC01.positive_path_gain' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9544495Z 'RC01.empty_welfare_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-16T22:30:23.9544932Z 'RC01.perturbed_triple_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```
This preserves the final kernel/axiom evidence beyond the 7-day artifact retention interval. No rerun or new theory undertaken in this turn. GitHub Actions CI and standard axiom names do not establish author understanding, external novelty, or empirical relevance.
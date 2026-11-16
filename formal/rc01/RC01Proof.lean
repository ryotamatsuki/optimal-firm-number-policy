import Mathlib

namespace RC01
open scoped BigOperators

-- The economic allocation equations are supplied by the analytical circle model.
-- Doubled demand is used throughout the binary participation game.
section Game
variable {I : Type*} [DecidableEq I]

def NoEntry (q : Finset I → I → ℝ) (θ : ℝ) (S : Finset I) : Prop :=
  ∀ i, i ∉ S → q (insert i S) i ≤ θ

def Stay (q : Finset I → I → ℝ) (θ : ℝ) (S : Finset I) : Prop :=
  ∀ i, i ∈ S → θ ≤ q S i

def Equilibrium (q : Finset I → I → ℝ) (θ : ℝ) (S : Finset I) : Prop :=
  NoEntry q θ S ∧ Stay q θ S

def payoff (q : Finset I → I → ℝ) (θ : ℝ) (S : Finset I) (i : I) : ℝ :=
  if i ∈ S then q S i - θ else 0

theorem binary_equilibrium_iff (q : Finset I → I → ℝ) (θ : ℝ) (S : Finset I) :
    Equilibrium q θ S ↔
      ((∀ i ∈ S, payoff q θ (S.erase i) i ≤ payoff q θ S i) ∧
       (∀ i ∉ S, payoff q θ (insert i S) i ≤ payoff q θ S i)) := by
  constructor
  · rintro ⟨hn, hs⟩
    constructor
    · intro i hi
      have h := hs i hi
      simp [payoff, hi]
      linarith
    · intro i hi
      have h := hn i hi
      simp [payoff, hi]
      linarith
  · rintro ⟨hs, hn⟩
    constructor
    · intro i hi
      have h := hn i hi
      simp [payoff, hi] at h
      linarith
    · intro i hi
      have h := hs i hi
      simp [payoff, hi] at h
      linarith

-- Local circle allocation fact: deleting a site either leaves an idle
-- entrant's doubled share unchanged or makes it equal to the deleted
-- site's doubled share (the merged gap, including one/zero-site cases).
def MergeLaw (q : Finset I → I → ℝ) : Prop :=
  ∀ S i, i ∈ S → ∀ j, j ∉ S.erase i →
    q (insert j (S.erase i)) j = q S i ∨
      (j ∉ S ∧ q (insert j (S.erase i)) j = q (insert j S) j)

theorem delete_preserves_noentry {q : Finset I → I → ℝ} {θ : ℝ}
    (law : MergeLaw q) {S : Finset I} {i : I}
    (hn : NoEntry q θ S) (hi : i ∈ S) (loss : q S i < θ) :
    NoEntry q θ (S.erase i) := by
  intro j hj
  rcases law S i hi j hj with he | ⟨hjS, he⟩
  · rw [he]
    exact le_of_lt loss
  · rw [he]
    exact hn j hjS

theorem exists_equilibrium_below {q : Finset I → I → ℝ} {θ : ℝ}
    (law : MergeLaw q) (S : Finset I) (hn : NoEntry q θ S) :
    ∃ R : Finset I, R ⊆ S ∧ Equilibrium q θ R := by
  classical
  have aux : ∀ n : ℕ, ∀ P : Finset I, P.card = n → NoEntry q θ P →
      ∃ R : Finset I, R ⊆ P ∧ Equilibrium q θ R := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro P hc hp
      by_cases hs : Stay q θ P
      · exact ⟨P, fun _ h => h, hp, hs⟩
      · unfold Stay at hs
        push Not at hs
        obtain ⟨i, hi, hl⟩ := hs
        have hlt : (P.erase i).card < n := by
          rw [← hc]
          exact Finset.card_erase_lt_of_mem hi
        obtain ⟨R, hr, he⟩ := ih _ hlt (P.erase i) rfl
          (delete_preserves_noentry law hp hi hl)
        exact ⟨R, fun _ hj => (Finset.mem_erase.mp (hr hj)).2, he⟩
  exact aux S.card S rfl hn

theorem exists_pure_equilibrium [Fintype I] {q : Finset I → I → ℝ} {θ : ℝ}
    (law : MergeLaw q) : ∃ R : Finset I, Equilibrium q θ R := by
  classical
  obtain ⟨R, _, he⟩ := exists_equilibrium_below law Finset.univ (by
    intro i hi
    exact False.elim (hi (Finset.mem_univ i)))
  exact ⟨R, he⟩

-- Invariant payoff-with-entry data on every subset of one parity imply
-- identical equilibrium and observed active demands on that restricted set.
theorem common_equilibrium_below {q r : Finset I → I → ℝ} {θ : ℝ}
    {P : Finset I} (law : MergeLaw q) (hn : NoEntry q θ P)
    (inv : ∀ S : Finset I, S ⊆ P → ∀ i, q (insert i S) i = r (insert i S) i) :
    ∃ S : Finset I, S ⊆ P ∧ Equilibrium q θ S ∧ Equilibrium r θ S ∧
      (∀ i ∈ S, q S i = r S i) := by
  obtain ⟨S, hsub, hq⟩ := exists_equilibrium_below law P hn
  have hobs : ∀ i ∈ S, q S i = r S i := by
    intro i hi
    have h := inv S hsub i
    simpa [Finset.insert_eq_of_mem hi] using h
  have hr : Equilibrium r θ S := by
    constructor
    · intro i hi
      rw [← inv S hsub i]
      exact hq.1 i hi
    · intro i hi
      rw [← hobs i hi]
      exact hq.2 i hi
  exact ⟨S, hsub, hq, hr, hobs⟩
end Game

-- Oriented periodic gaps are indexed by natural numbers. Equality of every
-- adjacent sum is exactly the equality of full-activity doubled shares.
def arc (d : ℕ → ℝ) (i k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, d (i+j)

theorem arc_two (d : ℕ → ℝ) (i : ℕ) :
    arc d i 2 = d i + d (i+1) := by
  simp [arc, Finset.sum_range_succ]

theorem even_arc_invariant (d e : ℕ → ℝ)
    (h : ∀ i, d i + d (i+1) = e i + e (i+1)) (i k : ℕ) :
    arc d i (2*k) = arc e i (2*k) := by
  induction k with
  | zero => simp [arc]
  | succ k ih =>
    have hk : 2*(k+1) = 2*k+1+1 := by omega
    change arc d i (2*(k+1)) = arc e i (2*(k+1))
    rw [hk]
    unfold arc at *
    simp only [Finset.sum_range_succ, ih]
    have he := h (i+2*k)
    rw [show i+(2*k+1) = (i+2*k)+1 by omega]
    linarith

theorem compatible_gap_differs_everywhere {d e : ℕ → ℝ}
    (h : ∀ i, d i + d (i+1) = e i + e (i+1))
    (different : ∃ i, d i ≠ e i) : ∀ j, d j ≠ e j := by
  intro j hj
  have back : ∀ k, d k = e k → d 0 = e 0 := by
    intro k
    induction k with
    | zero => exact fun h0 => h0
    | succ k ih =>
      intro hk
      apply ih
      have he := h k
      change d (k+1) = e (k+1) at hk
      linarith
  have h0 := back j hj
  have forward : ∀ k, d k = e k := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih =>
      have he := h k
      change d (k+1) = e (k+1)
      linarith
  obtain ⟨k,hk⟩ := different
  exact hk (forward k)

theorem triple_signal_changes {d e : ℕ → ℝ}
    (h : ∀ i, d i + d (i+1) = e i + e (i+1))
    (different : ∃ i, d i ≠ e i) (i : ℕ) :
    d i + d (i+1) + d (i+2) ≠ e i + e (i+1) + e (i+2) := by
  intro he
  apply compatible_gap_differs_everywhere h different (i+2)
  linarith [h i]

theorem parity_sum_bound (f : ℕ → ℝ) (a : ℝ) (n : ℕ)
    (h : ∀ i < n, a ≤ f i) : (n : ℝ)*a ≤ ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h n (by omega)
    linarith

theorem parity_upper_bound (f : ℕ → ℝ) (a : ℝ) (n : ℕ)
    (h : ∀ i < n, f i ≤ a) : (∑ i ∈ Finset.range n, f i) ≤ (n : ℝ)*a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h n (by omega)
    linarith

theorem window_order (he ho : ℕ → ℝ) (n : ℕ) (H E O : ℝ)
    (se : (∑ i ∈ Finset.range n, he i) = 1)
    (so : (∑ i ∈ Finset.range n, ho i) = 1)
    (lowE : ∀ i < n, H ≤ he i) (lowO : ∀ i < n, H ≤ ho i)
    (upE : ∀ i < n, he i ≤ E) (upO : ∀ i < n, ho i ≤ O) :
    (n : ℝ)*H ≤ 1 ∧ 1 ≤ (n : ℝ)*min E O := by
  have he1 := parity_sum_bound he H n lowE
  have ho1 := parity_sum_bound ho H n lowO
  have he2 := parity_upper_bound he E n upE
  have ho2 := parity_upper_bound ho O n upO
  constructor
  · linarith [he1, ho1]
  · rcases le_total E O with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith

-- Crucial combinatorial junction: isolated omissions, with both parity
-- classes barred from wholesale omission, force a mixed local pattern.
theorem junction_exists (active : ℕ → Bool) (h : ℕ → ℝ) (θ T : ℝ)
    (omitted : ∃ i, active i = false)
    (isolated : ∀ i, active i = false → active (i+1) = true)
    (noentry : ∀ i, active i = false → h i ≤ θ)
    (evenmax : ∃ k, T ≤ h (2*k))
    (oddmax : ∃ k, T ≤ h (2*k+1))
    (inside : θ < T) :
    ∃ i, (active i = false ∧ active (i+1) = true ∧ active (i+2) = true) ∨
          (active i = true ∧ active (i+1) = true ∧ active (i+2) = false) := by
  by_contra hn
  have skip : ∀ i, active i = false → active (i+2) = false := by
    intro i hi
    cases he : active (i+2) with
    | false => rfl
    | true => exact False.elim (hn ⟨i, Or.inl ⟨hi, isolated i hi, he⟩⟩)
  have advance : ∀ i, active i = true → active (i+1) = true → active (i+2) = true := by
    intro i hi hj
    cases he : active (i+2) with
    | false => exact False.elim (hn ⟨i, Or.inr ⟨hi,hj,he⟩⟩)
    | true => rfl
  have no0 : active 0 ≠ false := by
    intro h0
    have ev : ∀ k, active (2*k) = false := by
      intro k
      induction k with
      | zero => simpa using h0
      | succ k ih =>
        rw [show 2*(k+1) = 2*k+2 by omega]
        exact skip _ ih
    obtain ⟨k,hk⟩ := evenmax
    exact (not_lt_of_ge (le_trans hk (noentry _ (ev k)))) inside
  have no1 : active 1 ≠ false := by
    intro h1
    have od : ∀ k, active (2*k+1) = false := by
      intro k
      induction k with
      | zero => simpa using h1
      | succ k ih =>
        rw [show 2*(k+1)+1 = (2*k+1)+2 by omega]
        exact skip _ ih
    obtain ⟨k,hk⟩ := oddmax
    exact (not_lt_of_ge (le_trans hk (noentry _ (od k)))) inside
  have all : ∀ k, active k = true ∧ active (k+1) = true := by
    intro k
    induction k with
    | zero =>
      constructor
      · cases he : active 0 <;> simp_all
      · cases he : active 1 <;> simp_all
    | succ k ih =>
      exact ⟨ih.2, advance k ih.1 ih.2⟩
  obtain ⟨i,hi⟩ := omitted
  have ht := (all i).1
  simp_all

-- Local measured share equations at a junction are the economic interface.
-- The theorem derives separation, rather than taking injectivity as input.
theorem interior_signal_separation (active : ℕ → Bool) (d e h q r : ℕ → ℝ)
    (θ T : ℝ)
    (compatible : ∀ i, d i+d (i+1) = e i+e (i+1))
    (different : ∃ i, d i ≠ e i)
    (omitted : ∃ i, active i = false)
    (isolated : ∀ i, active i = false → active (i+1) = true)
    (noentry : ∀ i, active i = false → h i ≤ θ)
    (evenmax : ∃ k, T ≤ h (2*k))
    (oddmax : ∃ k, T ≤ h (2*k+1))
    (inside : θ < T)
    (left : ∀ i, active i = false → active (i+1) = true → active (i+2) = true →
      q (i+1) = d i+d (i+1)+d (i+2) ∧ r (i+1) = e i+e (i+1)+e (i+2))
    (right : ∀ i, active i = true → active (i+1) = true → active (i+2) = false →
      q (i+1) = d (i+1)+d (i+2)+d (i+3) ∧ r (i+1) = e (i+1)+e (i+2)+e (i+3)) :
    ∃ i, active i = true ∧ q i ≠ r i := by
  obtain ⟨i, hi | hi⟩ := junction_exists active h θ T omitted isolated noentry evenmax oddmax inside
  · obtain ⟨hq, hr⟩ := left i hi.1 hi.2.1 hi.2.2
    exact ⟨i+1, hi.2.1, by rw [hq,hr]; exact triple_signal_changes compatible different i⟩
  · obtain ⟨hq, hr⟩ := right i hi.1 hi.2.1 hi.2.2
    refine ⟨i+1, hi.2.1, ?_⟩
    rw [hq,hr]
    simpa [Nat.add_assoc] using triple_signal_changes compatible different (i+1)

theorem isolated_from_triple_bound (active : ℕ → Bool) (g : ℕ → ℝ) (θ T K : ℝ)
    (inside : θ < T) (three : T ≤ K)
    (lower : ∀ i, K ≤ g i)
    (adjacent : ∀ i, active i = false → active (i+1) = false → g i ≤ θ) :
    ∀ i, active i = false → active (i+1) = true := by
  intro i hi
  cases h : active (i+1) with
  | true => rfl
  | false => exact False.elim ((not_lt_of_ge (le_trans three (le_trans (lower i) (adjacent i hi h)))) inside)

theorem missed_window {A : Set ℝ} {H T : ℝ}
    (miss : ∀ x ∈ A, ¬ (H < x ∧ x < T)) :
    ∀ x ∈ A, x ≤ H ∨ T ≤ x := by
  intro x hx
  by_cases lo : x ≤ H
  · exact Or.inl lo
  · right
    by_contra hi
    exact miss x hx ⟨lt_of_not_ge lo, lt_of_not_ge hi⟩

def history {α σ : Type*} (choose : List σ → α) (observe : α → σ) : ℕ → List σ
  | 0 => []
  | n+1 => let past := history choose observe n; past ++ [observe (choose past)]

theorem same_history {α σ : Type*} (choose : List σ → α) (f g : α → σ)
    (h : ∀ x, f x = g x) : ∀ n, history choose f n = history choose g n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [history, ih, h]

theorem perturbation_menu {A : Set ℝ} {L R H T : ℝ}
    (partition : ∀ x ∈ A, x ≤ L ∨ R ≤ x)
    (hL : L < H) (hR : T < R) :
    ∀ x ∈ A, ¬ (H < x ∧ x < T) := by
  intro x hx hi
  rcases partition x hx with lo | high
  · linarith [hi.1]
  · linarith [hi.2]

theorem transfer_cancel (v p c k F s D : ℝ) :
    (v - p - D) + (p - c - k * F + k * s) - k * s =
      v - c - k * F - D := by ring

theorem merge_linear (a b t : ℝ) :
    t*((a+b)^2-a^2-b^2)/4 = t*a*b/2 := by ring

theorem merge_quadratic (a b t : ℝ) :
    t*((a+b)^3-a^3-b^3)/12 = t*a*b*(a+b)/4 := by ring

theorem split_saving_bound {a b l t F : ℝ}
    (hl : 0 ≤ l) (ha : l ≤ a) (hb : l ≤ b) (ht : 0 ≤ t) :
    t*l^2/2-F ≤ t*a*b/2-F := by
  have hab : l*l ≤ a*b :=
    mul_le_mul ha hb hl (le_trans hl ha)
  have hh := mul_le_mul_of_nonneg_left hab ht
  nlinarith

theorem isolated_removal_bound {a b A B t F : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : a ≤ A) (hB : b ≤ B) (ht : 0 ≤ t) :
    F-t*A*B/2 ≤ F-t*a*b/2 := by
  have hab : a*b ≤ A*B := mul_le_mul hA hB hb (le_trans ha hA)
  have hh := mul_le_mul_of_nonneg_left hab ht
  nlinarith

-- Accumulating the per-site improvements for any number of distinct edits.
theorem cumulative_saving (cost : ℕ → ℝ) (delta : ℝ) (n : ℕ)
    (h : ∀ i < n, delta ≤ cost i - cost (i+1)) :
    (n : ℝ)*delta ≤ cost 0 - cost n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h n (by omega)
    change delta ≤ cost n - cost (n+1) at h2
    change ((n : ℝ)+1)*delta ≤ cost 0 - cost (n+1)
    linarith

-- Loss bounds are against the known-state optimum on the SAME menu.
theorem deterministic_regret {A : Set ℝ} {L R gamma delta : ℝ}
    {rU rC : ℝ → ℝ} (part : ∀ x ∈ A, x ≤ L ∨ R ≤ x)
    (low : ∀ x ∈ A, x ≤ L → delta ≤ rC x)
    (high : ∀ x ∈ A, R ≤ x → gamma ≤ rU x) :
    ∀ x ∈ A, min gamma delta ≤ max (rU x) (rC x) := by
  intro x hx
  rcases part x hx with lo | hi
  · exact le_trans (min_le_right _ _) (le_trans (low x hx lo) (le_max_right _ _))
  · exact le_trans (min_le_left _ _) (le_trans (high x hx hi) (le_max_left _ _))

theorem no_common_optimum {A : Set ℝ} {L R gamma delta : ℝ}
    {rU rC : ℝ → ℝ} (hg : 0 < gamma) (hd : 0 < delta)
    (part : ∀ x ∈ A, x ≤ L ∨ R ≤ x)
    (low : ∀ x ∈ A, x ≤ L → delta ≤ rC x)
    (high : ∀ x ∈ A, R ≤ x → gamma ≤ rU x) :
    ¬ ∃ x ∈ A, rU x = 0 ∧ rC x = 0 := by
  rintro ⟨x,hx,hu,hc⟩
  rcases part x hx with lo | hi
  · have h := low x hx lo; linarith
  · have h := high x hx hi; linarith

theorem randomized_regret {gamma delta p rU rC : ℝ}
    (hg : 0 < gamma) (hd : 0 < delta)
    (hu : (1-p)*gamma ≤ rU) (hc : p*delta ≤ rC) :
    gamma*delta/(gamma+delta) ≤ max rU rC := by
  have h1 := mul_le_mul_of_nonneg_left (le_trans hu (le_max_left rU rC)) (le_of_lt hd)
  have h2 := mul_le_mul_of_nonneg_left (le_trans hc (le_max_right rU rC)) (le_of_lt hg)
  apply (div_le_iff₀ (show 0 < gamma+delta by linarith)).2
  nlinarith only [h1,h2]

theorem witness_bounds :
    (1/4-1/200 : ℝ)^2/2-1/50 = 801/80000 ∧
    (1/50 : ℝ)-(1/20+1/200)*(9/20+1/200)/2 = 599/80000 ∧
    (801/80000 : ℝ)*(599/80000)/((801/80000)+(599/80000)) = 479799/112000000 := by
  norm_num

#print axioms binary_equilibrium_iff
#print axioms delete_preserves_noentry
#print axioms exists_equilibrium_below
#print axioms exists_pure_equilibrium
#print axioms common_equilibrium_below
#print axioms arc_two
#print axioms even_arc_invariant
#print axioms compatible_gap_differs_everywhere
#print axioms triple_signal_changes
#print axioms parity_sum_bound
#print axioms parity_upper_bound
#print axioms window_order
#print axioms junction_exists
#print axioms interior_signal_separation
#print axioms isolated_from_triple_bound
#print axioms missed_window
#print axioms same_history
#print axioms perturbation_menu
#print axioms transfer_cancel
#print axioms merge_linear
#print axioms merge_quadratic
#print axioms split_saving_bound
#print axioms isolated_removal_bound
#print axioms cumulative_saving
#print axioms deterministic_regret
#print axioms no_common_optimum
#print axioms randomized_regret
#print axioms witness_bounds
end RC01

namespace RC01
open scoped BigOperators

theorem two_step_difference {d e : ℕ → ℝ}
    (h : ∀ i, d i + d (i+1) = e i + e (i+1)) (i : ℕ) :
    d (i+2) - e (i+2) = d i - e i := by
  have h0 := h i
  have h1 := h (i+1)
  rw [show i+1+1 = i+2 by omega] at h1
  linarith

theorem even_step_difference {d e : ℕ → ℝ}
    (h : ∀ i, d i+d (i+1) = e i+e (i+1)) (i k : ℕ) :
    d (i+2*k)-e (i+2*k) = d i-e i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show i+2*(k+1) = (i+2*k)+2 by omega, two_step_difference h, ih]

theorem odd_period_identifies {d e : ℕ → ℝ} (n : ℕ)
    (h : ∀ i, d i+d (i+1) = e i+e (i+1))
    (pd : d (2*n+1) = d 0) (pe : e (2*n+1) = e 0) : ∀ i, d i=e i := by
  have hd := even_step_difference h 1 n
  rw [show 1+2*n = 2*n+1 by omega, pd, pe] at hd
  have h0 := h 0
  simp only [Nat.zero_add] at h0
  have heq : d 0=e 0 := by linarith
  intro i
  by_contra hi
  exact compatible_gap_differs_everywhere h ⟨i,hi⟩ 0 heq

theorem pair_sum_arc (d : ℕ → ℝ) (i n : ℕ) :
    (∑ j ∈ Finset.range n, (d (i+2*j)+d (i+2*j+1))) = arc d i (2*n) := by
  induction n with
  | zero => simp [arc]
  | succ n ih =>
    change (∑ j ∈ Finset.range (n+1), (d (i+2*j)+d (i+2*j+1))) = arc d i (2*(n+1))
    rw [Finset.sum_range_succ, ih, show 2*(n+1) = 2*n+1+1 by omega]
    unfold arc
    simp only [Finset.sum_range_succ]
    rw [show i+(2*n+1) = i+2*n+1 by omega]
    ring

theorem arc_shift (d : ℕ → ℝ) (n : ℕ) :
    arc d 0 n + d n = d 0 + arc d 1 n := by
  induction n with
  | zero => simp [arc]
  | succ n ih =>
    change arc d 0 (n+1)+d (n+1) = d 0+arc d 1 (n+1)
    unfold arc at *
    simp only [Nat.zero_add] at ih
    simp only [Finset.sum_range_succ, Nat.zero_add]
    rw [show 1+n = n+1 by omega]
    linarith only [ih]

theorem cycle_parity_sums (d : ℕ → ℝ) (n : ℕ)
    (total : arc d 0 (2*n)=1) (period : d (2*n)=d 0) :
    (∑ j ∈ Finset.range n, (d (2*j)+d (2*j+1)))=1 ∧
    (∑ j ∈ Finset.range n, (d (1+2*j)+d (1+2*j+1)))=1 := by
  have he := (pair_sum_arc d 0 n).trans total
  have ho := pair_sum_arc d 1 n
  have hh := arc_shift d (2*n)
  rw [period,total] at hh
  have he' : arc d 1 (2*n)=1 := by linarith
  exact ⟨by simpa only [Nat.zero_add] using he, ho.trans he'⟩

theorem lower_sum_eq_all (f : ℕ → ℝ) (a : ℝ) (n : ℕ)
    (low : ∀ i < n, a ≤ f i)
    (total : (∑ i ∈ Finset.range n, f i)=(n : ℝ)*a) :
    ∀ i < n, f i=a := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    have hlo : ∀ i < n, a ≤ f i := fun i hi => low i (by omega)
    have hb := parity_sum_bound f a n hlo
    rw [Finset.sum_range_succ,Nat.cast_succ] at total
    have hn := low n (by omega)
    have heq : f n=a := by linarith
    have hsub : (∑ j ∈ Finset.range n, f j)=(n : ℝ)*a := by linarith
    intro i hi
    by_cases he : i=n
    · subst i
      exact heq
    · exact ih hlo hsub i (by omega)

theorem zero_window_uniform (he ho : ℕ → ℝ) (n : ℕ) (H E O : ℝ)
    (se : (∑ i ∈ Finset.range n, he i)=1)
    (so : (∑ i ∈ Finset.range n, ho i)=1)
    (lowE : ∀ i<n, H≤he i) (lowO : ∀ i<n, H≤ho i)
    (upE : ∀ i<n, he i≤E) (upO : ∀ i<n, ho i≤O)
    (collapse : min E O=H) :
    (∀ i<n, he i=H) ∧ (∀ i<n, ho i=H) := by
  have hb := window_order he ho n H E O se so lowE lowO upE upO
  rw [collapse] at hb
  have hh : (n : ℝ)*H=1 := le_antisymm hb.1 hb.2
  exact ⟨lower_sum_eq_all he H n lowE (se.trans hh.symm),
    lower_sum_eq_all ho H n lowO (so.trans hh.symm)⟩

-- Exact observable data on a single parity: an arc with an even number of
-- elementary gaps, a sum of two such arcs, or a singleton/empty constant.
inductive ParityMeasure where
  | fixed (c : ℝ)
  | single (i k : ℕ)
  | double (i k j l : ℕ)

def evalParity (d : ℕ → ℝ) : ParityMeasure → ℝ
  | .fixed c => c
  | .single i k => arc d i (2*k)
  | .double i k j l => arc d i (2*k)+arc d j (2*l)

theorem parity_measure_invariant (d e : ℕ → ℝ)
    (h : ∀ i, d i+d (i+1)=e i+e (i+1)) (x : ParityMeasure) :
    evalParity d x=evalParity e x := by
  cases x with
  | fixed c => rfl
  | single i k => exact even_arc_invariant d e h i k
  | double i k j l =>
    simp only [evalParity, even_arc_invariant d e h]

section Family
variable {I W : Type*} [DecidableEq I]

theorem family_parity_data_invariant (q : W → Finset I → I → ℝ)
    (d : W → ℕ → ℝ) (w0 : W) (P : Finset I)
    (expr : Finset I → I → ParityMeasure)
    (compatible : ∀ w i, d w i+d w (i+1)=d w0 i+d w0 (i+1))
    (data : ∀ w S, S ⊆ P → ∀ i, q w (insert i S) i = evalParity (d w) (expr S i)) :
    ∀ w S, S ⊆ P → ∀ i, q w (insert i S) i=q w0 (insert i S) i := by
  intro w S hS i
  rw [data w S hS i,data w0 S hS i]
  exact parity_measure_invariant (d w) (d w0) (compatible w) (expr S i)

theorem family_common_below (q : W → Finset I → I → ℝ) (w0 : W)
    (θ : ℝ) (P : Finset I) (law : MergeLaw (q w0))
    (hn : NoEntry (q w0) θ P)
    (inv : ∀ w S, S ⊆ P → ∀ i, q w (insert i S) i=q w0 (insert i S) i) :
    ∃ S : Finset I, S ⊆ P ∧ ∀ w, Equilibrium (q w) θ S ∧ ∀ i∈S, q w S i=q w0 S i := by
  obtain ⟨S,hsub,he⟩ := exists_equilibrium_below law P hn
  refine ⟨S,hsub,?_⟩
  intro w
  have obs : ∀ i∈S, q w S i=q w0 S i := by
    intro i hi
    simpa [Finset.insert_eq_of_mem hi] using inv w S hsub i
  refine ⟨?_, obs⟩
  constructor
  · intro i hi
    rw [inv w S hsub i]
    exact he.1 i hi
  · intro i hi
    rw [obs i hi]
    exact he.2 i hi

-- The analytic gap model supplies P (the retained parity), its no-entry
-- constraint at T, and the parity-expression data for its subsets.
theorem outside_window_family [Fintype I] (q : W → Finset I → I → ℝ)
    (w0 : W) (H T θ : ℝ) (P : Finset I)
    (law : MergeLaw (q w0))
    (fullLower : ∀ i, H≤q w0 Finset.univ i)
    (fullObs : ∀ w i, q w Finset.univ i=q w0 Finset.univ i)
    (parityNoEntry : NoEntry (q w0) T P)
    (inv : ∀ w S, S⊆P → ∀ i, q w (insert i S) i=q w0 (insert i S) i)
    (outside : θ≤H ∨ T≤θ) :
    ∃ S : Finset I, ∀ w, Equilibrium (q w) θ S ∧ ∀ i∈S, q w S i=q w0 S i := by
  rcases outside with lo | hi
  · refine ⟨Finset.univ,?_⟩
    intro w
    refine ⟨?_,fun i _ => fullObs w i⟩
    constructor
    · intro i hn
      exact False.elim (hn (Finset.mem_univ i))
    · intro i _
      rw [fullObs w i]
      exact le_trans lo (fullLower i)
  · have hn : NoEntry (q w0) θ P := by
      intro i hni
      exact le_trans (parityNoEntry i hni) hi
    obtain ⟨S,_,hS⟩ := family_common_below q w0 θ P law hn inv
    exact ⟨S,hS⟩
end Family

theorem shared_observer_exists {W α σ : Type*}
    (feasible : W → α → σ → Prop)
    (common : ∀ x, ∃ s, ∀ w, feasible w x s) :
    ∃ observe : α → σ, ∀ w x, feasible w x (observe x) := by
  classical
  exact ⟨fun x => Classical.choose (common x),
    fun w x => Classical.choose_spec (common x) w⟩

-- Connect the local economic best-response bounds to the identifying pattern.
theorem interior_window_certificate (active : ℕ → Bool)
    (d e h q r entry g : ℕ → ℝ) (H T θ K : ℝ)
    (compatible : ∀ i, d i+d (i+1)=e i+e (i+1))
    (different : ∃ i, d i≠e i)
    (hmin : ∃ i, h i=H)
    (evenmax : ∃ k, T≤h (2*k)) (oddmax : ∃ k, T≤h (2*k+1))
    (lo : H<θ) (hi : θ<T) (kbound : T≤K)
    (full : (∀ i, active i=true) → ∀ i, q i=h i)
    (stay : ∀ i, active i=true → θ≤q i)
    (idle : ∀ i, active i=false → entry i≤θ)
    (lower : ∀ i, active i=false → h i≤entry i)
    (gmin : ∀ i, K≤g i)
    (adjacent : ∀ i, active i=false → active (i+1)=false → g i≤entry i)
    (left : ∀ i, active i=false → active (i+1)=true → active (i+2)=true →
      q (i+1)=d i+d (i+1)+d (i+2) ∧ r (i+1)=e i+e (i+1)+e (i+2))
    (right : ∀ i, active i=true → active (i+1)=true → active (i+2)=false →
      q (i+1)=d (i+1)+d (i+2)+d (i+3) ∧ r (i+1)=e (i+1)+e (i+2)+e (i+3)) :
    ∃ i, active i=true ∧ q i≠r i := by
  have omit : ∃ i, active i=false := by
    by_contra hn
    have all : ∀ i, active i=true := by
      intro i
      cases he : active i with
      | false => exact False.elim (hn ⟨i,he⟩)
      | true => rfl
    obtain ⟨i,he⟩ := hmin
    have hs := stay i (all i)
    have hf := full all i
    linarith
  have iso := isolated_from_triple_bound active g θ T K hi kbound gmin
    (fun i ha hb => le_trans (adjacent i ha hb) (idle i ha))
  have hn : ∀ i, active i=false → h i≤θ :=
    fun i ha => le_trans (lower i ha) (idle i ha)
  exact interior_signal_separation active d e h q r θ T compatible different omit iso hn evenmax oddmax hi left right

theorem pow_two_lower (n : ℕ) : (n : ℝ)+1≤(2 : ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.cast_succ,pow_succ]
    have hn : 0≤(n : ℝ) := Nat.cast_nonneg n
    linarith

theorem finite_dyadic_probe (ε : ℝ) (he : 0<ε) :
    ∃ n : ℕ, 0<(1/2 : ℝ)^n ∧ (1/2 : ℝ)^n<ε := by
  obtain ⟨n,hn⟩ := exists_nat_gt (1/ε)
  have hPow := pow_two_lower n
  have hPos : 0<(2 : ℝ)^n := pow_pos (by norm_num) n
  have hlt : 1/ε<(2 : ℝ)^n := by linarith
  have hmul := (div_lt_iff₀ he).mp hlt
  have hdiv : (1 : ℝ)/(2 : ℝ)^n<ε :=
    (div_lt_iff₀ hPos).2 (by nlinarith only [hmul])
  refine ⟨n,pow_pos (by norm_num) n,?_⟩
  simpa only [div_pow,one_pow] using hdiv

theorem perturbed_share_bounds (h u v η : ℝ) (hu : |u|<η) (hv : |v|<η) :
    h-2*η<h+u+v ∧ h+u+v<h+2*η := by
  have hu' := abs_lt.mp hu
  have hv' := abs_lt.mp hv
  constructor <;> linarith [hu'.1,hu'.2,hv'.1,hv'.2]

-- The two type-specific optima are compared on exactly the same policy set.
def WorstCost {X : Type*} (E : ℝ → X → Prop) (C : X → ℝ) (x w : ℝ) : Prop :=
  (∃ S, E x S ∧ C S=w) ∧ ∀ S, E x S → C S≤w

def MenuOpt (A : Set ℝ) (w : ℝ → ℝ) (v : ℝ) : Prop :=
  (∃ x∈A, w x=v) ∧ ∀ x∈A, v≤w x

theorem robust_welfare_from_profiles {X : Type*} (A : Set ℝ)
    (EU EC : ℝ → X → Prop) (CU CC : X → ℝ) (sU sC : X)
    (rU rC : ℝ → ℝ) (uStar cStar L R gamma delta : ℝ)
    (zeroMenu : 0∈A) (rightMenu : R∈A)
    (wu : ∀ x∈A, WorstCost EU CU x (rU x))
    (wc : ∀ x∈A, WorstCost EC CC x (rC x))
    (ou : MenuOpt A rU uStar) (oc : MenuOpt A rC cStar)
    (uMin : ∀ S, CU sU≤CU S)
    (uInit : ∀ S, EU 0 S → CU S=CU sU)
    (uHigh : ∀ x∈A, R≤x → ∀ S, EU x S → CU sU+gamma≤CU S)
    (cLow : ∀ x∈A, x≤L → EC x sC)
    (cAtR : ∀ S, EC R S → CC S≤CC sC-delta) :
    uStar=CU sU ∧ cStar≤CC sC-delta ∧
    (∀ x∈A, R≤x → gamma≤rU x-uStar) ∧
    (∀ x∈A, x≤L → delta≤rC x-cStar) := by
  have uBound : ∀ x∈A, CU sU≤rU x := by
    intro x hx
    obtain ⟨S,_,he⟩ := (wu x hx).1
    rw [← he]
    exact uMin S
  have u0 : rU 0=CU sU := by
    obtain ⟨S,hs,he⟩ := (wu 0 zeroMenu).1
    exact he.symm.trans (uInit S hs)
  have uEq : uStar=CU sU := by
    obtain ⟨x,hx,he⟩ := ou.1
    have h1 := uBound x hx
    have h2 := ou.2 0 zeroMenu
    linarith
  have cR : rC R≤CC sC-delta := by
    obtain ⟨S,hs,he⟩ := (wc R rightMenu).1
    rw [← he]
    exact cAtR S hs
  have cBound := le_trans (oc.2 R rightMenu) cR
  refine ⟨uEq,cBound,?_,?_⟩
  · intro x hx hi
    obtain ⟨S,hs,he⟩ := (wu x hx).1
    have hm := uHigh x hx hi S hs
    linarith
  · intro x hx lo
    have hc := (wc x hx).2 sC (cLow x hx lo)
    linarith

#print axioms two_step_difference
#print axioms even_step_difference
#print axioms odd_period_identifies
#print axioms pair_sum_arc
#print axioms arc_shift
#print axioms cycle_parity_sums
#print axioms lower_sum_eq_all
#print axioms zero_window_uniform
#print axioms parity_measure_invariant
#print axioms family_parity_data_invariant
#print axioms family_common_below
#print axioms outside_window_family
#print axioms shared_observer_exists
#print axioms interior_window_certificate
#print axioms pow_two_lower
#print axioms finite_dyadic_probe
#print axioms perturbed_share_bounds
#print axioms robust_welfare_from_profiles
end RC01

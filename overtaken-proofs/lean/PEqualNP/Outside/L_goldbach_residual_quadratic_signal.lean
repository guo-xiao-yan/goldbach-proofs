import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

private lemma reindex_pairs (x q c : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ s ∈ (Finset.range (2*x+1)).filter (fun s => s % q = c),
      ∑ k ∈ (Finset.range (x+1)).filter (fun k => k ≤ s ∧ s-k ≤ x), f k (s-k)
      = ∑ k ∈ Finset.range (x+1), ∑ l ∈ Finset.range (x+1),
          if (k + l) % q = c then f k l else 0 := by
  simp only [Finset.sum_filter]
  have hh : ∀ s : ℕ, (if s % q = c then ∑ k ∈ Finset.range (x+1),
      (if k ≤ s ∧ s - k ≤ x then f k (s-k) else 0) else 0)
      = ∑ k ∈ Finset.range (x+1),
      (if k ≤ s ∧ s - k ≤ x then (if s % q = c then f k (s-k) else 0) else 0) := by
    intro s
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl (fun s _ => hh s), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [← Finset.sum_filter]
  have hset : (Finset.range (2*x+1)).filter (fun s => k ≤ s ∧ s - k ≤ x)
      = (Finset.range (x+1)).image (fun l => k + l) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨_, h1, h2⟩
      exact ⟨s - k, by omega, by omega⟩
    · rintro ⟨l, hl, rfl⟩
      omega
  rw [hset, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro l _
    simp
  · intro a _ b _ h
    simpa using h

private lemma fiber_zero (x q c : ℕ) (hq : 0 < q) (u v : ℕ → ℝ)
    (hu : ∀ r < q, ∑ i ∈ (Finset.range (x+1)).filter (fun k => k % q = r), u i = 0) :
    ∑ k ∈ Finset.range (x+1), ∑ l ∈ Finset.range (x+1),
      (if (k + l) % q = c then u k * v l else 0) = 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro l _
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.range (x+1)) (t := Finset.range q)
    (g := fun k => k % q)]
  · apply Finset.sum_eq_zero
    intro r hr
    rw [Finset.mem_range] at hr
    have : ∀ k ∈ (Finset.range (x+1)).filter (fun k => k % q = r),
        (if (k + l) % q = c then u k * v l else 0)
          = if (r + l) % q = c then u k * v l else 0 := by
      intro k hk
      rw [Finset.mem_filter] at hk
      have e : (k + l) % q = (r + l) % q := by
        rw [Nat.add_mod k, hk.2, Nat.add_mod r l, Nat.mod_eq_of_lt hr]
      rw [e]
    rw [Finset.sum_congr rfl this]
    by_cases h : (r + l) % q = c
    · simp only [h, ite_true]
      rw [← Finset.sum_mul, hu r hr, zero_mul]
    · simp [h]
  · intro k _
    simp only [Finset.mem_range]
    exact Nat.mod_lt _ hq


private lemma fiber_zero_r (x q c : ℕ) (hq : 0 < q) (u v : ℕ → ℝ)
    (hv : ∀ r < q, ∑ i ∈ (Finset.range (x+1)).filter (fun k => k % q = r), v i = 0) :
    ∑ k ∈ Finset.range (x+1), ∑ l ∈ Finset.range (x+1),
      (if (k + l) % q = c then u k * v l else 0) = 0 := by
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_).trans
    (fiber_zero x q c hq v u hv)
  rw [Nat.add_comm k l, mul_comm]

private lemma mod_two (q n : ℕ) (hq : 0 < q) (h : n < 2 * q) :
    n % q = if n < q then n else n - q := by
  split_ifs with h1
  · exact Nat.mod_eq_of_lt h1
  · rw [Nat.mod_eq_sub_mod (by omega)]
    exact Nat.mod_eq_of_lt (by omega)

private lemma mod_equiv (q c r l : ℕ) (hq : 0 < q) (hc : c < q) (hr : r < q) :
    (r + l) % q = c ↔ l % q = (c % q + q - r) % q := by
  have hu : l % q < q := Nat.mod_lt _ hq
  have e1 : (r + l) % q = (r + l % q) % q := by
    rw [Nat.add_mod r l, Nat.mod_eq_of_lt hr]
  rw [e1, Nat.mod_eq_of_lt hc]
  generalize l % q = u at hu ⊢
  have h1 := mod_two q (r + u) hq (by omega)
  have h2 := mod_two q (c + q - r) hq (by omega)
  rw [h1, h2]
  split_ifs <;> omega

private lemma pair_sum (x q c : ℕ) (hq : 0 < q) (hc : c < q) (A B : ℕ → ℝ) :
    ∑ k ∈ Finset.range (x+1), ∑ l ∈ Finset.range (x+1),
      (if (k + l) % q = c then A k * B l else 0)
    = ∑ r ∈ Finset.range q,
      (∑ i ∈ (Finset.range (x+1)).filter (fun k => k % q = r), A i) *
      (∑ j ∈ (Finset.range (x+1)).filter (fun k => k % q = (c % q + q - r) % q), B j) := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.range (x+1)) (t := Finset.range q)
    (g := fun k => k % q)]
  · apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mem_range] at hr
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_filter] at hk
    have key : ∀ l, (k + l) % q = c ↔ l % q = (c % q + q - r) % q := by
      intro l
      have e : (k + l) % q = (r + l) % q := by
        rw [Nat.add_mod k l, hk.2, Nat.add_mod r l, Nat.mod_eq_of_lt hr]
      rw [e]
      exact mod_equiv q c r l hq hc hr
    simp only [key]
    rw [← Finset.sum_filter, Finset.mul_sum]
  · intro k _
    simp only [Finset.mem_range]
    exact Nat.mod_lt _ hq


theorem PEqualNP.Outside.L_goldbach_residual_quadratic_signal :
    let F := fun x q r : ℕ => (Finset.range (x+1)).filter (fun k => k % q=r); let e := fun (x q : ℕ) (a : ℕ → ℝ) k => let f := F x q (k % q); a k-(∑ i ∈ f, a i)/(f.card:ℝ); let C := fun (x : ℕ) (a b : ℕ → ℝ) s => ∑ k ∈ (Finset.range (x+1)).filter (fun k => k ≤ s ∧ s-k ≤ x), a k*b (s-k); ∀ (x q c : ℕ) (a b : ℕ → ℝ), c<q → (∑ s ∈ (Finset.range (2*x+1)).filter (fun s => s % q=c), (s:ℝ)^2*C x (e x q a) (e x q b) s) = 2*∑ r ∈ Finset.range q, ((∑ i ∈ F x q r, (i:ℝ)*e x q a i)*(∑ j ∈ F x q ((c % q+q-r) % q), (j:ℝ)*e x q b j)) := by
  intro F e C x q c a b hc
  have hq : 0 < q := by omega
  have hz : ∀ (g : ℕ → ℝ), ∀ r < q,
      (∑ i ∈ (Finset.range (x+1)).filter (fun k => k % q = r), e x q g i) = 0 := by
    intro g r hr
    have hc : ∀ i ∈ F x q r, e x q g i = g i - (∑ i ∈ F x q r, g i) / ((F x q r).card : ℝ) := by
      intro i hi
      have hi' : i % q = r := (Finset.mem_filter.mp hi).2
      simp only [e, hi']
    show ∑ i ∈ F x q r, e x q g i = 0
    rw [Finset.sum_congr rfl hc, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    by_cases h0 : ((F x q r).card : ℝ) = 0
    · have : F x q r = ∅ := Finset.card_eq_zero.mp (by exact_mod_cast h0)
      rw [this]; simp
    · rw [mul_div_cancel₀ _ h0, sub_self]
  have step : ∑ s ∈ (Finset.range (2*x+1)).filter (fun s => s % q = c), (s:ℝ)^2 * C x (e x q a) (e x q b) s
      = ∑ s ∈ (Finset.range (2*x+1)).filter (fun s => s % q = c),
        ∑ k ∈ (Finset.range (x+1)).filter (fun k => k ≤ s ∧ s-k ≤ x),
          ((k + (s - k) : ℕ) : ℝ)^2 * (e x q a k * e x q b (s-k)) := by
    apply Finset.sum_congr rfl
    intro s _
    simp only [C]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_filter] at hk
    rw [Nat.add_sub_cancel' hk.2.1]
  rw [step, reindex_pairs x q c (fun k l => ((k + l : ℕ) : ℝ)^2 * (e x q a k * e x q b l))]
  have h2 : ∀ k l : ℕ,
      (if (k + l) % q = c then ((k + l : ℕ) : ℝ)^2 * (e x q a k * e x q b l) else 0)
      = (if (k + l) % q = c then (((k:ℝ)^2 * e x q a k) * e x q b l) else 0)
        + 2 * (if (k + l) % q = c then (((k:ℝ) * e x q a k) * ((l:ℝ) * e x q b l)) else 0)
        + (if (k + l) % q = c then (e x q a k * ((l:ℝ)^2 * e x q b l)) else 0) := by
    intro k l
    split_ifs
    · push_cast; ring
    · simp
  simp only [h2, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [fiber_zero_r x q c hq (fun k => (k:ℝ)^2 * e x q a k) (e x q b) (hz b),
    fiber_zero x q c hq (e x q a) (fun l => (l:ℝ)^2 * e x q b l) (hz a),
    pair_sum x q c hq hc (fun k => (k:ℝ) * e x q a k) (fun l => (l:ℝ) * e x q b l)]
  simp only [zero_add, add_zero]
  rfl

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Sum
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

private theorem poly_order :
    let F := fun x q r : ℕ => (Finset.range (x+1)).filter (fun k => k % q=r); let C := fun (x : ℕ) (a b : ℕ → ℝ) s => ∑ k ∈ (Finset.range (x+1)).filter (fun k => k ≤ s ∧ s-k ≤ x), a k*b (s-k); ∀ (x q c m l d : ℕ) (a b : ℕ → ℝ), 0<q → d < m + l → (∀ r<q, ∀ j < m, (∑ i ∈ F x q r, (i:ℝ)^j*a i)=0) → (∀ r<q, ∀ j < l, (∑ i ∈ F x q r, (i:ℝ)^j*b i)=0) → (∑ s ∈ (Finset.range (2*x+1)).filter (fun s => s % q=c), (s:ℝ)^d*C x a b s)=0 := by
  intro F C x q c m l d a b hq hd ha hb
  simp only [F] at ha hb
  have step : ∑ s ∈ (Finset.range (2*x+1)).filter (fun s => s % q = c), (s:ℝ)^d * C x a b s
      = ∑ s ∈ (Finset.range (2*x+1)).filter (fun s => s % q = c),
        ∑ k ∈ (Finset.range (x+1)).filter (fun k => k ≤ s ∧ s-k ≤ x),
          ((k + (s - k) : ℕ) : ℝ)^d * (a k * b (s-k)) := by
    apply Finset.sum_congr rfl
    intro s _
    simp only [C]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_filter] at hk
    rw [Nat.add_sub_cancel' hk.2.1]
  rw [step, reindex_pairs x q c (fun k l => ((k + l : ℕ) : ℝ)^d * (a k * b l))]
  have expand : ∀ k l : ℕ, ((k + l : ℕ) : ℝ)^d * (a k * b l)
      = ∑ i ∈ Finset.range (d+1), (d.choose i : ℝ) *
          (((k:ℝ)^i * a k) * ((l:ℝ)^(d-i) * b l)) := by
    intro k l
    rw [Nat.cast_add, add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h2 : ∀ k ∈ Finset.range (x+1), ∀ l ∈ Finset.range (x+1),
      (if (k + l) % q = c then ((k + l : ℕ) : ℝ)^d * (a k * b l) else 0)
      = ∑ i ∈ Finset.range (d+1), (d.choose i : ℝ) *
          (if (k + l) % q = c then (((k:ℝ)^i * a k) * ((l:ℝ)^(d-i) * b l)) else 0) := by
    intro k _ l _
    split_ifs
    · exact expand k l
    · simp
  rw [Finset.sum_congr rfl (fun k hk => Finset.sum_congr rfl (fun l hl => h2 k hk l hl))]
  have h4 : ∀ i ∈ Finset.range (d+1),
      ∑ k ∈ Finset.range (x+1), ∑ l ∈ Finset.range (x+1), (d.choose i : ℝ) *
          (if (k + l) % q = c then (((k:ℝ)^i * a k) * ((l:ℝ)^(d-i) * b l)) else 0) = 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    simp only [← Finset.mul_sum]
    by_cases him : i < m
    · rw [fiber_zero x q c hq (fun k => (k:ℝ)^i * a k) (fun l => (l:ℝ)^(d-i) * b l)
        (fun r hr => ha r hr i him), mul_zero]
    · have hjl : d - i < l := by omega
      rw [Finset.sum_comm]
      have : ∀ l ∈ Finset.range (x+1), ∑ k ∈ Finset.range (x+1),
          (if (k + l) % q = c then (((k:ℝ)^i * a k) * ((l:ℝ)^(d-i) * b l)) else 0)
          = ∑ k ∈ Finset.range (x+1),
          (if (l + k) % q = c then (((l:ℝ)^(d-i) * b l) * ((k:ℝ)^i * a k)) else 0) := by
        intro l _
        apply Finset.sum_congr rfl
        intro k _
        rw [Nat.add_comm k l, mul_comm]
      rw [Finset.sum_congr rfl this]
      rw [fiber_zero x q c hq (fun l => (l:ℝ)^(d-i) * b l) (fun k => (k:ℝ)^i * a k)
        (fun r hr => hb r hr (d-i) hjl), mul_zero]
  calc _ = ∑ k ∈ Finset.range (x+1), ∑ i ∈ Finset.range (d+1), ∑ l ∈ Finset.range (x+1),
        (d.choose i : ℝ) *
          (if (k + l) % q = c then (((k:ℝ)^i * a k) * ((l:ℝ)^(d-i) * b l)) else 0) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_comm]
    _ = ∑ i ∈ Finset.range (d+1), ∑ k ∈ Finset.range (x+1), ∑ l ∈ Finset.range (x+1),
        (d.choose i : ℝ) *
          (if (k + l) % q = c then (((k:ℝ)^i * a k) * ((l:ℝ)^(d-i) * b l)) else 0) :=
        Finset.sum_comm
    _ = 0 := Finset.sum_eq_zero h4

theorem PEqualNP.Outside.L_goldbach_residual_class_affine :
    let F := fun x q r : ℕ => (Finset.range (x+1)).filter (fun k => k % q=r); let e := fun (x q : ℕ) (a : ℕ → ℝ) k => let f := F x q (k % q); a k-(∑ i ∈ f, a i)/(f.card:ℝ); let C := fun (x : ℕ) (a b : ℕ → ℝ) s => ∑ k ∈ (Finset.range (x+1)).filter (fun k => k ≤ s ∧ s-k ≤ x), a k*b (s-k); ∀ (x q c : ℕ) (a b : ℕ → ℝ) (u v : ℝ), 0<q → (∑ s ∈ (Finset.range (2*x+1)).filter (fun s => s % q=c), (u+v*(s:ℝ))*C x (e x q a) (e x q b) s)=0 := by
  intro F e C x q c a b u v hq
  have hz : ∀ (g : ℕ → ℝ), ∀ r < q, ∀ j < 1,
      (∑ i ∈ F x q r, (i:ℝ)^j * e x q g i) = 0 := by
    intro g r hr j hj
    have hj0 : j = 0 := by omega
    subst hj0
    simp only [pow_zero, one_mul]
    have hc : ∀ i ∈ F x q r, e x q g i = g i - (∑ i ∈ F x q r, g i) / ((F x q r).card : ℝ) := by
      intro i hi
      have hi' : i % q = r := (Finset.mem_filter.mp hi).2
      simp only [e, hi']
    rw [Finset.sum_congr rfl hc, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    by_cases h0 : ((F x q r).card : ℝ) = 0
    · have : F x q r = ∅ := Finset.card_eq_zero.mp (by exact_mod_cast h0)
      rw [this]; simp
    · rw [mul_div_cancel₀ _ h0, sub_self]
  have h0 := poly_order x q c 1 1 0 (e x q a) (e x q b) hq (by omega) (hz a) (hz b)
  have h1 := poly_order x q c 1 1 1 (e x q a) (e x q b) hq (by omega) (hz a) (hz b)
  have h0' : ∑ s ∈ (Finset.range (2*x+1)).filter (fun s => s % q = c),
      C x (e x q a) (e x q b) s = 0 := by
    simp only [pow_zero, one_mul] at h0
    exact h0
  have h1' : ∑ s ∈ (Finset.range (2*x+1)).filter (fun s => s % q = c),
      (s:ℝ) * C x (e x q a) (e x q b) s = 0 := by
    simp only [pow_one] at h1
    exact h1
  have : ∀ s : ℕ, (u + v * (s:ℝ)) * C x (e x q a) (e x q b) s
      = u * C x (e x q a) (e x q b) s + v * ((s:ℝ) * C x (e x q a) (e x q b) s) := by
    intro s; ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, h0', h1', mul_zero, add_zero]

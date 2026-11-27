import Mathlib

private lemma rg_greedy {m : ℕ} (p : ℕ → Fin m → ℝ) (n : ℕ) :
    ∃ ε : ℕ → ℝ, (∀ k, ε k = 1 ∨ ε k = -1) ∧
      ∑ j, (∑ k ∈ Finset.range n, ε k * p k j) ^ 2 ≤ ∑ j, ∑ k ∈ Finset.range n, (p k j) ^ 2 := by
  induction n with
  | zero => exact ⟨fun _ => 1, fun _ => Or.inl rfl, by simp⟩
  | succ n ih =>
    obtain ⟨ε, hε, hle⟩ := ih
    set S : Fin m → ℝ := fun j => ∑ k ∈ Finset.range n, ε k * p k j with hS
    set s : ℝ := if ∑ j, S j * p n j ≤ 0 then 1 else -1 with hs
    have hs1 : s = 1 ∨ s = -1 := by simp only [hs]; split_ifs <;> simp
    have hs2 : s * ∑ j, S j * p n j ≤ 0 := by
      simp only [hs]; split_ifs with h
      · simpa using h
      · push_neg at h; linarith
    refine ⟨fun k => if k = n then s else ε k, ?_, ?_⟩
    · intro k; by_cases h : k = n
      · simp only [h, if_true]; exact hs1
      · simp only [h, if_false]; exact hε k
    · have hsum : ∀ j, ∑ k ∈ Finset.range (n+1), (if k = n then s else ε k) * p k j = S j + s * p n j := by
        intro j
        rw [Finset.sum_range_succ]
        simp only [if_true, hS]
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        have : k ≠ n := by simp at hk; omega
        simp [this]
      simp only [hsum, Finset.sum_range_succ, Finset.sum_add_distrib]
      have e : ∀ j, (S j + s * p n j) ^ 2 = S j ^ 2 + 2 * (s * (S j * p n j)) + s ^ 2 * p n j ^ 2 := by
        intro j; ring
      simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
      have hs3 : s ^ 2 = 1 := by rcases hs1 with h | h <;> simp [h]
      rw [hs3]
      have : ∑ j, S j ^ 2 ≤ ∑ j, ∑ k ∈ Finset.range n, p k j ^ 2 := hle
      nlinarith

private lemma rg_split (n : ℕ) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.range (2 * n + 1), f k = ∑ k ∈ Finset.range n, (f k + f (2 * n - k)) + f n := by
  have h1 : ∑ k ∈ Finset.range (2 * n + 1), f k = ∑ k ∈ Finset.range n, f k + ∑ k ∈ Finset.Ico n (2 * n + 1), f k := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico, Finset.sum_Ico_consecutive _ (Nat.zero_le n) (by omega)]
  have h2 : ∑ k ∈ Finset.Ico n (2 * n + 1), f k = f n + ∑ k ∈ Finset.Ico (n + 1) (2 * n + 1), f k := by
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  have h3 : ∑ k ∈ Finset.Ico (n + 1) (2 * n + 1), f k = ∑ k ∈ Finset.range n, f (2 * n - k) := by
    symm
    apply Finset.sum_nbij' (fun k => 2 * n - k) (fun k => 2 * n - k)
    · intro k hk; simp at hk ⊢; omega
    · intro k hk; simp at hk ⊢; omega
    · intro k hk; simp at hk; omega
    · intro k hk; simp at hk; omega
    · intro k hk; rfl
  rw [h1, h2, h3, Finset.sum_add_distrib]; ring

theorem Conjectures.Goldbach.ReflectionGridThinning :
    ∀ (n m : ℕ) (w : ℕ → ℝ) (a : ℕ → Fin m → ℝ), (∀ k, 0 ≤ w k) → ∃ v : ℕ → ℝ, (∀ k, 0 ≤ v k ∧ v k ≤ 2*w k) ∧ (∀ k ≤ 2*n, v k * v (2*n-k) = 0) ∧ v n = 0 ∧ (∑ j, ((∑ k ∈ Finset.range (2*n+1), (v k-w k)*a k j) + w n*a n j)^2) ≤ ∑ j, ∑ k ∈ Finset.range n, (w k*a k j-w (2*n-k)*a (2*n-k) j)^2 := by
  intro n m w a hw
  obtain ⟨ε, hε, hle⟩ := rg_greedy (fun k j => w k * a k j - w (2 * n - k) * a (2 * n - k) j) n
  set v : ℕ → ℝ := fun k => if k < n then (if ε k = 1 then 2 * w k else 0) else if k = n then 0 else if k ≤ 2 * n then (if ε (2 * n - k) = 1 then 0 else 2 * w k) else 0 with hv
  have hv0 : v n = 0 := by simp [hv]
  have hvk : ∀ k, k < n → v k = if ε k = 1 then 2 * w k else 0 := by
    intro k hk; simp [hv, hk]
  have hvk' : ∀ k, k < n → v (2 * n - k) = if ε k = 1 then 0 else 2 * w (2 * n - k) := by
    intro k hk
    have h2 : ¬ (2 * n - k < n) := by omega
    have h3 : 2 * n - k ≠ n := by omega
    have h4 : 2 * n - k ≤ 2 * n := by omega
    have h5 : 2 * n - (2 * n - k) = k := by omega
    simp [hv, h2, h3, h4, h5]
  refine ⟨v, ?_, ?_, hv0, ?_⟩
  · intro k
    have := hw k
    simp only [hv]
    split_ifs <;> constructor <;> linarith
  · intro k hk
    by_cases h1 : k < n
    · rw [hvk k h1, hvk' k h1]
      split_ifs <;> simp
    · by_cases h2 : k = n
      · subst h2; simp [hv0]
      · have h3 : 2 * n - k < n := by omega
        have h5 : 2 * n - (2 * n - k) = k := by omega
        have := hvk' (2 * n - k) h3
        rw [h5] at this
        have h6 := hvk (2 * n - k) h3
        rw [this, h6]
        split_ifs <;> simp
  · refine le_trans (le_of_eq ?_) hle
    apply Finset.sum_congr rfl
    intro j _
    have pair : ∀ k ∈ Finset.range n, (v k - w k) * a k j + (v (2 * n - k) - w (2 * n - k)) * a (2 * n - k) j = ε k * (w k * a k j - w (2 * n - k) * a (2 * n - k) j) := by
      intro k hk
      have h1 : k < n := by simpa using hk
      rw [hvk k h1, hvk' k h1]
      rcases hε k with h | h
      · rw [if_pos h, if_pos h, h]; ring
      · have h' : ε k ≠ 1 := by rw [h]; norm_num
        rw [if_neg h', if_neg h', h]; ring
    rw [rg_split n (fun k => (v k - w k) * a k j), Finset.sum_congr rfl pair, hv0]
    ring

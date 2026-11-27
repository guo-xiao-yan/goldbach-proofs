import Mathlib

theorem Conjectures.JoshiAbc.RoundingRadical :
    let rad := fun (n : ℕ) => n.primeFactors.prod id; ∀ (a b : ℕ) (S : Finset ℕ) (u : ℕ → ℝ), 0<a → 0<b → S ⊆ (2*a*b*(a+b)).primeFactors → (∀ p ∈ S, 0≤u p ∧ u p≤1) → S.sum (fun p => u p*Real.log p) ≤ Real.log (rad (a*b*(a+b)))+Real.log 2 := by
  intro rad a b S u ha hb hS hu
  have hn : a*b*(a+b) ≠ 0 := by positivity
  have hsub : S ⊆ insert 2 (a*b*(a+b)).primeFactors := by
    intro p hp
    have h := hS hp
    have e : 2*a*b*(a+b) = 2*(a*b*(a+b)) := by ring
    rw [e, Nat.primeFactors_mul (by norm_num) hn, Nat.Prime.primeFactors Nat.prime_two] at h
    simpa using h
  have hpos : ∀ p ∈ (insert 2 (a*b*(a+b)).primeFactors), 0 ≤ Real.log p := by
    intro p hp
    apply Real.log_nonneg
    have : 0 < p := by
      rcases Finset.mem_insert.mp hp with h | h
      · omega
      · exact (Nat.prime_of_mem_primeFactors h).pos
    exact_mod_cast this
  have h1 : S.sum (fun p => u p * Real.log p) ≤ S.sum (fun p => Real.log p) := by
    apply Finset.sum_le_sum
    intro p hp
    have hl := hpos p (hsub hp)
    have := hu p hp
    nlinarith [this.1, this.2]
  have h2 : S.sum (fun p => Real.log p) ≤ (insert 2 (a*b*(a+b)).primeFactors).sum (fun p => Real.log p) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => hpos p hp)
  have h3 : (a*b*(a+b)).primeFactors.sum (fun p => Real.log p) = Real.log (rad (a*b*(a+b))) := by
    show _ = Real.log (((a*b*(a+b)).primeFactors.prod id : ℕ) : ℝ)
    rw [Nat.cast_prod, Real.log_prod]
    · rfl
    · intro p hp
      have := (Nat.prime_of_mem_primeFactors hp).pos
      simp
      omega
  have h4 : (insert 2 (a*b*(a+b)).primeFactors).sum (fun p => Real.log p) ≤ (a*b*(a+b)).primeFactors.sum (fun p => Real.log p) + Real.log 2 := by
    by_cases h : 2 ∈ (a*b*(a+b)).primeFactors
    · rw [Finset.insert_eq_of_mem h]
      have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      linarith
    · rw [Finset.sum_insert h, Nat.cast_ofNat]
      linarith
  linarith

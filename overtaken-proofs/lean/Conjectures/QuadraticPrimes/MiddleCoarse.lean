import Mathlib

private theorem qpmc_card (p x : ℕ) (hp : p.Prime) (hxp : x < p) :
    ((Finset.Ioc x (2 * x)).filter (fun n => p ∣ n ^ 2 + 1)).card ≤ 2 := by
  haveI := Fact.mk hp
  have hne : (Polynomial.X ^ 2 + 1 : Polynomial (ZMod p)) ≠ 0 := by
    intro h
    have := congrArg (Polynomial.eval 0) h
    simp at this
  have hdeg : (Polynomial.X ^ 2 + 1 : Polynomial (ZMod p)).natDegree ≤ 2 := by
    compute_degree
  have h1 : ((Polynomial.X ^ 2 + 1 : Polynomial (ZMod p)).roots.toFinset).card ≤ 2 :=
    (Multiset.toFinset_card_le _).trans
      ((Polynomial.card_roots' _).trans hdeg)
  refine le_trans ?_ h1
  apply Finset.card_le_card_of_injOn (fun n : ℕ => (n : ZMod p))
  · intro n hn
    simp only [Finset.coe_filter, Finset.mem_Ioc, Set.mem_setOf_eq] at hn
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_roots hne]
    have h2 := (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) p).2 hn.2
    simp at h2 ⊢
    exact h2
  · intro n hn m hm hnm
    simp only [Finset.coe_filter, Finset.mem_Ioc, Set.mem_setOf_eq] at hn hm
    have h3 := (ZMod.natCast_eq_natCast_iff n m p).1 hnm
    have h4 := (Nat.modEq_iff_dvd.1 h3)
    have h5 : ((m : ℤ) - n) = 0 :=
      Int.eq_zero_of_abs_lt_dvd h4 (abs_lt.2 ⟨by omega, by omega⟩)
    omega

private theorem qpmc_val (p x n : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (hxp : x < p)
    (hn : n ≤ 2 * x) : (n ^ 2 + 1).factorization p ≤ 2 := by
  by_contra h
  have h3 : 3 ≤ (n ^ 2 + 1).factorization p := by omega
  have hd : p ^ 3 ∣ n ^ 2 + 1 :=
    (hp.pow_dvd_iff_le_factorization (by positivity)).2 h3
  have hle := Nat.le_of_dvd (by positivity) hd
  have : n ≤ 2 * p := by omega
  have : n ^ 2 ≤ 4 * p ^ 2 := by nlinarith
  nlinarith [sq_nonneg p]

private theorem qpmc_mod (p x n : ℕ) (hx : 1 ≤ x) (hp : p.Prime) (hxp : x < p)
    (hn : n ∈ Finset.Ioc x (2 * x)) (hd : p ∣ n ^ 2 + 1) : p % 4 = 1 := by
  simp only [Finset.mem_Ioc] at hn
  haveI := Fact.mk hp
  rcases hp.eq_two_or_odd with h2 | h2
  · subst h2
    have : n = 2 := by omega
    subst this
    omega
  · have h0 := (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) p).2 hd
    have hsq : IsSquare (-1 : ZMod p) := by
      refine ⟨(n : ZMod p), ?_⟩
      push_cast at h0
      linear_combination (-1 : ZMod p) * h0
    have := ZMod.exists_sq_eq_neg_one_iff.1 hsq
    omega

theorem Conjectures.QuadraticPrimes.MiddleCoarse :
    let wgt := fun (n p : ℕ) => (((n ^ 2 + 1).factorization p : ℕ) : ℝ) * Real.log (p : ℝ); let middle := fun (x : ℕ) => Finset.sum (Finset.Ioc x (2 * x)) (fun n => Finset.sum ((n ^ 2 + 1).primeFactors.filter (fun p => x < p ∧ p ^ 100000 ≤ n ^ 132301)) (fun (p : ℕ) => wgt n p)); let apTheta := fun (x : ℕ) => Finset.sum ((Finset.range ((2 * x) ^ 132301 + 1)).filter (fun p => p.Prime ∧ p % 4 = 1)) (fun p => Real.log (p : ℝ)); ∀ x : ℕ, 1 ≤ x → middle x ≤ 4 * apTheta x := by
  intro wgt middle apTheta x hx
  simp only [middle, apTheta]
  set P := (Finset.range ((2 * x) ^ 132301 + 1)).filter (fun p => p.Prime ∧ p % 4 = 1) with hP
  have step1 : ∀ n ∈ Finset.Ioc x (2 * x),
      Finset.sum ((n ^ 2 + 1).primeFactors.filter (fun p => x < p ∧ p ^ 100000 ≤ n ^ 132301))
          (fun (p : ℕ) => wgt n p)
        ≤ Finset.sum P (fun p => if x < p ∧ p ∣ n ^ 2 + 1 then wgt n p else 0) := by
    intro n hn
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hpm
      simp only [Finset.mem_filter, Nat.mem_primeFactors] at hpm
      obtain ⟨⟨hpp, hpd, _⟩, hxp, hpow⟩ := hpm
      have hn' := Finset.mem_Ioc.1 hn
      simp only [hP, Finset.mem_filter, Finset.mem_range]
      refine ⟨⟨?_, hpp, qpmc_mod p x n hx hpp hxp hn hpd⟩, hxp, hpd⟩
      have h1 : p ≤ p ^ 100000 := Nat.le_self_pow (by norm_num) p
      have h2 : n ^ 132301 ≤ (2 * x) ^ 132301 := Nat.pow_le_pow_left hn'.2 _
      omega
    · intro p _ _
      simp only [wgt]
      have : (0 : ℝ) ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
      positivity
  refine (Finset.sum_le_sum step1).trans ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hpP
  simp only [hP, Finset.mem_filter, Finset.mem_range] at hpP
  obtain ⟨_, hpp, hp4⟩ := hpP
  have h5 : 5 ≤ p := by have := hpp.two_le; omega
  have hlog : (0 : ℝ) ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
  by_cases hxp : x < p
  · have e : ∀ n : ℕ, (if x < p ∧ p ∣ n ^ 2 + 1 then wgt n p else 0)
        = if p ∣ n ^ 2 + 1 then wgt n p else 0 := by
      intro n; simp [hxp]
    simp only [e]
    rw [← Finset.sum_filter]
    have hb : ∀ n ∈ (Finset.Ioc x (2 * x)).filter (fun n => p ∣ n ^ 2 + 1),
        wgt n p ≤ 2 * Real.log (p : ℝ) := by
      intro n hn
      have hn2 := (Finset.mem_Ioc.1 (Finset.mem_filter.1 hn).1).2
      have := qpmc_val p x n hpp h5 hxp hn2
      simp only [wgt]
      have : (((n ^ 2 + 1).factorization p : ℕ) : ℝ) ≤ 2 := by exact_mod_cast this
      nlinarith
    refine (Finset.sum_le_sum hb).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc : (((Finset.Ioc x (2 * x)).filter (fun n => p ∣ n ^ 2 + 1)).card : ℝ) ≤ 2 := by
      exact_mod_cast qpmc_card p x hpp hxp
    nlinarith
  · have e : ∀ n : ℕ, (if x < p ∧ p ∣ n ^ 2 + 1 then wgt n p else 0) = 0 := by
      intro n; simp [hxp]
    simp only [e, Finset.sum_const_zero]
    positivity

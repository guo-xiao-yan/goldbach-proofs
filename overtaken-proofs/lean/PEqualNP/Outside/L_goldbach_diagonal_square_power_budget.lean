import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

private lemma dsb_log2 : (1/2 : ℝ) ≤ Real.log 2 := by
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2⁻¹ by norm_num)
  rw [Real.log_inv] at h
  linarith

private lemma dsb_natlog (n : ℕ) (hn : 1 ≤ n) : (Nat.log 2 n : ℝ) ≤ 2 * Real.log n := by
  have h : 2 ^ (Nat.log 2 n) ≤ n := Nat.pow_log_le_self 2 (by omega)
  have h2 : (2:ℝ) ^ (Nat.log 2 n) ≤ n := by exact_mod_cast h
  have h3 := Real.log_le_log (by positivity) h2
  rw [Real.log_pow] at h3
  nlinarith [dsb_log2, (Nat.cast_nonneg (Nat.log 2 n) : (0:ℝ) ≤ _)]

private lemma dsb_omega (n : ℕ) (hn : 1 ≤ n) : (n.primeFactors.card : ℝ) ≤ 2 * Real.log n := by
  have h1 : 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p :=
    Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have h2 : ∏ p ∈ n.primeFactors, p ≤ n := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n)
  have h3 : (2:ℝ) ^ n.primeFactors.card ≤ n := by exact_mod_cast h1.trans h2
  have h4 := Real.log_le_log (by positivity) h3
  rw [Real.log_pow] at h4
  nlinarith [dsb_log2, (Nat.cast_nonneg n.primeFactors.card : (0:ℝ) ≤ _)]

private lemma dsb_S1 (n : ℕ) :
    ((Finset.range (n+1)).filter (fun k => ¬ k.Prime ∧ ArithmeticFunction.vonMangoldt k ≠ 0)).card
      ≤ (Nat.sqrt n + 1) * (Nat.log 2 n + 1) := by
  have hsub : (Finset.range (n+1)).filter (fun k => ¬ k.Prime ∧ ArithmeticFunction.vonMangoldt k ≠ 0)
      ⊆ ((Finset.range (Nat.sqrt n + 1)) ×ˢ (Finset.range (Nat.log 2 n + 1))).image (fun x => x.1 ^ x.2) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hkn, hnp, hΛ⟩ := hk
    have hpp : IsPrimePow k := ArithmeticFunction.vonMangoldt_ne_zero_iff.1 hΛ
    obtain ⟨p, a, hp, ha, hpa⟩ := (isPrimePow_nat_iff k).1 hpp
    have hp' : p.Prime := hp
    have ha2 : 2 ≤ a := by
      by_contra h
      have : a = 1 := by omega
      subst this
      simp at hpa
      exact hnp (hpa ▸ hp')
    have hkn' : p ^ a ≤ n := by omega
    have h1 : p * p ≤ p ^ a := by
      calc p * p = p ^ 2 := by ring
        _ ≤ p ^ a := Nat.pow_le_pow_right hp'.pos ha2
    have h2 : 2 ^ a ≤ p ^ a := Nat.pow_le_pow_left hp'.two_le a
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_range]
    refine ⟨(p, a), ⟨?_, ?_⟩, hpa⟩
    · have : p ≤ Nat.sqrt n := Nat.le_sqrt.2 (h1.trans hkn')
      simp only; omega
    · have : a ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (h2.trans hkn')
      simp only; omega
  calc _ ≤ (((Finset.range (Nat.sqrt n + 1)) ×ˢ (Finset.range (Nat.log 2 n + 1))).image (fun x => x.1 ^ x.2)).card :=
        Finset.card_le_card hsub
    _ ≤ ((Finset.range (Nat.sqrt n + 1)) ×ˢ (Finset.range (Nat.log 2 n + 1))).card := Finset.card_image_le
    _ = _ := by simp

private lemma dsb_S2 (n : ℕ) (hn : 1 ≤ n) :
    ((Finset.range (n+1)).filter (fun k => k.Prime ∧ ¬ k.Coprime n)).card ≤ n.primeFactors.card := by
  apply Finset.card_le_card
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_range] at hk
  obtain ⟨_, hp, hc⟩ := hk
  rw [Nat.mem_primeFactors]
  refine ⟨hp, ?_, by omega⟩
  by_contra h
  exact hc ((Nat.Prime.coprime_iff_not_dvd hp).2 h)

private lemma dsb_term (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : k ≤ n) :
    |(if k.Coprime n then (ArithmeticFunction.vonMangoldt k)^2 else 0)
      - ((if k.Prime then Real.log (k:ℝ) else 0))^2| ≤ (Real.log n)^2 := by
  have hΛ0 := ArithmeticFunction.vonMangoldt_nonneg (n := k)
  have hΛ : ArithmeticFunction.vonMangoldt k ≤ Real.log n := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp; exact Real.log_nonneg (by exact_mod_cast hn)
    · exact ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast hk))
  have hsq : (ArithmeticFunction.vonMangoldt k)^2 ≤ (Real.log n)^2 := by gcongr
  by_cases hp : k.Prime
  · rw [if_pos hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
    have hl : Real.log (k:ℝ) ≤ Real.log n := ArithmeticFunction.vonMangoldt_apply_prime hp ▸ hΛ
    have hl0 : 0 ≤ Real.log (k:ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
    have : Real.log (k:ℝ) ^ 2 ≤ Real.log n ^ 2 := by gcongr
    split_ifs
    · simp; positivity
    · rw [zero_sub, abs_neg, abs_of_nonneg (by positivity)]; exact this
  · rw [if_neg hp]
    split_ifs
    · rw [show (0:ℝ)^2 = 0 by norm_num, sub_zero, abs_of_nonneg (by positivity)]; exact hsq
    · simp; positivity

private lemma dsb_zero (n k : ℕ)
    (hk : k ∈ (Finset.range (n+1))) (hnm : k ∉ ((Finset.range (n+1)).filter (fun k => ¬ k.Prime ∧ ArithmeticFunction.vonMangoldt k ≠ 0)
      ∪ (Finset.range (n+1)).filter (fun k => k.Prime ∧ ¬ k.Coprime n))) :
    (if k.Coprime n then (ArithmeticFunction.vonMangoldt k)^2 else 0)
      - ((if k.Prime then Real.log (k:ℝ) else 0))^2 = 0 := by
  simp only [Finset.mem_union, Finset.mem_filter, not_or, not_and, not_not] at hnm
  by_cases hp : k.Prime
  · have hc : k.Coprime n := hnm.2 hk hp
    rw [if_pos hp, if_pos hc, ArithmeticFunction.vonMangoldt_apply_prime hp]; ring
  · have := hnm.1 hk hp
    rw [if_neg hp, this]
    split_ifs <;> simp

theorem PEqualNP.Outside.L_goldbach_diagonal_square_power_budget :
    let p := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let D := fun (φ : ℝ → ℝ) (n : ℕ) => (∑ k ∈ (Finset.range (n+1)).filter (fun k => k.Coprime n), (ArithmeticFunction.vonMangoldt k)^2*(φ ((k:ℝ)/n))^2)/(n:ℝ); ∃ K : ℝ, 0<K ∧ ∀ (n : ℕ) (φ : ℝ → ℝ), 2≤n → (∀ u, |φ u|≤1) → (∀ u : ℝ, u < 1/3 ∨ 2/3 < u → φ u=0) → |D φ n - (∑ k ∈ Finset.range (n+1), (p k)^2*(φ ((k:ℝ)/n))^2)/(n:ℝ)| ≤ K*(Real.log (2*(n:ℝ)))^3/Real.sqrt (n:ℝ) := by
  intro p D
  refine ⟨10, by norm_num, ?_⟩
  intro n φ hn hφ1 _
  set S1 := (Finset.range (n+1)).filter (fun k => ¬ k.Prime ∧ ArithmeticFunction.vonMangoldt k ≠ 0) with hS1
  set S2 := (Finset.range (n+1)).filter (fun k => k.Prime ∧ ¬ k.Coprime n) with hS2
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set E : ℕ → ℝ := fun k => (if k.Coprime n then (ArithmeticFunction.vonMangoldt k)^2 else 0)
      - ((if k.Prime then Real.log (k:ℝ) else 0))^2 with hE
  have hsq1 : ∀ k, (φ ((k:ℝ)/n))^2 ≤ 1 := by
    intro k
    have := hφ1 ((k:ℝ)/n)
    have h0 := abs_nonneg (φ ((k:ℝ)/n))
    nlinarith [sq_abs (φ ((k:ℝ)/n))]
  have hdiff : D φ n - (∑ k ∈ Finset.range (n+1), (p k)^2*(φ ((k:ℝ)/n))^2)/(n:ℝ)
      = (∑ k ∈ Finset.range (n+1), E k * (φ ((k:ℝ)/n))^2) / (n:ℝ) := by
    show (∑ k ∈ (Finset.range (n+1)).filter (fun k => k.Coprime n), (ArithmeticFunction.vonMangoldt k)^2*(φ ((k:ℝ)/n))^2)/(n:ℝ) - _ = _
    rw [Finset.sum_filter, ← sub_div, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro k _
    simp only [hE, p]
    split_ifs <;> ring
  have hpt : ∀ k ∈ Finset.range (n+1), |E k * (φ ((k:ℝ)/n))^2|
      ≤ if k ∈ S1 ∪ S2 then (Real.log n)^2 else 0 := by
    intro k hk
    split_ifs with hm
    · rw [abs_mul, abs_of_nonneg (sq_nonneg (φ ((k:ℝ)/n)))]
      calc |E k| * (φ ((k:ℝ)/n))^2 ≤ (Real.log n)^2 * 1 := by
            gcongr
            exact dsb_term n hn1 k (by simpa [Nat.lt_succ_iff] using hk)
            exact hsq1 k
        _ = _ := mul_one _
    · rw [show E k = 0 from dsb_zero n k hk hm]; simp
  have hsum : |∑ k ∈ Finset.range (n+1), E k * (φ ((k:ℝ)/n))^2|
      ≤ ((S1 ∪ S2).card : ℝ) * (Real.log n)^2 := by
    calc _ ≤ ∑ k ∈ Finset.range (n+1), |E k * (φ ((k:ℝ)/n))^2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range (n+1), (if k ∈ S1 ∪ S2 then (Real.log n)^2 else 0) :=
          Finset.sum_le_sum hpt
      _ = ((S1 ∪ S2).card : ℝ) * (Real.log n)^2 := by
          rw [Finset.sum_ite_mem, Finset.inter_eq_right.2]
          · simp
          · intro k hk
            simp only [hS1, hS2, Finset.mem_union, Finset.mem_filter] at hk
            rcases hk with h | h <;> exact h.1
  -- real-number bookkeeping
  set s := Real.sqrt (n:ℝ) with hs
  have hs1 : 1 ≤ s := by
    rw [hs]; exact Real.one_le_sqrt.2 (by exact_mod_cast hn1)
  have hss : s * s = n := Real.mul_self_sqrt hnpos.le
  set ℓ := Real.log (2 * (n:ℝ)) with hℓ
  have hln : Real.log n ≤ ℓ := Real.log_le_log hnpos (by linarith)
  have hl2 : (1/2:ℝ) ≤ ℓ := by
    have : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) (by
      have : (1:ℝ) ≤ n := by exact_mod_cast hn1
      linarith)
    linarith [dsb_log2]
  have hln0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  have hc1 : (S1.card : ℝ) ≤ ((Nat.sqrt n : ℝ) + 1) * ((Nat.log 2 n : ℝ) + 1) := by
    exact_mod_cast dsb_S1 n
  have hsq : (Nat.sqrt n : ℝ) ≤ s := Real.nat_sqrt_le_real_sqrt
  have hL := dsb_natlog n hn1
  have hω := dsb_omega n hn1
  have hc2 : (S2.card : ℝ) ≤ n.primeFactors.card := by exact_mod_cast dsb_S2 n hn1
  have hcu : ((S1 ∪ S2).card : ℝ) ≤ S1.card + S2.card := by exact_mod_cast Finset.card_union_le _ _
  have hL0 : (0:ℝ) ≤ Nat.log 2 n := Nat.cast_nonneg _
  have hsq0 : (0:ℝ) ≤ Nat.sqrt n := Nat.cast_nonneg _
  have hcard : ((S1 ∪ S2).card : ℝ) ≤ 10 * s * ℓ := by
    have h1 : (S1.card : ℝ) ≤ 8 * s * ℓ := by
      calc (S1.card : ℝ) ≤ ((Nat.sqrt n : ℝ) + 1) * ((Nat.log 2 n : ℝ) + 1) := hc1
        _ ≤ (2 * s) * (4 * ℓ) := by
          apply mul_le_mul <;> nlinarith
        _ = 8 * s * ℓ := by ring
    nlinarith
  have hfin : |∑ k ∈ Finset.range (n+1), E k * (φ ((k:ℝ)/n))^2| ≤ 10 * s * ℓ ^ 3 := by
    refine hsum.trans ?_
    have hlsq : (Real.log n)^2 ≤ ℓ^2 := by gcongr
    calc ((S1 ∪ S2).card : ℝ) * (Real.log n)^2 ≤ (10 * s * ℓ) * ℓ^2 := by
          apply mul_le_mul hcard hlsq (by positivity) (by positivity)
      _ = 10 * s * ℓ ^ 3 := by ring
  rw [hdiff, abs_div, abs_of_pos hnpos, div_le_div_iff₀ hnpos (by linarith)]
  calc |∑ k ∈ Finset.range (n+1), E k * (φ ((k:ℝ)/n))^2| * s ≤ (10 * s * ℓ ^ 3) * s :=
        mul_le_mul_of_nonneg_right hfin (by linarith)
    _ = 10 * ℓ ^ 3 * (n:ℝ) := by rw [← hss]; ring

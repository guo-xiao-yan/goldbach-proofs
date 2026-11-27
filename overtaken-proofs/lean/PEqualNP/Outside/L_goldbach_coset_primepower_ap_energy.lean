import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

open Classical in
private lemma pp_card (n : ℕ) :
    ((Finset.range (n+1)).filter (fun k => ∃ b a : ℕ, 2 ≤ b ∧ 2 ≤ a ∧ b^a = k)).card
      ≤ Nat.sqrt n * Nat.log 2 n := by
  have hsub : (Finset.range (n+1)).filter (fun k => ∃ b a : ℕ, 2 ≤ b ∧ 2 ≤ a ∧ b^a = k) ⊆
      (Finset.Icc 2 (Nat.sqrt n) ×ˢ Finset.Icc 2 (Nat.log 2 n)).image (fun p : ℕ × ℕ => p.1 ^ p.2) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hkn, b, a, hb, ha, rfl⟩ := hk
    have hkn' : b ^ a ≤ n := by omega
    rw [Finset.mem_image]
    refine ⟨(b, a), ?_, rfl⟩
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨hb, ?_⟩, ha, ?_⟩
    · rw [Nat.le_sqrt']
      exact le_trans (Nat.pow_le_pow_right (by omega) ha) hkn'
    · apply Nat.le_log_of_pow_le Nat.one_lt_two
      exact le_trans (Nat.pow_le_pow_left hb a) hkn'
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_image_le
    _ = (Nat.sqrt n + 1 - 2) * (Nat.log 2 n + 1 - 2) := by simp
    _ ≤ Nat.sqrt n * Nat.log 2 n := Nat.mul_le_mul (by omega) (by omega)

private lemma log2_le (n : ℕ) (hn : 1 ≤ n) : (Nat.log 2 n : ℝ) ≤ 2 * Real.log (n : ℝ) := by
  have h1 : (2 : ℕ) ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have h2 : ((2 : ℝ)) ^ Nat.log 2 n ≤ (n : ℝ) := by exact_mod_cast h1
  have h3 : Real.log ((2 : ℝ) ^ Nat.log 2 n) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by positivity) h2
  rw [Real.log_pow] at h3
  have h4 := Real.log_two_gt_d9
  have h5 : (0 : ℝ) ≤ (Nat.log 2 n : ℝ) := Nat.cast_nonneg _
  nlinarith

open Classical in
private lemma diff_total (n : ℕ) :
    ∑ k ∈ Finset.range (n+1), (ArithmeticFunction.vonMangoldt k - (if k.Prime then Real.log (k:ℝ) else 0))
      ≤ ((Nat.sqrt n * Nat.log 2 n : ℕ) : ℝ) * Real.log (n : ℝ) := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hpt : ∀ k ∈ Finset.range (n+1),
      ArithmeticFunction.vonMangoldt k - (if k.Prime then Real.log (k:ℝ) else 0)
        ≤ if (∃ b a : ℕ, 2 ≤ b ∧ 2 ≤ a ∧ b^a = k) then Real.log (n : ℝ) else 0 := by
    intro k hk
    have hkn : k ≤ n := by simp only [Finset.mem_range] at hk; omega
    by_cases hp : k.Prime
    · rw [if_pos hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
      split_ifs <;> linarith
    · rw [if_neg hp, sub_zero]
      by_cases h0 : ArithmeticFunction.vonMangoldt k = 0
      · rw [h0]; split_ifs <;> linarith
      · have hpp : IsPrimePow k := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h0
        obtain ⟨p, a, hpr, ha, hpa⟩ := (isPrimePow_nat_iff k).mp hpp
        have ha2 : 2 ≤ a := by
          by_contra hlt
          have : a = 1 := by omega
          subst this
          have hkp : k = p := by simpa using hpa.symm
          exact hp (hkp ▸ hpr)
        rw [if_pos ⟨p, a, hpr.two_le, ha2, hpa⟩]
        have hk0 : 0 < k := hpp.pos
        calc ArithmeticFunction.vonMangoldt k ≤ Real.log (k : ℝ) := ArithmeticFunction.vonMangoldt_le_log
          _ ≤ Real.log (n : ℝ) := Real.log_le_log (by exact_mod_cast hk0) (by exact_mod_cast hkn)
  calc _ ≤ ∑ k ∈ Finset.range (n+1), (if (∃ b a : ℕ, 2 ≤ b ∧ 2 ≤ a ∧ b^a = k) then Real.log (n : ℝ) else 0) :=
        Finset.sum_le_sum hpt
    _ = (((Finset.range (n+1)).filter (fun k => ∃ b a : ℕ, 2 ≤ b ∧ 2 ≤ a ∧ b^a = k)).card : ℝ) * Real.log (n : ℝ) := by
        rw [← Finset.sum_filter]; simp
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hlog
        exact_mod_cast pp_card n

private lemma total_bound (n : ℕ) (hn : 2 ≤ n) :
    ∑ k ∈ Finset.range (n+1), (ArithmeticFunction.vonMangoldt k - (if k.Prime then Real.log (k:ℝ) else 0))
      ≤ 2 * Real.sqrt (n:ℝ) * (Real.log (2 * (n:ℝ)))^2 := by
  refine le_trans (diff_total n) ?_
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hl2 : Real.log (n : ℝ) ≤ Real.log (2 * (n : ℝ)) :=
    Real.log_le_log (by linarith) (by linarith)
  have hs : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := Real.nat_sqrt_le_real_sqrt
  have hs0 : (0 : ℝ) ≤ (Nat.sqrt n : ℝ) := Nat.cast_nonneg _
  have hL := log2_le n (by omega)
  have hL0 : (0 : ℝ) ≤ (Nat.log 2 n : ℝ) := Nat.cast_nonneg _
  push_cast
  have h1 : (Nat.sqrt n : ℝ) * (Nat.log 2 n : ℝ) ≤ Real.sqrt (n : ℝ) * (2 * Real.log (2 * (n : ℝ))) :=
    mul_le_mul hs (by linarith) hL0 (Real.sqrt_nonneg _)
  have h2 : 0 ≤ Real.log (2 * (n : ℝ)) := hlog.trans hl2
  have h3 := Real.sqrt_nonneg (n : ℝ)
  calc (Nat.sqrt n : ℝ) * (Nat.log 2 n : ℝ) * Real.log (n : ℝ)
      ≤ (Real.sqrt (n : ℝ) * (2 * Real.log (2 * (n : ℝ)))) * Real.log (2 * (n : ℝ)) :=
        mul_le_mul h1 hl2 hlog (by positivity)
    _ = 2 * Real.sqrt (n:ℝ) * (Real.log (2 * (n:ℝ)))^2 := by ring

theorem PEqualNP.Outside.L_goldbach_coset_primepower_ap_energy :
    let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q=r); let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let A := fun n q r : ℕ => ∑ k ∈ F n q r, w k; ∃ C : ℝ, 0<C ∧ ∀ n q : ℕ, 2≤n → 0<q → (∑ r ∈ Finset.range q, ((∑ k ∈ F n q r, ArithmeticFunction.vonMangoldt k)-A n q r)^2) ≤ C*(n:ℝ)*(Real.log (2*(n:ℝ)))^4 := by
  intro F w A
  refine ⟨4, by norm_num, ?_⟩
  intro n q hn hq
  have hnn : ∀ k, 0 ≤ ArithmeticFunction.vonMangoldt k - w k := by
    intro k
    by_cases hp : k.Prime
    · simp only [w, if_pos hp, ArithmeticFunction.vonMangoldt_apply_prime hp]; simp
    · simp only [w, if_neg hp, sub_zero]; exact ArithmeticFunction.vonMangoldt_nonneg
  have hd : ∀ r, (∑ k ∈ F n q r, ArithmeticFunction.vonMangoldt k) - A n q r
      = ∑ k ∈ F n q r, (ArithmeticFunction.vonMangoldt k - w k) := by
    intro r
    simp only [A, Finset.sum_sub_distrib]
  have hd0 : ∀ r, 0 ≤ ∑ k ∈ F n q r, (ArithmeticFunction.vonMangoldt k - w k) :=
    fun r => Finset.sum_nonneg (fun k _ => hnn k)
  have htot : ∑ r ∈ Finset.range q, ∑ k ∈ F n q r, (ArithmeticFunction.vonMangoldt k - w k)
      = ∑ k ∈ Finset.range (n+1), (ArithmeticFunction.vonMangoldt k - w k) := by
    apply Finset.sum_fiberwise_of_maps_to (g := fun k => k % q)
    intro k _
    exact Finset.mem_range.mpr (Nat.mod_lt k hq)
  have hT := total_bound n hn
  have hT0 : 0 ≤ ∑ k ∈ Finset.range (n+1), (ArithmeticFunction.vonMangoldt k - w k) :=
    Finset.sum_nonneg (fun k _ => hnn k)
  simp only [hd]
  have hsq : ∑ r ∈ Finset.range q, (∑ k ∈ F n q r, (ArithmeticFunction.vonMangoldt k - w k))^2
      ≤ (∑ r ∈ Finset.range q, ∑ k ∈ F n q r, (ArithmeticFunction.vonMangoldt k - w k))^2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun r _ => hd0 r)
  rw [htot] at hsq
  have hs : 0 ≤ Real.sqrt (n:ℝ) := Real.sqrt_nonneg _
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hT' : ∑ k ∈ Finset.range (n+1), (ArithmeticFunction.vonMangoldt k - w k)
      ≤ 2 * Real.sqrt (n:ℝ) * (Real.log (2 * (n:ℝ)))^2 := hT
  calc _ ≤ _ := hsq
    _ ≤ (2 * Real.sqrt (n:ℝ) * (Real.log (2 * (n:ℝ)))^2)^2 := pow_le_pow_left₀ hT0 hT' 2
    _ = 4 * (Real.sqrt (n:ℝ))^2 * (Real.log (2 * (n:ℝ)))^4 := by ring
    _ = 4 * (n:ℝ) * (Real.log (2 * (n:ℝ)))^4 := by rw [Real.sq_sqrt hn0]

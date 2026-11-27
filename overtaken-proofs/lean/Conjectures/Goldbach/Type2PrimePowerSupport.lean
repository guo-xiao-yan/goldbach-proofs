import Mathlib

private theorem t2pp_sum_inv_sqrt (B : ℕ) :
    ∑ a ∈ Finset.Icc 1 B, (1 / Real.sqrt (a : ℝ)) ≤ 2 * Real.sqrt (B : ℝ) := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hs : 0 < Real.sqrt ((B + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
    have ht : 0 ≤ Real.sqrt (B : ℝ) := Real.sqrt_nonneg _
    have hs2 : Real.sqrt ((B + 1 : ℕ) : ℝ) ^ 2 = (B : ℝ) + 1 := by
      rw [Real.sq_sqrt (by positivity)]; push_cast; ring
    have ht2 : Real.sqrt (B : ℝ) ^ 2 = (B : ℝ) := Real.sq_sqrt (by positivity)
    have key : 1 / Real.sqrt ((B + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt ((B + 1 : ℕ) : ℝ) - 2 * Real.sqrt (B : ℝ) := by
      rw [div_le_iff₀ hs]
      nlinarith [sq_nonneg (Real.sqrt ((B + 1 : ℕ) : ℝ) - Real.sqrt (B : ℝ))]
    linarith

private theorem t2pp_changed (j : ℕ) (hj : ArithmeticFunction.vonMangoldt j ≠ (if Nat.Prime j then Real.log (j : ℝ) else 0)) :
    ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ j = p ^ k := by
  by_cases hp : Nat.Prime j
  · exfalso
    apply hj
    rw [if_pos hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
  · rw [if_neg hp] at hj
    have := ArithmeticFunction.vonMangoldt_ne_zero_iff.1 hj
    obtain ⟨p, k, hp', hk, rfl⟩ := this
    refine ⟨p, k, Nat.prime_iff.2 hp', ?_, rfl⟩
    by_contra h
    have : k = 1 := by omega
    subst this
    exact hp (by simpa using Nat.prime_iff.2 hp')

theorem Conjectures.Goldbach.Type2PrimePowerSupport :
    ∀ n U B : ℕ, let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0; let coeff := fun (v : ℕ → ℝ) (m : ℕ) => ∑ a ∈ m.divisors.filter (fun a => U < a ∧ a ≤ B ∧ U < m / a), (∑ d ∈ a.divisors.filter (fun d => U < d), ((ArithmeticFunction.moebius d : ℤ) : ℝ)) * v (m / a); (((Finset.range (n + 1)).filter (fun m => coeff ArithmeticFunction.vonMangoldt m ≠ coeff w m)).card : ℝ) ≤ 2 * Real.sqrt n * Real.sqrt B * (Nat.log 2 n : ℝ) := by
  intro n U B w coeff
  set L := Nat.log 2 n with hL
  let T : ℕ → ℕ → Finset ℕ := fun a k => (Finset.Icc 1 (Nat.sqrt (n / a))).image (fun p => a * p ^ k)
  have hsub : (Finset.range (n + 1)).filter (fun m => coeff ArithmeticFunction.vonMangoldt m ≠ coeff w m)
      ⊆ (Finset.Icc 1 B).biUnion (fun a => (Finset.Icc 2 L).biUnion (fun k => T a k)) := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_range] at hm
    obtain ⟨hmn, hne⟩ := hm
    have hex : ∃ a ∈ m.divisors.filter (fun a => U < a ∧ a ≤ B ∧ U < m / a),
        ArithmeticFunction.vonMangoldt (m / a) ≠ w (m / a) := by
      by_contra hcon
      push_neg at hcon
      apply hne
      simp only [coeff]
      apply Finset.sum_congr rfl
      intro a ha
      rw [hcon a ha]
    obtain ⟨a, ha, hav⟩ := hex
    rw [Finset.mem_filter, Nat.mem_divisors] at ha
    obtain ⟨⟨hadvd, hm0⟩, _, haB, _⟩ := ha
    have ha0 : 0 < a := Nat.pos_of_dvd_of_pos hadvd (Nat.pos_of_ne_zero hm0)
    obtain ⟨p, k, hp, hk, hpk⟩ := t2pp_changed (m / a) hav
    have hmeq : m = a * p ^ k := by
      rw [← hpk]; exact (Nat.mul_div_cancel' hadvd).symm
    have hp2 := hp.two_le
    have hpk2 : p * p ≤ p ^ k := by
      calc p * p = p ^ 2 := by ring
        _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
    have h2k : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp2 k
    have hapk : a * p ^ k ≤ n := by omega
    have hpk' : p ^ k ≤ n := le_trans (Nat.le_mul_of_pos_left _ ha0) hapk
    rw [Finset.mem_biUnion]
    refine ⟨a, Finset.mem_Icc.2 ⟨ha0, haB⟩, ?_⟩
    rw [Finset.mem_biUnion]
    refine ⟨k, Finset.mem_Icc.2 ⟨hk, Nat.le_log_of_pow_le (by norm_num) (le_trans h2k hpk')⟩, ?_⟩
    rw [Finset.mem_image]
    refine ⟨p, Finset.mem_Icc.2 ⟨hp.pos, ?_⟩, hmeq.symm⟩
    rw [Nat.le_sqrt]
    apply (Nat.le_div_iff_mul_le ha0).2
    calc p * p * a ≤ p ^ k * a := Nat.mul_le_mul_right _ hpk2
      _ = a * p ^ k := by ring
      _ ≤ n := hapk
  have hcard : ((Finset.range (n + 1)).filter (fun m => coeff ArithmeticFunction.vonMangoldt m ≠ coeff w m)).card
      ≤ ∑ a ∈ Finset.Icc 1 B, ∑ k ∈ Finset.Icc 2 L, Nat.sqrt (n / a) := by
    refine le_trans (Finset.card_le_card hsub) ?_
    refine le_trans Finset.card_biUnion_le ?_
    apply Finset.sum_le_sum
    intro a _
    refine le_trans Finset.card_biUnion_le ?_
    apply Finset.sum_le_sum
    intro k _
    refine le_trans Finset.card_image_le ?_
    simp
  have hreal : ((∑ a ∈ Finset.Icc 1 B, ∑ k ∈ Finset.Icc 2 L, Nat.sqrt (n / a) : ℕ) : ℝ)
      ≤ ∑ a ∈ Finset.Icc 1 B, (L : ℝ) * (Real.sqrt n * (1 / Real.sqrt (a : ℝ))) := by
    push_cast
    apply Finset.sum_le_sum
    intro a ha
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    have ha0 : (0 : ℝ) < a := by
      have := (Finset.mem_Icc.1 ha).1
      exact_mod_cast this
    have h1 : ((Nat.sqrt (n / a) : ℕ) : ℝ) ≤ Real.sqrt n * (1 / Real.sqrt (a : ℝ)) := by
      calc ((Nat.sqrt (n / a) : ℕ) : ℝ) ≤ Real.sqrt ((n / a : ℕ) : ℝ) := Real.nat_sqrt_le_real_sqrt
        _ ≤ Real.sqrt ((n : ℝ) / a) := Real.sqrt_le_sqrt (Nat.cast_div_le)
        _ = Real.sqrt n * (1 / Real.sqrt (a : ℝ)) := by
          rw [Real.sqrt_div (by positivity)]; ring
    have h2 : (((L + 1 - 2 : ℕ)) : ℝ) ≤ L := by
      have : L + 1 - 2 ≤ L := by omega
      exact_mod_cast this
    have h3 : 0 ≤ Real.sqrt n * (1 / Real.sqrt (a : ℝ)) := by positivity
    have h4 : (0 : ℝ) ≤ ((Nat.sqrt (n / a) : ℕ) : ℝ) := by positivity
    calc (((L + 1 - 2 : ℕ)) : ℝ) * ((Nat.sqrt (n / a) : ℕ) : ℝ)
        ≤ (L : ℝ) * ((Nat.sqrt (n / a) : ℕ) : ℝ) := mul_le_mul_of_nonneg_right h2 h4
      _ ≤ (L : ℝ) * (Real.sqrt n * (1 / Real.sqrt (a : ℝ))) := mul_le_mul_of_nonneg_left h1 (by positivity)
  calc (((Finset.range (n + 1)).filter (fun m => coeff ArithmeticFunction.vonMangoldt m ≠ coeff w m)).card : ℝ)
      ≤ ((∑ a ∈ Finset.Icc 1 B, ∑ k ∈ Finset.Icc 2 L, Nat.sqrt (n / a) : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ a ∈ Finset.Icc 1 B, (L : ℝ) * (Real.sqrt n * (1 / Real.sqrt (a : ℝ))) := hreal
    _ = (L : ℝ) * Real.sqrt n * ∑ a ∈ Finset.Icc 1 B, (1 / Real.sqrt (a : ℝ)) := by
        rw [mul_assoc, Finset.mul_sum, Finset.mul_sum]
    _ ≤ (L : ℝ) * Real.sqrt n * (2 * Real.sqrt (B : ℝ)) :=
        mul_le_mul_of_nonneg_left (t2pp_sum_inv_sqrt B) (by positivity)
    _ = 2 * Real.sqrt n * Real.sqrt B * (L : ℝ) := by ring

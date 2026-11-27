import Mathlib

namespace GbTS

noncomputable def E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

theorem E_add (x y : ℝ) : E (x + y) = E x * E y := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem E_norm (x : ℝ) : ‖E x‖ = 1 := by
  unfold E
  exact Complex.norm_exp_ofReal_mul_I _

theorem E_neg (x : ℝ) : E (-x) = (starRingEnd ℂ) (E x) := by
  unfold E
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

theorem E_nat (m : ℕ) (x : ℝ) : E ((m : ℝ) * x) = (E x) ^ m := by
  induction m with
  | zero => simp [E]
  | succ m ih =>
    rw [pow_succ, ← ih, ← E_add]
    congr 1
    push_cast
    ring

theorem geom_bound (H M M' : ℕ) (x : ℝ) (hM : M' ≤ M + H) :
    ‖∑ m ∈ Finset.Ico M M', E ((m : ℝ) * x)‖ ≤
      (if E x = 1 then (H : ℝ) else min (H : ℝ) (2 / ‖1 - E x‖)) := by
  have hcard : ‖∑ m ∈ Finset.Ico M M', E ((m : ℝ) * x)‖ ≤ (H : ℝ) := by
    calc ‖∑ m ∈ Finset.Ico M M', E ((m : ℝ) * x)‖ ≤ ∑ m ∈ Finset.Ico M M', ‖E ((m : ℝ) * x)‖ :=
          norm_sum_le _ _
      _ = ((Finset.Ico M M').card : ℝ) := by simp [E_norm]
      _ ≤ (H : ℝ) := by
          rw [Nat.card_Ico]
          have : M' - M ≤ H := by omega
          exact_mod_cast this
  split_ifs with h1
  · exact hcard
  · refine le_min hcard ?_
    have hne : (E x) - 1 ≠ 0 := sub_ne_zero.mpr h1
    have hpos : 0 < ‖1 - E x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm h1))
    rw [le_div_iff₀ hpos]
    simp_rw [E_nat]
    by_cases hle : M' ≤ M
    · rw [Finset.Ico_eq_empty (by omega)]
      simp
    · rw [Finset.sum_Ico_eq_sum_range]
      simp_rw [pow_add]
      rw [← Finset.mul_sum, geom_sum_eq h1, norm_mul, norm_div, norm_pow, E_norm, one_pow, one_mul]
      have : ‖(E x) ^ (M' - M) - 1‖ ≤ 2 := by
        calc ‖(E x) ^ (M' - M) - 1‖ ≤ ‖(E x) ^ (M' - M)‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
          _ = 2 := by rw [norm_pow, E_norm]; norm_num
      have h2 : ‖E x - 1‖ = ‖1 - E x‖ := norm_sub_rev _ _
      rw [h2, div_mul_cancel₀ _ hpos.ne'] 
      exact this

theorem initial_segment (N M H k l : ℕ) :
    ∃ M', M' ≤ M + H ∧
      (Finset.Ico M (M + H)).filter (fun m => m * k ≤ N ∧ m * l ≤ N) = Finset.Ico M M' := by
  by_cases hc : max k l = 0
  · refine ⟨M + H, le_rfl, ?_⟩
    have hk : k = 0 := by omega
    have hl : l = 0 := by omega
    subst hk; subst hl
    apply Finset.filter_true_of_mem
    intro m _
    simp
  · refine ⟨min (M + H) (N / max k l + 1), by omega, ?_⟩
    ext m
    simp only [Finset.mem_filter, Finset.mem_Ico]
    have key : (m * k ≤ N ∧ m * l ≤ N) ↔ m ≤ N / max k l := by
      rw [Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hc)]
      rcases le_total k l with h | h
      · rw [max_eq_right h]
        exact ⟨fun h2 => h2.2, fun h2 => ⟨le_trans (Nat.mul_le_mul_left m h) h2, h2⟩⟩
      · rw [max_eq_left h]
        exact ⟨fun h2 => h2.1, fun h2 => ⟨h2, le_trans (Nat.mul_le_mul_left m h) h2⟩⟩
    rw [key]
    omega

theorem type_two (N M H : ℕ) (K : Finset ℕ) (a b : ℕ → ℂ) (t : ℝ) :
    ‖∑ m ∈ Finset.Ico M (M+H), a m * ∑ k ∈ K, (if m*k ≤ N then b k * E ((m : ℝ) * (k : ℝ) * t) else 0)‖ ^ 2 ≤
      (∑ m ∈ Finset.Ico M (M+H), ‖a m‖ ^ 2) *
      (∑ k ∈ K, ∑ l ∈ K, ‖b k‖ * ‖b l‖ *
        (if E (((k : ℝ) - (l : ℝ)) * t) = 1 then (H : ℝ)
          else min (H : ℝ) (2 / ‖1 - E (((k : ℝ) - (l : ℝ)) * t)‖))) := by
  set I := Finset.Ico M (M+H) with hI
  set T : ℕ → ℂ := fun m => ∑ k ∈ K, (if m*k ≤ N then b k * E ((m : ℝ) * (k : ℝ) * t) else 0) with hT
  have step1 : ‖∑ m ∈ I, a m * T m‖ ^ 2 ≤ (∑ m ∈ I, ‖a m‖ ^ 2) * (∑ m ∈ I, ‖T m‖ ^ 2) := by
    have h1 : ‖∑ m ∈ I, a m * T m‖ ≤ ∑ m ∈ I, ‖a m‖ * ‖T m‖ := by
      refine (norm_sum_le _ _).trans ?_
      simp [norm_mul]
    calc ‖∑ m ∈ I, a m * T m‖ ^ 2 ≤ (∑ m ∈ I, ‖a m‖ * ‖T m‖) ^ 2 := by gcongr
      _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  refine step1.trans (mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun _ _ => by positivity))
  have expand : ∀ m : ℕ, (((‖T m‖ ^ 2 : ℝ)) : ℂ) =
      ∑ k ∈ K, ∑ l ∈ K, (if m * k ≤ N ∧ m * l ≤ N then
        b k * (starRingEnd ℂ) (b l) * E ((m : ℝ) * (((k : ℝ) - (l : ℝ)) * t)) else 0) := by
    intro m
    push_cast
    rw [← Complex.mul_conj']
    simp only [hT, map_sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h1 : m * k ≤ N <;> by_cases h2 : m * l ≤ N <;> simp only [h1, h2, if_true, if_false, and_self, and_true, true_and, and_false, false_and, map_zero, mul_zero, zero_mul]
    rw [map_mul]
    have : E ((m : ℝ) * (((k : ℝ) - (l : ℝ)) * t)) =
        E ((m : ℝ) * (k : ℝ) * t) * (starRingEnd ℂ) (E ((m : ℝ) * (l : ℝ) * t)) := by
      rw [← E_neg, ← E_add]; congr 1; ring
    rw [this]; ring
  have hsum : ∑ m ∈ I, ‖T m‖ ^ 2 = ‖∑ k ∈ K, ∑ l ∈ K, b k * (starRingEnd ℂ) (b l) *
      ∑ m ∈ I.filter (fun m => m * k ≤ N ∧ m * l ≤ N), E ((m : ℝ) * (((k : ℝ) - (l : ℝ)) * t))‖ := by
    have : ((∑ m ∈ I, ‖T m‖ ^ 2 : ℝ) : ℂ) = ∑ k ∈ K, ∑ l ∈ K, b k * (starRingEnd ℂ) (b l) *
        ∑ m ∈ I.filter (fun m => m * k ≤ N ∧ m * l ≤ N), E ((m : ℝ) * (((k : ℝ) - (l : ℝ)) * t)) := by
      rw [Complex.ofReal_sum]
      simp_rw [expand]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum, Finset.sum_filter]
    rw [← this, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity)]
  rw [hsum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [norm_mul, norm_mul, Complex.norm_conj]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  obtain ⟨M', hM', hset⟩ := initial_segment N M H k l
  rw [hset]
  exact geom_bound H M M' _ hM'

end GbTS

theorem Conjectures.Goldbach.TypeIiSpacingBound :
    let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); let cap (H : ℕ) (x : ℝ) := if E x = 1 then (H : ℝ) else min (H : ℝ) (2 / ‖1 - E x‖); ∀ (N M H : ℕ) (K : Finset ℕ) (a b : ℕ → ℂ) (t : ℝ), let I := Finset.Ico M (M+H); ‖∑ m ∈ I, a m * ∑ k ∈ K, (if m*k ≤ N then b k * E ((m : ℝ) * (k : ℝ) * t) else 0)‖ ^ 2 ≤ (∑ m ∈ I, ‖a m‖ ^ 2) * (∑ k ∈ K, ∑ l ∈ K, ‖b k‖ * ‖b l‖ * cap H (((k : ℝ) - (l : ℝ)) * t)) := by
  intro E cap N M H K a b t I
  exact GbTS.type_two N M H K a b t

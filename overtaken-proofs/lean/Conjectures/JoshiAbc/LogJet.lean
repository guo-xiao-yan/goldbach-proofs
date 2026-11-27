import Mathlib

theorem Conjectures.JoshiAbc.LogJet :
    ∀ (K : Type) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K] (r : K), r^14=(29:K) → 0 < ‖r‖ → ‖r‖<1 → (∀ n : ℕ, 0<n → ‖(n:K)‖ = ‖r‖^(14*multiplicity 29 n)) → ∀ x : K, ‖x‖ ≤ ‖r‖ → ‖(∑' k : ℕ, (-1:K)^k*((29:K)*x)^(k+1)/((k+1:ℕ):K))/(29:K)-x‖ ≤ ‖r‖^4 := by
  intro K _ _ _ _ r hr hρ0 hρ1 hv x hx
  have h29 : ‖(29:K)‖ = ‖r‖^14 := by rw [← hr, norm_pow]
  have h29x : ‖(29:K) * x‖ ≤ ‖r‖^15 := by
    have e : ‖r‖^15 = ‖r‖^14 * ‖r‖ := pow_succ ‖r‖ 14
    rw [norm_mul, h29, e]
    exact mul_le_mul_of_nonneg_left hx (by positivity)
  have key : ∀ k E : ℕ, 14 * multiplicity 29 (k+1) + E ≤ 15 * (k+1) →
      ‖(-1:K)^k*((29:K)*x)^(k+1)/((k+1:ℕ):K)‖ ≤ ‖r‖^E := by
    intro k E hE
    have hvk := hv (k+1) (Nat.succ_pos k)
    rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow, hvk]
    have hp : 0 < ‖r‖^(14 * multiplicity 29 (k+1)) := by positivity
    rw [div_le_iff₀ hp, ← pow_add]
    calc ‖(29:K) * x‖^(k+1) ≤ (‖r‖^15)^(k+1) := pow_le_pow_left₀ (norm_nonneg _) h29x _
      _ = ‖r‖^(15*(k+1)) := by rw [← pow_mul]
      _ ≤ ‖r‖^(E + 14 * multiplicity 29 (k+1)) :=
        pow_le_pow_of_le_one hρ0.le hρ1.le (by omega)
  have hm : ∀ k : ℕ, 29 * multiplicity 29 (k+1) ≤ k+1 := fun k => mul_multiplicity_le
  have hs : Summable (fun k : ℕ => (-1:K)^k*((29:K)*x)^(k+1)/((k+1:ℕ):K)) := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hρ0.le hρ1).mul_right ‖r‖) fun k => ?_
    rw [← pow_succ]
    exact key k (k+1) (by have := hm k; omega)
  rw [hs.tsum_eq_zero_add]
  have h29ne : (29:K) ≠ 0 := by norm_num
  have h0 : (-1:K)^0*((29:K)*x)^(0+1)/((0+1:ℕ):K) = 29 * x := by simp
  rw [h0, add_div, mul_div_cancel_left₀ _ h29ne, add_sub_cancel_left, norm_div, h29,
    div_le_iff₀ (by positivity)]
  have hT : ‖∑' k : ℕ, (-1:K)^(k+1)*((29:K)*x)^(k+1+1)/((k+1+1:ℕ):K)‖ ≤ ‖r‖^18 := by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun k => ?_
    exact key (k+1) 18 (by have := hm (k+1); omega)
  calc _ ≤ ‖r‖^18 := hT
    _ = ‖r‖^4 * ‖r‖^14 := by rw [← pow_add]

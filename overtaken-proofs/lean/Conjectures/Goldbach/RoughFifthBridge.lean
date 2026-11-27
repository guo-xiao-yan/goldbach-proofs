import Mathlib

private theorem rfb_prod_ge (q : ℕ) : ∀ l : List ℕ, (∀ x ∈ l, q ≤ x) → q ^ l.length ≤ l.prod := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
    intro h
    simp only [List.length_cons, List.prod_cons, pow_succ]
    have h1 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have h2 := h a (List.mem_cons_self)
    calc q ^ t.length * q ≤ t.prod * a := Nat.mul_le_mul h1 h2
      _ = a * t.prod := by ring

private theorem rfb_pointwise (N m : ℕ) (hm : 2 ≤ m) (hlt : m < N) (hq : N < m.minFac ^ 5) :
    (2 * (if Nat.Prime m then (1:ℝ) else 0)) =
      1 - (ArithmeticFunction.liouville m : ℝ) - 2 * (if ArithmeticFunction.cardFactors m = 3 then (1:ℝ) else 0) := by
  have hm0 : m ≠ 0 := by omega
  have hge : m.minFac ^ (ArithmeticFunction.cardFactors m) ≤ m := by
    rw [ArithmeticFunction.cardFactors_apply]
    conv_rhs => rw [← Nat.prod_primeFactorsList hm0]
    apply rfb_prod_ge
    intro x hx
    exact Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactorsList hx).two_le
      (Nat.dvd_of_mem_primeFactorsList hx)
  have hpos : 0 < ArithmeticFunction.cardFactors m := by
    rw [Nat.pos_iff_ne_zero]
    intro h
    rw [ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one] at h
    omega
  have hle : ArithmeticFunction.cardFactors m ≤ 4 := by
    by_contra h
    have h5 : 5 ≤ ArithmeticFunction.cardFactors m := by omega
    have := Nat.pow_le_pow_right (Nat.minFac_pos m) h5
    omega
  rw [ArithmeticFunction.liouville_apply hm0]
  have hp : Nat.Prime m ↔ ArithmeticFunction.cardFactors m = 1 :=
    ArithmeticFunction.cardFactors_eq_one_iff_prime.symm
  generalize ArithmeticFunction.cardFactors m = k at *
  interval_cases k <;> simp [hp]  <;> norm_num

theorem Conjectures.Goldbach.RoughFifthBridge :
    let C := fun N : ℕ => (Finset.range N).filter (fun p => Nat.Prime p ∧ N < 3*p ∧ 3*p < 2*N ∧ 1 < N-p ∧ N < (N-p).minFac^5); ∀ N : ℕ, 2*(((C N).filter (fun p => Nat.Prime (N-p))).card:ℝ) = ((C N).card:ℝ) - (C N).sum (fun p => (ArithmeticFunction.liouville (N-p) : ℝ)) - 2*(((C N).filter (fun p => ArithmeticFunction.cardFactors (N-p) = 3)).card:ℝ) := by
  intro C N
  have hP : (((C N).filter (fun p => Nat.Prime (N-p))).card:ℝ) = ∑ p ∈ C N, (if Nat.Prime (N-p) then (1:ℝ) else 0) := Finset.natCast_card_filter _ _
  have hT : (((C N).filter (fun p => ArithmeticFunction.cardFactors (N-p) = 3)).card:ℝ) = ∑ p ∈ C N, (if ArithmeticFunction.cardFactors (N-p) = 3 then (1:ℝ) else 0) := Finset.natCast_card_filter _ _
  have hM : ((C N).card:ℝ) = ∑ p ∈ C N, (1:ℝ) := by simp
  rw [hP, hT, hM, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [C, Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨hpN, hpp, _, _, h1, hq⟩ := hp
  have := rfb_pointwise N (N-p) (by omega) (by have := hpp.pos; omega) hq
  exact this

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr

private lemma conv_abs_bound (x q c : ℕ) (a b : ℕ → ℝ) :
    ∑ s ∈ (Finset.range (2*x+1)).filter (fun s => s % q = c),
      ∑ k ∈ (Finset.range (x+1)).filter (fun k => k ≤ s ∧ s-k ≤ x), |a k| * |b (s-k)|
      ≤ (∑ i ∈ Finset.range (x+1), |a i|) * (∑ j ∈ Finset.range (x+1), |b j|) := by
  simp only [Finset.sum_filter]
  have hh : ∀ s : ℕ, (if s % q = c then ∑ k ∈ Finset.range (x+1),
      (if k ≤ s ∧ s - k ≤ x then |a k| * |b (s-k)| else 0) else 0)
      = ∑ k ∈ Finset.range (x+1),
      (if s % q = c then (if k ≤ s ∧ s - k ≤ x then |a k| * |b (s-k)| else 0) else 0) := by
    intro s
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun s _ => hh s), Finset.sum_comm, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  simp only [← Finset.sum_filter]
  rw [Finset.filter_filter]
  set T := (Finset.filter (fun s => (s % q = c) ∧ (k ≤ s ∧ s - k ≤ x)) (Finset.range (2*x+1)))
  have hinj : Set.InjOn (fun s => s - k) (T : Set ℕ) := by
    intro s hs t ht hst
    simp only [T, Finset.mem_coe, Finset.mem_filter] at hs ht
    simp only at hst
    omega
  rw [← Finset.mul_sum]
  have : ∑ s ∈ T, |b (s-k)| = ∑ j ∈ T.image (fun s => s - k), |b j| :=
    (Finset.sum_image (f := fun j => |b j|) hinj).symm
  rw [this]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    simp only [Finset.mem_image, T, Finset.mem_filter] at hj
    obtain ⟨s, ⟨_, _, _, h⟩, rfl⟩ := hj
    simp only [Finset.mem_range]
    omega
  · intros; exact abs_nonneg _

theorem PEqualNP.Outside.L_goldbach_residual_test_approximation :
    let C := fun (x : ℕ) (a b : ℕ → ℝ) s => ∑ k ∈ (Finset.range (x+1)).filter (fun k => k ≤ s ∧ s-k ≤ x), a k*b (s-k); ∀ (x q c : ℕ) (a b g p : ℕ → ℝ) (δ : ℝ), let S := (Finset.range (2*x+1)).filter (fun s => s % q=c); (∀ s ∈ S, |g s-p s|≤δ) → 0≤δ → (∑ s ∈ S, p s*C x a b s)=0 → |∑ s ∈ S, g s*C x a b s| ≤ δ*(∑ i ∈ Finset.range (x+1), |a i|)*(∑ j ∈ Finset.range (x+1), |b j|) := by
  intro C x q c a b g p δ S h hδ hp
  have hS : S = (Finset.range (2*x+1)).filter (fun s => s % q = c) := rfl
  have e1 : ∑ s ∈ S, g s * C x a b s = ∑ s ∈ S, (g s - p s) * C x a b s := by
    have : ∑ s ∈ S, (g s - p s) * C x a b s
        = ∑ s ∈ S, g s * C x a b s - ∑ s ∈ S, p s * C x a b s := by
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intros; ring
    rw [this, hp, sub_zero]
  rw [e1]
  have hC : ∀ s, |C x a b s| ≤
      ∑ k ∈ (Finset.range (x+1)).filter (fun k => k ≤ s ∧ s-k ≤ x), |a k| * |b (s-k)| := by
    intro s
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply le_of_eq; apply Finset.sum_congr rfl; intros; rw [abs_mul]
  calc |∑ s ∈ S, (g s - p s) * C x a b s|
      ≤ ∑ s ∈ S, |(g s - p s) * C x a b s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ S, δ * ∑ k ∈ (Finset.range (x+1)).filter (fun k => k ≤ s ∧ s-k ≤ x), |a k| * |b (s-k)| := by
        apply Finset.sum_le_sum
        intro s hs
        rw [abs_mul]
        exact mul_le_mul (h s hs) (hC s) (abs_nonneg _) hδ
    _ = δ * ∑ s ∈ S, ∑ k ∈ (Finset.range (x+1)).filter (fun k => k ≤ s ∧ s-k ≤ x), |a k| * |b (s-k)| := by
        rw [Finset.mul_sum]
    _ ≤ δ * ((∑ i ∈ Finset.range (x+1), |a i|) * (∑ j ∈ Finset.range (x+1), |b j|)) := by
        rw [hS]
        exact mul_le_mul_of_nonneg_left (conv_abs_bound x q c a b) hδ
    _ = _ := by ring

import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

private lemma abel_aux (a g : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, (a k - a (k-1)) * g k)
      = a n * g n - a 0 * g 0 - ∑ k ∈ Finset.range n, a k * (g (k+1) - g k) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel]
    ring

theorem PEqualNP.Outside.L_goldbach_diagonal_abel_error :
    let p := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let θ := fun n : ℕ => ∑ k ∈ Finset.range (n+1), p k; let g := fun (φ : ℝ → ℝ) (n k : ℕ) => Real.log (k:ℝ)*(φ ((k:ℝ)/n))^2; ∀ (φ : ℝ → ℝ) (n : ℕ), 1≤n → (∀ u : ℝ, u < 1/3 ∨ 2/3 < u → φ u=0) → (∑ k ∈ Finset.Icc 1 n, (p k-1)*g φ n k) = - ∑ k ∈ Finset.range n, (θ k-(k:ℝ))*(g φ n (k+1)-g φ n k) := by
  intro p θ g φ n hn hφ
  have hstep : ∀ k ∈ Finset.Icc 1 n, (p k - 1) * g φ n k
      = ((θ k - (k:ℝ)) - (θ (k-1) - ((k-1 : ℕ):ℝ))) * g φ n k := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k-1, by omega⟩
    simp only [θ, Nat.add_sub_cancel, Finset.sum_range_succ _ (j+1)]
    push_cast
    ring
  rw [Finset.sum_congr rfl hstep, abel_aux (fun k => θ k - (k:ℝ)) (g φ n) n]
  have h0 : θ 0 - ((0:ℕ):ℝ) = 0 := by simp [θ, p, Nat.not_prime_zero]
  have h1 : g φ n n = 0 := by
    have : φ ((n:ℝ)/n) = 0 := by
      apply hφ; right
      have : (n:ℝ)/n = 1 := div_self (by positivity)
      rw [this]; norm_num
    simp only [g, this]; simp
  simp only [h0, h1]
  ring

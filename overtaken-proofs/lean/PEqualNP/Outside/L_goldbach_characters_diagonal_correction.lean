import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic

theorem PEqualNP.Outside.L_goldbach_characters_diagonal_correction :
    ∀ (n : ℕ) [NeZero n], 2<n → ∀ w : ℕ → ℝ, (∑ a : (ZMod n)ˣ, w (a : ZMod n).val * w ((-a : (ZMod n)ˣ) : ZMod n).val) = ∑ k ∈ (Finset.range n).filter (fun k => k.Coprime n), w k*w (n-k) := by
  intro n _ hn w
  have hneg : ∀ a : (ZMod n)ˣ, (((-a : (ZMod n)ˣ) : ZMod n)).val = n - (a : ZMod n).val := by
    intro a
    rw [Units.val_neg, ZMod.neg_val]
    have : (a : ZMod n) ≠ 0 := by
      intro h
      have h1 := a.isUnit
      rw [h] at h1
      have := (isUnit_zero_iff.mp h1)
      have h2 : (1 : ZMod n) = 0 := this.symm
      have : n ∣ 1 := (ZMod.natCast_eq_zero_iff 1 n).mp (by simpa using h2)
      have := Nat.le_of_dvd one_pos this
      omega
    simp [this]
  simp_rw [hneg]
  refine Finset.sum_bij (fun a _ => (a : ZMod n).val) ?_ ?_ ?_ ?_
  · intro a _
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨ZMod.val_lt _, ZMod.val_coe_unit_coprime a⟩
  · intro a _ b _ h
    exact Units.ext (ZMod.val_injective n h)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    refine ⟨ZMod.unitOfCoprime k hk.2, Finset.mem_univ _, ?_⟩
    simp [ZMod.val_natCast_of_lt hk.1]
  · intro a _
    rfl

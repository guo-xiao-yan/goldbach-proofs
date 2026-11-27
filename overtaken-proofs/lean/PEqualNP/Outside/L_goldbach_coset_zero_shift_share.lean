import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Nat

private theorem zss_set (n q : ℕ) (hq : 0 < q) :
    ((Finset.range (2*n+1)).filter (fun s => s % q = n % q)).erase n =
      (Finset.Icc 1 (n/q)).image (fun h => n - h*q) ∪ (Finset.Icc 1 (n/q)).image (fun h => n + h*q) := by
  ext s
  simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_range, Finset.mem_union,
    Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨hne, hs, hmod⟩
    rcases lt_or_gt_of_ne hne with h | h
    · left
      have hd : q ∣ n - s := (Nat.modEq_iff_dvd' h.le).1 hmod
      obtain ⟨h0, hh⟩ := hd
      have hpos : 1 ≤ h0 := by
        rcases Nat.eq_zero_or_pos h0 with e | e
        · subst e; simp at hh; omega
        · exact e
      refine ⟨h0, ⟨hpos, ?_⟩, ?_⟩
      · rw [Nat.le_div_iff_mul_le hq]
        have : h0 * q = n - s := by rw [hh]; ring
        omega
      · have : h0 * q = n - s := by rw [hh]; ring
        omega
    · right
      have hd : q ∣ s - n := (Nat.modEq_iff_dvd' h.le).1 hmod.symm
      obtain ⟨h0, hh⟩ := hd
      have hpos : 1 ≤ h0 := by
        rcases Nat.eq_zero_or_pos h0 with e | e
        · subst e; simp at hh; omega
        · exact e
      have : h0 * q = s - n := by rw [hh]; ring
      refine ⟨h0, ⟨hpos, ?_⟩, ?_⟩
      · rw [Nat.le_div_iff_mul_le hq]
        omega
      · omega
  · rintro (⟨h0, ⟨h1, h2⟩, rfl⟩ | ⟨h0, ⟨h1, h2⟩, rfl⟩)
    · rw [Nat.le_div_iff_mul_le hq] at h2
      have : 1 * q ≤ h0 * q := Nat.mul_le_mul_right q h1
      refine ⟨by omega, by omega, ?_⟩
      have e : n = (n - h0 * q) + h0 * q := by omega
      conv_rhs => rw [e]
      rw [Nat.add_mul_mod_self_right]
    · rw [Nat.le_div_iff_mul_le hq] at h2
      have : 1 * q ≤ h0 * q := Nat.mul_le_mul_right q h1
      refine ⟨by omega, by omega, ?_⟩
      rw [Nat.add_mul_mod_self_right]

theorem PEqualNP.Outside.L_goldbach_coset_zero_shift_share :
    let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let B := fun n s : ℕ => ∑ k ∈ (Finset.range (n+1)).filter (fun k => k ≤ s ∧ s-k ≤ n), w k*w (s-k); let Z := fun n q : ℕ => ∑ s ∈ (Finset.range (2*n+1)).filter (fun s => s % q=n % q), B n s; ∀ n q : ℕ, 0<q → Z n q-B n n = (∑ h ∈ Finset.Icc 1 (n/q), (B n (n-h*q)+B n (n+h*q))) := by
  intro w B Z n q hq
  have hn : n ∈ (Finset.range (2*n+1)).filter (fun s => s % q = n % q) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, trivial⟩
  show (∑ s ∈ (Finset.range (2*n+1)).filter (fun s => s % q = n % q), B n s) - B n n = _
  rw [← Finset.add_sum_erase _ _ hn, zss_set n q hq, add_sub_cancel_left,
    Finset.sum_union, Finset.sum_image, Finset.sum_image, Finset.sum_add_distrib]
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_Icc, Nat.le_div_iff_mul_le hq] at ha hb
    have : a * q = b * q := by simp only at hab; omega
    exact Nat.eq_of_mul_eq_mul_right hq this
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_Icc, Nat.le_div_iff_mul_le hq] at ha hb
    have : a * q = b * q := by simp only at hab; omega
    exact Nat.eq_of_mul_eq_mul_right hq this
  · rw [Finset.disjoint_left]
    intro s h1 h2
    simp only [Finset.mem_image, Finset.mem_Icc, Nat.le_div_iff_mul_le hq] at h1 h2
    obtain ⟨a, ⟨ha1, ha2⟩, rfl⟩ := h1
    obtain ⟨b, ⟨hb1, hb2⟩, hb⟩ := h2
    have : 1 * q ≤ b * q := Nat.mul_le_mul_right q hb1
    omega

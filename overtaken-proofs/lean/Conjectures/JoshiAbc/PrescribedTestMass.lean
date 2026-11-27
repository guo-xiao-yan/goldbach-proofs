import Mathlib

open ZMod in
private theorem orth (N : ℕ) [NeZero N] (d : ZMod N) :
    ∑ k : ZMod N, stdAddChar (d * k) = if d = 0 then (N:ℂ) else 0 := by
  have h := AddChar.sum_eq_ite (AddChar.mulShift (stdAddChar : AddChar (ZMod N) ℂ) d)
  simp only [AddChar.mulShift_apply] at h
  rw [h]
  by_cases hd : d = 0
  · subst hd; simp [AddChar.ext_iff]
  · have : AddChar.mulShift (stdAddChar : AddChar (ZMod N) ℂ) d ≠ 0 := by
      intro h0
      have h1 := DFunLike.congr_fun h0 1
      apply hd
      apply injective_stdAddChar
      simpa using h1
    simp [this, hd]

theorem Conjectures.JoshiAbc.PrescribedTestMass :
    ∀ (N : ℕ) [NeZero N] (S : Finset (ZMod N)), let u := fun x : ZMod N => if x ∈ S then (1:ℂ) else 0; (∑ k : ZMod N, ‖ZMod.dft u k‖^2)/(N:ℝ)^2 = (S.card:ℝ)/N := by
  intro N _ S u
  have hN : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hu : ∀ i, (starRingEnd ℂ) (u i) = u i := by
    intro i; simp only [u]; split_ifs <;> simp
  have e2 : ∀ k : ZMod N, ((‖ZMod.dft u k‖^2 : ℝ) : ℂ) =
      ∑ j, ∑ i, u j * u i * ZMod.stdAddChar ((i - j) * k) := by
    intro k
    have e1 : ((‖ZMod.dft u k‖^2 : ℝ) : ℂ) = ZMod.dft u k * (starRingEnd ℂ) (ZMod.dft u k) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [e1, ZMod.dft_apply, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [smul_eq_mul, map_mul (starRingEnd ℂ), hu]
    rw [← AddChar.map_neg_eq_conj, neg_neg]
    have h3 : (i - j) * k = i * k + -(j * k) := by ring
    rw [h3, AddChar.map_add_eq_mul]
    ring
  have key : ∑ k : ZMod N, ((‖ZMod.dft u k‖^2 : ℝ) : ℂ) = (N:ℂ) * (S.card : ℂ) := by
    simp_rw [e2]
    calc ∑ k : ZMod N, ∑ j, ∑ i, u j * u i * ZMod.stdAddChar ((i - j) * k)
        = ∑ j, ∑ i, ∑ k : ZMod N, u j * u i * ZMod.stdAddChar ((i - j) * k) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = (N:ℂ) * (S.card : ℂ) := by
          simp_rw [← Finset.mul_sum, orth, sub_eq_zero]
          simp [u, Finset.sum_ite_eq', mul_comm, Finset.sum_ite_mem]
  have key' : ∑ k : ZMod N, ‖ZMod.dft u k‖^2 = (N:ℝ) * S.card := by exact_mod_cast key
  rw [key']
  field_simp

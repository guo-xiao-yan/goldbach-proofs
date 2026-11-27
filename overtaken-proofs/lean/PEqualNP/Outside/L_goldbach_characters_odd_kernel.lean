import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.Complex

private instance gb_hero (e : ℕ) [NeZero e] : HasEnoughRootsOfUnity ℂ e :=
  ⟨⟨Complex.exp (2 * Real.pi * Complex.I / e), Complex.isPrimitiveRoot_exp e (NeZero.ne e)⟩,
    rootsOfUnity.isCyclic ℂ e⟩

private theorem gb_sign (n : ℕ) (χ : DirichletCharacter ℂ n) : χ (-1) = 1 ∨ χ (-1) = -1 := by
  have h : χ (-1) * χ (-1) = 1 := by
    rw [← map_mul]; simp
  exact mul_self_eq_one_iff.mp h

theorem PEqualNP.Outside.L_goldbach_characters_odd_kernel :
    ∀ (n : ℕ) [NeZero n], 2<n → let odd := (Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1); ∀ a b : (ZMod n)ˣ, ((2:ℂ)/(n.totient:ℂ))* (∑ χ ∈ odd, χ ((↑a : ZMod n)⁻¹)*χ (↑b : ZMod n)) = (if a=b then 1 else 0) - (if (↑a : ZMod n) = -(↑b : ZMod n) then 1 else 0) := by
  intro n _ hn odd a b
  have hφ : (n.totient : ℂ) ≠ 0 := by
    have : 0 < n.totient := Nat.totient_pos.mpr (by omega)
    exact_mod_cast this.ne'
  have hA := DirichletCharacter.sum_char_inv_mul_char_eq ℂ (n := n) a.isUnit (↑b : ZMod n)
  have hB := DirichletCharacter.sum_char_inv_mul_char_eq ℂ (n := n) a.isUnit (-(↑b : ZMod n))
  have hB' : ∑ χ : DirichletCharacter ℂ n, χ (-1) * (χ ((↑a : ZMod n)⁻¹) * χ (↑b : ZMod n))
      = if (↑a : ZMod n) = -(↑b : ZMod n) then (n.totient : ℂ) else 0 := by
    rw [← hB]
    refine Finset.sum_congr rfl fun χ _ => ?_
    have e1 : -(↑b : ZMod n) = (-1) * ↑b := by ring
    rw [e1, map_mul]
    ring
  have hodd : ∑ χ ∈ odd, χ ((↑a : ZMod n)⁻¹) * χ (↑b : ZMod n)
      = ∑ χ : DirichletCharacter ℂ n, ((1 - χ (-1)) / 2) * (χ ((↑a : ZMod n)⁻¹) * χ (↑b : ZMod n)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rcases gb_sign n χ with h | h
    · rw [h]; norm_num
    · rw [h]; norm_num <;> ring
  have hab : ((↑a : ZMod n) = ↑b) ↔ a = b := Units.val_inj
  rw [hodd]
  have e : ∑ χ : DirichletCharacter ℂ n, ((1 - χ (-1)) / 2) * (χ ((↑a : ZMod n)⁻¹) * χ (↑b : ZMod n))
      = (∑ χ : DirichletCharacter ℂ n, χ ((↑a : ZMod n)⁻¹) * χ (↑b : ZMod n)
        - ∑ χ : DirichletCharacter ℂ n, χ (-1) * (χ ((↑a : ZMod n)⁻¹) * χ (↑b : ZMod n))) / 2 := by
    rw [← Finset.sum_sub_distrib, div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun χ _ => ?_
    ring
  rw [e, hA, hB']
  by_cases h1 : a = b <;> by_cases h2 : (↑a : ZMod n) = -(↑b : ZMod n)
  · have h1' : (↑a : ZMod n) = ↑b := congrArg _ h1
    simp only [if_pos h1, if_pos h1', if_pos h2]
    field_simp
  · have h1' : (↑a : ZMod n) = ↑b := congrArg _ h1
    simp only [if_pos h1, if_pos h1', if_neg h2]
    field_simp
    ring
  · have h1' : ¬ (↑a : ZMod n) = ↑b := fun h => h1 (hab.mp h)
    simp only [if_neg h1, if_neg h1', if_pos h2]
    field_simp
    ring
  · have h1' : ¬ (↑a : ZMod n) = ↑b := fun h => h1 (hab.mp h)
    simp only [if_neg h1, if_neg h1', if_neg h2]
    field_simp
    ring

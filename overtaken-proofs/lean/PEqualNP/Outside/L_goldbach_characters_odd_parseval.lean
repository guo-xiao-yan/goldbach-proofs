import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Totient
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

theorem PEqualNP.Outside.L_goldbach_characters_odd_parseval :
    ∀ (n : ℕ) [NeZero n], 2<n → let odd := (Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1); ∀ f : (ZMod n)ˣ → ℝ, (2/(n.totient : ℝ))*(∑ χ ∈ odd, ‖∑ a : (ZMod n)ˣ, (f a : ℂ)*χ (a : ZMod n)‖^2) = (∑ a : (ZMod n)ˣ, (f a)^2) - ∑ a : (ZMod n)ˣ, f a*f (-a) := by
  intro n _ hn odd f
  have : HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod n)ˣ) :=
    ⟨⟨_, Complex.isPrimitiveRoot_exp _ (Monoid.exponent_ne_zero_of_finite)⟩, rootsOfUnity.isCyclic ℂ _⟩
  have hφpos : 0 < n.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hφ : (n.totient : ℂ) ≠ 0 := by exact_mod_cast hφpos.ne'
  have hT : ∀ u : (ZMod n)ˣ, ∑ χ : DirichletCharacter ℂ n, χ (u : ZMod n)
      = if u = 1 then (n.totient : ℂ) else 0 := by
    intro u
    rw [DirichletCharacter.sum_characters_eq]
    simp only [Units.val_eq_one]
  have hconj : ∀ (χ : DirichletCharacter ℂ n) (b : (ZMod n)ˣ),
      (starRingEnd ℂ) (χ (b : ZMod n)) = χ ((b⁻¹ : (ZMod n)ˣ) : ZMod n) := by
    intro χ b
    have h1 : (starRingEnd ℂ) (χ (b : ZMod n)) = χ⁻¹ (b : ZMod n) := MulChar.star_apply' χ _
    rw [h1, MulChar.inv_apply_eq_inv']
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
  have hsq : ∀ χ : DirichletCharacter ℂ n,
      ((‖∑ a : (ZMod n)ˣ, (f a : ℂ) * χ (a : ZMod n)‖ ^ 2 : ℝ) : ℂ)
        = ∑ a, ∑ b, (f a : ℂ) * f b * χ ((a * b⁻¹ : (ZMod n)ˣ) : ZMod n) := by
    intro χ
    push_cast
    rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, Complex.conj_ofReal, hconj, map_mul]
    ring
  have hind : ∀ χ : DirichletCharacter ℂ n,
      (if χ (-1) = -1 then (1 : ℂ) else 0) = (1 - χ (-1)) / 2 := by
    intro χ
    have h2 : χ (-1) * χ (-1) = 1 := by
      rw [← map_mul]; simp
    have h3 : (χ (-1) - 1) * (χ (-1) + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp h3 with h | h
    · have : χ (-1) = 1 := by linear_combination h
      rw [this]; norm_num
    · have : χ (-1) = -1 := by linear_combination h
      rw [this]; norm_num
  have hodd : ∀ g : DirichletCharacter ℂ n → ℂ,
      ∑ χ ∈ odd, g χ = ∑ χ, (1 - χ (-1)) / 2 * g χ := by
    intro g
    show ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ n => χ (-1) = -1), g χ = _
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [← hind]
    split_ifs <;> simp
  have hmain : ((∑ χ ∈ odd, ‖∑ a : (ZMod n)ˣ, (f a : ℂ) * χ (a : ZMod n)‖ ^ 2 : ℝ) : ℂ)
      = (n.totient : ℂ) / 2 * (((∑ a : (ZMod n)ˣ, (f a) ^ 2 : ℝ) : ℂ)
        - ((∑ a : (ZMod n)ˣ, f a * f (-a) : ℝ) : ℂ)) := by
    rw [Complex.ofReal_sum]
    simp only [hsq]
    rw [hodd]
    have hstep : ∀ χ : DirichletCharacter ℂ n,
        (1 - χ (-1)) / 2 * ∑ a : (ZMod n)ˣ, ∑ b : (ZMod n)ˣ, (f a : ℂ) * f b * χ ((a * b⁻¹ : (ZMod n)ˣ) : ZMod n)
        = ∑ a : (ZMod n)ˣ, ∑ b : (ZMod n)ˣ, (f a : ℂ) * f b / 2 *
            (χ ((a * b⁻¹ : (ZMod n)ˣ) : ZMod n) - χ ((-(a * b⁻¹) : (ZMod n)ˣ) : ZMod n)) := by
      intro χ
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      have : χ ((-(a * b⁻¹) : (ZMod n)ˣ) : ZMod n) = χ (-1) * χ ((a * b⁻¹ : (ZMod n)ˣ) : ZMod n) := by
        rw [← map_mul, Units.val_neg]; congr 1; ring
      rw [this]; ring
    simp only [hstep]
    have hswap : ∀ G : DirichletCharacter ℂ n → (ZMod n)ˣ → (ZMod n)ˣ → ℂ,
        ∑ χ, ∑ a, ∑ b, G χ a b = ∑ a, ∑ b, ∑ χ, G χ a b := by
      intro G
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    rw [hswap]
    have hper : ∀ a b : (ZMod n)ˣ, (∑ χ : DirichletCharacter ℂ n, (f a : ℂ) * f b / 2 *
        (χ ((a * b⁻¹ : (ZMod n)ˣ) : ZMod n) - χ ((-(a * b⁻¹) : (ZMod n)ˣ) : ZMod n)))
        = (if a = b then (f a : ℂ) * f b / 2 * n.totient else 0)
          - (if -a = b then (f a : ℂ) * f b / 2 * n.totient else 0) := by
      intro a b
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, hT, hT]
      have e1 : (a * b⁻¹ = 1) = (a = b) := propext mul_inv_eq_one
      have e2 : (-(a * b⁻¹) = 1) = (-a = b) := by
        rw [← neg_mul]; exact propext mul_inv_eq_one
      simp only [e1, e2]
      split_ifs <;> ring
    simp only [hper]
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_sub_distrib (s := Finset.univ) _ _]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    push_cast
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  apply Complex.ofReal_injective
  have h1 := hmain
  push_cast at h1 ⊢
  rw [h1]
  field_simp

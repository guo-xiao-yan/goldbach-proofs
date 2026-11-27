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

theorem PEqualNP.Outside.L_goldbach_characters_odd_card :
    ∀ (n : ℕ) [NeZero n], 2<n → let odd := (Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1); 2*odd.card=n.totient := by
  intro n _ hn odd
  have hne : (-1 : ZMod n) ≠ 1 := by
    intro h
    have h2 : ((2 : ℕ) : ZMod n) = 0 := by
      have : (1 : ZMod n) + 1 = 0 := neg_eq_iff_add_eq_zero.mp h
      simpa [one_add_one_eq_two] using this
    have := (ZMod.natCast_eq_zero_iff 2 n).mp h2
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hs := DirichletCharacter.sum_characters_eq ℂ (n := n) (-1)
  simp only [hne, ↓reduceIte] at hs
  have hcard : (Finset.univ : Finset (DirichletCharacter ℂ n)).card = n.totient := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ n
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (DirichletCharacter ℂ n))
    (fun χ => χ (-1) = -1) (fun χ => χ (-1))
  have h1 : ∑ χ ∈ odd, χ (-1) = -(odd.card : ℂ) := by
    rw [Finset.sum_congr rfl (g := fun _ => (-1 : ℂ))]
    · simp
    · intro χ hχ; exact (Finset.mem_filter.mp hχ).2
  have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (DirichletCharacter ℂ n)))
    (fun χ : DirichletCharacter ℂ n => χ (-1) = -1)
  have h2 : ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => ¬ χ (-1) = -1), χ (-1)
      = (((Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => ¬ χ (-1) = -1)).card : ℂ) := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℂ))]
    · simp
    · intro χ hχ
      rcases gb_sign n χ with h | h
      · exact h
      · exact absurd h (Finset.mem_filter.mp hχ).2
  change ∑ χ ∈ odd, χ (-1) + _ = _ at hsplit
  rw [hs, h1, h2] at hsplit
  have hnat : odd.card = ((Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => ¬ χ (-1) = -1)).card := by
    have : (odd.card : ℂ) = (((Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => ¬ χ (-1) = -1)).card : ℂ) := by linear_combination -hsplit
    exact_mod_cast this
  change odd.card + _ = _ at hc
  omega

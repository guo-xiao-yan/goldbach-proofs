import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Totient

private theorem gb_odd_card (d : ℕ) [NeZero d] (hd : 2 < d) :
    2 * ((Finset.univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ (-1) = -1)).card
      = d.totient := by
  have : Fact (2 < d) := ⟨hd⟩
  have hexp : NeZero (Monoid.exponent (ZMod d)ˣ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have : HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod d)ˣ) :=
    ⟨⟨_, Complex.isPrimitiveRoot_exp _ (NeZero.ne _)⟩, rootsOfUnity.isCyclic _ _⟩
  have hne : (-1 : ZMod d) ≠ 1 := ZMod.neg_one_ne_one
  have hsum := DirichletCharacter.sum_characters_eq_zero ℂ hne
  have htot : Fintype.card (DirichletCharacter ℂ d) = d.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ d
  set odd := (Finset.univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ (-1) = -1) with hodd
  have hcard : odd.card + (Finset.univ.filter (fun χ : DirichletCharacter ℂ d => ¬ χ (-1) = -1)).card
      = d.totient := by
    rw [hodd, Finset.card_filter_add_card_filter_not, Finset.card_univ, htot]
  have h1 : ∑ χ ∈ odd, χ (-1) = -(odd.card : ℂ) := by
    rw [Finset.sum_congr rfl (g := fun _ => (-1 : ℂ))]
    · simp
    · intro χ hχ
      exact (Finset.mem_filter.1 hχ).2
  have h2 : ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ d => ¬ χ (-1) = -1), χ (-1)
      = ((Finset.univ.filter (fun χ : DirichletCharacter ℂ d => ¬ χ (-1) = -1)).card : ℂ) := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℂ))]
    · simp
    · intro χ hχ
      have hn := (Finset.mem_filter.1 hχ).2
      rcases DirichletCharacter.even_or_odd χ with h | h
      · exact h
      · exact absurd h hn
  have h3 := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (DirichletCharacter ℂ d))
    (fun χ => χ (-1) = -1) (fun χ => χ (-1))
  rw [hsum, ← hodd, h1, h2] at h3
  have h4 : ((Finset.univ.filter (fun χ : DirichletCharacter ℂ d => ¬ χ (-1) = -1)).card : ℂ)
      = (odd.card : ℂ) := by linear_combination h3
  have h5 : (Finset.univ.filter (fun χ : DirichletCharacter ℂ d => ¬ χ (-1) = -1)).card
      = odd.card := by exact_mod_cast h4
  omega

private theorem gb_change_neg_one (d n : ℕ) [NeZero n] (hd : d ∣ n)
    (ψ : DirichletCharacter ℂ d) :
    DirichletCharacter.changeLevel hd ψ (-1) = ψ (-1) := by
  have := DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ hd (a := -1) (isCoprime_one_left.neg_left)
  simpa using this

theorem PEqualNP.Outside.L_goldbach_characters_low_conductor_card :
    ∀ (n : ℕ) [NeZero n], 2<n → let odd := (Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1); ∀ d : ℕ, d∣n → 2<d → 2*(odd.filter (fun χ => χ.conductor ∣ d)).card = d.totient := by
  intro n inst _ odd d hdn hd
  have : NeZero d := ⟨by omega⟩
  rw [← gb_odd_card d hd]
  congr 1
  symm
  apply Finset.card_bij (fun ψ _ => DirichletCharacter.changeLevel hdn ψ)
  · intro ψ hψ
    have hψ' := (Finset.mem_filter.1 hψ).2
    simp only [odd, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_⟩
    · rw [gb_change_neg_one]; exact hψ'
    · apply DirichletCharacter.conductor_dvd_of_mem_conductorSet
      exact DirichletCharacter.changeLevel_factorsThrough ψ hdn
  · intro a _ b _ h
    exact DirichletCharacter.changeLevel_injective hdn h
  · intro χ hχ
    simp only [odd, Finset.mem_filter, Finset.mem_univ, true_and] at hχ
    obtain ⟨h1, h2⟩ := hχ
    have hft : DirichletCharacter.FactorsThrough χ d :=
      DirichletCharacter.FactorsThrough.mono χ (DirichletCharacter.factorsThrough_conductor χ) h2 hdn
    obtain ⟨_, ψ, hψ⟩ := hft
    refine ⟨ψ, ?_, hψ.symm⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← gb_change_neg_one d n hdn ψ, ← hψ]
    exact h1

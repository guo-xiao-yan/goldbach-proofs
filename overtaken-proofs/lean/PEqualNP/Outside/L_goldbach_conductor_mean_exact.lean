import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Totient

private theorem gb_layer_filter (n c p : ℕ) (hn : n ≠ 0) (hc : c ∣ n) (hp : p.Prime) :
    (Finset.Icc 1 (n.factorization p)).filter (fun j => c ∣ n / p ^ j) =
      Finset.Icc 1 (n.factorization p - c.factorization p) := by
  have hc0 : c ≠ 0 := fun h => hn (by simpa [h] using hc)
  have hle : c.factorization ≤ n.factorization := (Nat.factorization_le_iff_dvd hc0 hn).2 hc
  have hlep : c.factorization p ≤ n.factorization p := hle p
  ext j
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have hpj : p ^ j ∣ n := (hp.pow_dvd_iff_le_factorization hn).2 h2
    have hne : n / p ^ j ≠ 0 := by
      have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpj) (pow_pos hp.pos j)
      omega
    have := (Nat.factorization_le_iff_dvd hc0 hne).2 h3 p
    rw [Nat.factorization_div hpj, hp.factorization_pow] at this
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same] at this
    omega
  · rintro ⟨h1, h2⟩
    have h2' : j ≤ n.factorization p := by omega
    refine ⟨⟨h1, h2'⟩, ?_⟩
    have hpj : p ^ j ∣ n := (hp.pow_dvd_iff_le_factorization hn).2 h2'
    have hne : n / p ^ j ≠ 0 := by
      have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpj) (pow_pos hp.pos j)
      omega
    rw [← Nat.factorization_le_iff_dvd hc0 hne, Nat.factorization_div hpj, hp.factorization_pow]
    intro q
    simp only [Finsupp.tsub_apply]
    by_cases hq : q = p
    · subst hq
      simp only [Finsupp.single_eq_same]
      omega
    · have h0 : (Finsupp.single p j) q = 0 := by simp [Ne.symm hq]
      rw [h0]
      have := hle q
      omega

private theorem gb_deficit :
    ∀ (n : ℕ) [NeZero n], 2<n → ∀ χ : DirichletCharacter ℂ n, Real.log ((n:ℝ)/(χ.conductor:ℝ)) = ∑ p ∈ n.primeFactors, (Real.log (p:ℝ)) * (((Finset.Icc 1 (n.factorization p)).filter (fun j => χ.conductor ∣ n/p^j)).card : ℝ) := by
  intro n inst _ χ
  have hn : n ≠ 0 := NeZero.ne n
  have hcd : χ.conductor ∣ n := DirichletCharacter.conductor_dvd_level χ
  have hc0 : χ.conductor ≠ 0 := DirichletCharacter.conductor_ne_zero χ
  have hcast : ((n:ℝ)/(χ.conductor:ℝ)) = ((n / χ.conductor : ℕ) : ℝ) := by
    rw [Nat.cast_div hcd (by exact_mod_cast hc0)]
  rw [hcast, Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.factorization_div hcd]
  have hsupp : (n.factorization - χ.conductor.factorization).support ⊆ n.primeFactors := by
    intro p hp
    rw [← Nat.support_factorization]
    exact Finsupp.support_tsub hp |> fun h => by simpa using h
  rw [Finset.sum_subset hsupp]
  · apply Finset.sum_congr rfl
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    rw [gb_layer_filter n _ p hn hcd hpp, Nat.card_Icc]
    simp only [Finsupp.tsub_apply]
    push_cast [Nat.add_sub_cancel]
    ring_nf
  · intro p _ hp
    simp only [Finsupp.mem_support_iff, not_not] at hp
    simp [hp]

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

private theorem gb_lowcard :
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

private theorem gb_small (n d : ℕ) [NeZero n] (hdn : d ∣ n) (hd : d ≤ 2) (χ : DirichletCharacter ℂ n)
    (hc : χ.conductor ∣ d) : χ (-1) = 1 := by
  have hd0 : d ≠ 0 := fun h => (NeZero.ne n) (by simpa [h] using hdn)
  have hft : DirichletCharacter.FactorsThrough χ d :=
    DirichletCharacter.FactorsThrough.mono χ (DirichletCharacter.factorsThrough_conductor χ) hc hdn
  obtain ⟨_, ψ, hψ⟩ := hft
  have h1 : (-1 : ZMod d) = 1 := by
    have hd12 : d = 1 ∨ d = 2 := by omega
    rcases hd12 with rfl | rfl
    · exact Subsingleton.elim _ _
    · decide
  rw [hψ, gb_change_neg_one, h1, map_one]

private theorem gb_count (n : ℕ) [NeZero n] (h2 : 2 < n) (p j : ℕ) (hj : p ^ j ∣ n) :
    (2 / (n.totient : ℝ)) *
      ((((Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1)).filter
        (fun χ => χ.conductor ∣ n / p ^ j)).card : ℝ)
      = if 2 < n / p ^ j then ((n / p ^ j).totient : ℝ) / (n.totient : ℝ) else 0 := by
  have hdn : n / p ^ j ∣ n := Nat.div_dvd_of_dvd hj
  have htn : (n.totient : ℝ) ≠ 0 := by
    have := Nat.totient_pos.2 (show 0 < n by omega)
    positivity
  split_ifs with hd
  · have := gb_lowcard n h2 (n / p ^ j) hdn hd
    have h' : (2 : ℝ) * (((((Finset.univ : Finset (DirichletCharacter ℂ n)).filter
        (fun χ => χ (-1) = -1)).filter (fun χ => χ.conductor ∣ n / p ^ j)).card : ℕ) : ℝ)
        = ((n / p ^ j).totient : ℝ) := by exact_mod_cast this
    rw [div_mul_eq_mul_div, h', ]
  · have : (((Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1)).filter
        (fun χ => χ.conductor ∣ n / p ^ j)) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro χ hχ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ
      have := gb_small n (n / p ^ j) hdn (by omega) χ hχ.2
      rw [hχ.1] at this
      norm_num at this
    rw [this]
    simp

theorem PEqualNP.Outside.L_goldbach_conductor_mean_exact :
    ∀ (n : ℕ) [NeZero n], 2<n → Even n → let odd := (Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1); (2/(n.totient:ℝ))*(∑ χ ∈ odd, Real.log ((n:ℝ)/(χ.conductor:ℝ))) = ∑ p ∈ n.primeFactors, Real.log (p:ℝ) * ∑ j ∈ Finset.Icc 1 (n.factorization p), (if 2<n/p^j then ((n/p^j).totient:ℝ)/(n.totient:ℝ) else 0) := by
  intro n inst h2 _ odd
  have hn : n ≠ 0 := NeZero.ne n
  have key : ∀ p ∈ n.primeFactors, ∑ χ ∈ odd, Real.log (p:ℝ) *
      (((Finset.Icc 1 (n.factorization p)).filter (fun j => χ.conductor ∣ n/p^j)).card : ℝ)
      = Real.log (p:ℝ) * ∑ j ∈ Finset.Icc 1 (n.factorization p),
        (((odd.filter (fun χ => χ.conductor ∣ n / p ^ j)).card : ℕ) : ℝ) := by
    intro p _
    rw [← Finset.mul_sum]
    congr 1
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    exact Finset.sum_comm
  have hL : ∑ χ ∈ odd, Real.log ((n:ℝ)/(χ.conductor:ℝ)) = ∑ p ∈ n.primeFactors, Real.log (p:ℝ) *
      ∑ j ∈ Finset.Icc 1 (n.factorization p),
        (((odd.filter (fun χ => χ.conductor ∣ n / p ^ j)).card : ℕ) : ℝ) := by
    rw [Finset.sum_congr rfl (fun χ _ => gb_deficit n h2 χ), Finset.sum_comm]
    exact Finset.sum_congr rfl key
  rw [hL, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [mul_left_comm, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hj' := (Finset.mem_Icc.1 hj).2
  exact gb_count n h2 p j ((hpp.pow_dvd_iff_le_factorization hn).2 hj')

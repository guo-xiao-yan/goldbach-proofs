import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Data.Nat.Totient
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

private instance hero (e : ℕ) [NeZero e] : HasEnoughRootsOfUnity ℂ e :=
  ⟨⟨Complex.exp (2 * Real.pi * Complex.I / e), Complex.isPrimitiveRoot_exp e (NeZero.ne e)⟩,
    rootsOfUnity.isCyclic ℂ e⟩

private lemma sq_dich {m : ℕ} (χ : DirichletCharacter ℂ m) : χ (-1) = 1 ∨ χ (-1) = -1 := by
  have h : χ (-1) * χ (-1) = 1 := by
    rw [← map_mul]; simp
  exact mul_self_eq_one_iff.mp h

private lemma odd_card_gt (m : ℕ) [NeZero m] (hm : 2 < m) :
    2 * (Finset.univ.filter (fun χ : DirichletCharacter ℂ m => χ (-1) = -1)).card = m.totient := by
  have hne : (-1 : ZMod m) ≠ 1 := by
    intro h
    have h2 : ((2 : ℕ) : ZMod m) = 0 := by
      have : (1 : ZMod m) + 1 = 0 := by
        calc (1 : ZMod m) + 1 = 1 + (-1) := by rw [h]
          _ = 0 := by simp
      simpa [one_add_one_eq_two] using this
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hs := DirichletCharacter.sum_characters_eq_zero ℂ hne
  have htot := DirichletCharacter.sum_characters_eq (R := ℂ) (n := m) 1
  simp only [ite_true] at htot
  have hc : ∀ χ : DirichletCharacter ℂ m, χ (-1) = if χ (-1) = -1 then -1 else 1 := by
    intro χ
    rcases sq_dich χ with h | h
    · have : ¬ (χ (-1) = -1) := by
        rw [h]; intro h'
        have : (2:ℂ) = 0 := by linear_combination h'
        norm_num at this
      simp [h]
    · simp [h]
  have e1 : ∑ χ : DirichletCharacter ℂ m, χ (-1) =
      -((Finset.univ.filter (fun χ : DirichletCharacter ℂ m => χ (-1) = -1)).card : ℂ)
      + ((Finset.univ.filter (fun χ : DirichletCharacter ℂ m => ¬ χ (-1) = -1)).card : ℂ) := by
    rw [Finset.sum_congr rfl (fun χ _ => hc χ), Finset.sum_ite]
    simp
  have e2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (DirichletCharacter ℂ m))) (fun χ => χ (-1) = -1)
  have e3 : (Finset.univ : Finset (DirichletCharacter ℂ m)).card = m.totient := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ m
  rw [e1] at hs
  have hs' : ((Finset.univ.filter (fun χ : DirichletCharacter ℂ m => ¬ χ (-1) = -1)).card : ℂ)
      = (Finset.univ.filter (fun χ : DirichletCharacter ℂ m => χ (-1) = -1)).card := by
    linear_combination hs
  have hs'' := Nat.cast_injective (R := ℂ) hs'
  omega

private lemma odd_card_small (m : ℕ) [NeZero m] (hm : m ≤ 2) :
    (Finset.univ.filter (fun χ : DirichletCharacter ℂ m => χ (-1) = -1)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro χ _ h
  have h1 : (-1 : ZMod m) = 1 := by
    obtain rfl | rfl | rfl : m = 0 ∨ m = 1 ∨ m = 2 := by omega
    · exact absurd rfl (NeZero.ne 0)
    · exact Subsingleton.elim _ _
    · decide
  rw [h1, map_one] at h
  have : (2:ℂ) = 0 := by linear_combination h
  norm_num at this

private lemma change_card (n d : ℕ) [NeZero n] (hd : d ∣ n) :
    (Finset.univ.filter (fun χ : DirichletCharacter ℂ n => χ (-1) = -1 ∧ χ.conductor ∣ d)).card
      = (Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ (-1) = -1)).card := by
  have : NeZero d := ⟨fun h => NeZero.ne n (Nat.eq_zero_of_zero_dvd (h ▸ hd))⟩
  have key : ∀ ψ : DirichletCharacter ℂ d,
      DirichletCharacter.changeLevel hd ψ (-1) = ψ (-1) := by
    intro ψ
    have := DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ hd (a := -1) (isCoprime_one_left.neg_left)
    simpa using this
  symm
  apply Finset.card_bij (fun ψ _ => DirichletCharacter.changeLevel hd ψ)
  · intro ψ hψ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hψ ⊢
    refine ⟨by rw [key]; exact hψ, ?_⟩
    rw [DirichletCharacter.conductor_changeLevel]
    exact DirichletCharacter.conductor_dvd_level ψ
  · intro a _ b _ h
    exact DirichletCharacter.changeLevel_injective hd h
  · intro χ hχ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ
    obtain ⟨h1, h2⟩ := hχ
    have hm : d ∈ χ.conductorSet := by
      rw [DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ hd]; exact h2
    obtain ⟨_, ψ, hψ⟩ := hm
    refine ⟨ψ, ?_, hψ.symm⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hψ, key] at h1
    exact h1

private lemma odd_card_pow (i : ℕ) :
    (Finset.univ.filter (fun χ : DirichletCharacter ℂ (2^i) => χ (-1) = -1)).card
      = if 2 ≤ i then 2^(i-2) else 0 := by
  split_ifs with h
  · have h1 := odd_card_gt (2^i) (by
      calc 2 = 2^1 := by norm_num
        _ < 2^i := Nat.pow_lt_pow_right (by norm_num) (by omega))
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
    rw [Nat.totient_prime_pow Nat.prime_two (by omega)] at h1
    have e : 2 ^ (j + 2 - 1) * (2 - 1) = 2 * 2 ^ j := by
      rw [show j + 2 - 1 = j + 1 by omega]; ring
    simp only [Nat.add_sub_cancel]
    omega
  · apply odd_card_small
    have : i ≤ 1 := by omega
    calc 2 ^ i ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
      _ = 2 := by norm_num

private lemma cond_pow {k c : ℕ} (h : c ∣ 2^k) : ∃ i, i ≤ k ∧ c = 2^i := by
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h
  exact ⟨i, hi, rfl⟩

private lemma cnt (k i : ℕ) (hik : i ≤ k) :
    (Finset.univ.filter (fun χ : DirichletCharacter ℂ (2^k) =>
      χ (-1) = -1 ∧ χ.conductor ∣ 2^i)).card = if 2 ≤ i then 2^(i-2) else 0 := by
  rw [change_card (2^k) (2^i) (pow_dvd_pow 2 hik), odd_card_pow]

theorem PEqualNP.Outside.L_goldbach_characters_dyadic_low_fraction :
    ∀ k : ℕ, 4≤k → let n := 2^k; let X := (Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1); 2^(k/4)*(X.filter (fun χ => χ.conductor^4 ≤ n^3)).card ≤ X.card := by
  classical
  intro k hk n X
  show 2^(k/4) * ((Finset.univ.filter (fun χ : DirichletCharacter ℂ (2^k) => χ (-1) = -1)).filter
    (fun χ => χ.conductor^4 ≤ (2^k)^3)).card ≤
    (Finset.univ.filter (fun χ : DirichletCharacter ℂ (2^k) => χ (-1) = -1)).card
  rw [odd_card_pow k, Finset.filter_filter]
  have hj : 3 * k / 4 ≤ k := by omega
  have hc := cnt k (3 * k / 4) hj
  have hset : (Finset.univ.filter (fun χ : DirichletCharacter ℂ (2^k) =>
      χ (-1) = -1 ∧ χ.conductor^4 ≤ (2^k)^3)) =
      (Finset.univ.filter (fun χ : DirichletCharacter ℂ (2^k) =>
        χ (-1) = -1 ∧ χ.conductor ∣ 2^(3 * k / 4))) := by
    apply Finset.filter_congr
    intro χ _
    refine and_congr_right (fun _ => ?_)
    obtain ⟨i, hi, hci⟩ := cond_pow (DirichletCharacter.conductor_dvd_level χ)
    rw [hci, ← pow_mul, ← pow_mul, Nat.pow_dvd_pow_iff_le_right (by norm_num),
      Nat.pow_le_pow_iff_right (by norm_num)]
    omega
  rw [hset, hc]
  simp only [show 2 ≤ 3 * k / 4 by omega, show 2 ≤ k by omega, ↓reduceIte]
  rw [← pow_add]
  apply Nat.pow_le_pow_right (by norm_num)
  omega

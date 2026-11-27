import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

private lemma odd_card_aux (n : ℕ) [NeZero n] (hn : 2 < n) :
    2 * ((Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1)).card
      = n.totient := by
  have hz : NeZero (Monoid.exponent (ZMod n)ˣ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have hroots : HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod n)ˣ) :=
    ⟨⟨_, Complex.isPrimitiveRoot_exp _ hz.out⟩, inferInstance⟩
  have : Fact (2 < n) := ⟨hn⟩
  have hne : (-1 : ZMod n) ≠ 1 := ZMod.neg_one_ne_one
  have hsum := DirichletCharacter.sum_characters_eq ℂ (n := n) (-1)
  rw [ite_cond_eq_false _ _ (eq_false hne)] at hsum
  have hval : ∀ χ : DirichletCharacter ℂ n, χ (-1) = 1 ∨ χ (-1) = -1 := by
    intro χ
    have h : χ (-1) * χ (-1) = 1 := by
      rw [← map_mul]; simp
    have : (χ (-1) - 1) * (χ (-1) + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h1 | h1
    · left; linear_combination h1
    · right; linear_combination h1
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun χ : DirichletCharacter ℂ n => χ (-1) = -1) (fun χ => χ (-1))
  have h1 : ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1), χ (-1)
      = -((((Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1)).card : ℕ) : ℂ) := by
    rw [Finset.sum_congr rfl (g := fun _ => (-1 : ℂ)) (by intro χ hχ; exact (Finset.mem_filter.1 hχ).2)]
    simp
  have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (DirichletCharacter ℂ n))) (fun χ : DirichletCharacter ℂ n => χ (-1) = -1)
  have htot : (Finset.univ : Finset (DirichletCharacter ℂ n)).card = n.totient := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ n
  have h2 : ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => ¬ χ (-1) = -1), χ (-1)
      = (((Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => ¬ χ (-1) = -1)).card : ℂ) := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℂ))]
    · simp
    · intro χ hχ
      have := (Finset.mem_filter.1 hχ).2
      exact (hval χ).resolve_right this
  have hcC : ((((Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1)).card : ℕ) : ℂ)
      + (((Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => ¬ χ (-1) = -1)).card : ℂ) = (n.totient : ℂ) := by
    rw [← htot]; exact_mod_cast hc
  rw [h1, h2] at hsplit
  have hz2 : ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ n)), χ (-1) = 0 := hsum
  have hfin : (2 * (((Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1)).card : ℕ) : ℂ) = (n.totient : ℂ) := by
    linear_combination hcC - hsplit.trans hz2
  exact_mod_cast hfin

theorem PEqualNP.Outside.L_goldbach_primitive_mean_power_replacement :
    ∀ (n : ℕ) [NeZero n], 2<n → let X := (Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1); ∀ (A B : DirichletCharacter ℂ n → ℂ) (e : ℝ), 0≤e → (∀ χ∈X, ‖A χ-B χ‖ ≤ e) → let avg := fun f : DirichletCharacter ℂ n → ℝ => (2/(n.totient:ℝ))*∑ χ ∈ X, f χ; |avg (fun χ => ‖A χ‖^2)-avg (fun χ => ‖B χ‖^2)| ≤ 2*e*Real.sqrt (avg (fun χ => ‖B χ‖^2))+e^2 := by
  intro n _ hn X A B e he hAB avg
  have hcard : (2 * X.card : ℝ) = n.totient := by
    have h : 2 * X.card = n.totient := odd_card_aux n hn
    have h2 : ((2 * X.card : ℕ) : ℝ) = n.totient := by rw [h]
    push_cast at h2
    exact h2
  have hpos : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  set w : ℝ := 2 / (n.totient : ℝ) with hw
  have hw0 : 0 < w := by positivity
  have hwm : w * X.card = 1 := by
    rw [hw, ← hcard]
    have : (X.card : ℝ) ≠ 0 := by intro h; rw [h] at hcard; linarith
    field_simp
  have hterm : ∀ χ ∈ X, |‖A χ‖^2 - ‖B χ‖^2| ≤ 2 * e * ‖B χ‖ + e^2 := by
    intro χ hχ
    have h1 : |‖A χ‖ - ‖B χ‖| ≤ e := (abs_norm_sub_norm_le _ _).trans (hAB χ hχ)
    have h2 : ‖A χ‖^2 - ‖B χ‖^2 = (‖A χ‖ - ‖B χ‖)^2 + 2 * ‖B χ‖ * (‖A χ‖ - ‖B χ‖) := by ring
    rw [h2]
    have hb := norm_nonneg (B χ)
    have h3 : (‖A χ‖ - ‖B χ‖)^2 ≤ e^2 := by
      have := sq_le_sq' (abs_le.1 h1).1 (abs_le.1 h1).2
      nlinarith [this]
    calc |(‖A χ‖ - ‖B χ‖)^2 + 2 * ‖B χ‖ * (‖A χ‖ - ‖B χ‖)|
        ≤ |(‖A χ‖ - ‖B χ‖)^2| + |2 * ‖B χ‖ * (‖A χ‖ - ‖B χ‖)| := abs_add_le _ _
      _ ≤ e^2 + 2 * ‖B χ‖ * e := by
        rw [abs_of_nonneg (sq_nonneg _), abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * ‖B χ‖)]
        gcongr
      _ = 2 * e * ‖B χ‖ + e^2 := by ring
  have hdiff : |avg (fun χ => ‖A χ‖^2) - avg (fun χ => ‖B χ‖^2)|
      ≤ 2 * e * avg (fun χ => ‖B χ‖) + e^2 := by
    show |w * ∑ χ ∈ X, ‖A χ‖^2 - w * ∑ χ ∈ X, ‖B χ‖^2| ≤ 2 * e * (w * ∑ χ ∈ X, ‖B χ‖) + e^2
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos hw0]
    calc w * |∑ χ ∈ X, (‖A χ‖^2 - ‖B χ‖^2)|
        ≤ w * ∑ χ ∈ X, |‖A χ‖^2 - ‖B χ‖^2| := by gcongr; exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ w * ∑ χ ∈ X, (2 * e * ‖B χ‖ + e^2) := by gcongr with χ hχ; exact hterm χ hχ
      _ = 2 * e * (w * ∑ χ ∈ X, ‖B χ‖) + e^2 * (w * X.card) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp; ring
      _ = 2 * e * (w * ∑ χ ∈ X, ‖B χ‖) + e^2 := by rw [hwm]; ring
  have hcs : (∑ χ ∈ X, ‖B χ‖)^2 ≤ (X.card : ℝ) * ∑ χ ∈ X, ‖B χ‖^2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq X (fun _ => (1:ℝ)) (fun χ => ‖B χ‖)
    simpa using this
  have hsq : (avg (fun χ => ‖B χ‖))^2 ≤ avg (fun χ => ‖B χ‖^2) := by
    show (w * ∑ χ ∈ X, ‖B χ‖)^2 ≤ w * ∑ χ ∈ X, ‖B χ‖^2
    calc (w * ∑ χ ∈ X, ‖B χ‖)^2 = w^2 * (∑ χ ∈ X, ‖B χ‖)^2 := by ring
      _ ≤ w^2 * ((X.card : ℝ) * ∑ χ ∈ X, ‖B χ‖^2) := by gcongr
      _ = (w * X.card) * (w * ∑ χ ∈ X, ‖B χ‖^2) := by ring
      _ = w * ∑ χ ∈ X, ‖B χ‖^2 := by rw [hwm]; ring
  have hle : avg (fun χ => ‖B χ‖) ≤ Real.sqrt (avg (fun χ => ‖B χ‖^2)) :=
    (le_abs_self _).trans (Real.abs_le_sqrt hsq)
  calc _ ≤ 2 * e * avg (fun χ => ‖B χ‖) + e^2 := hdiff
    _ ≤ _ := by gcongr

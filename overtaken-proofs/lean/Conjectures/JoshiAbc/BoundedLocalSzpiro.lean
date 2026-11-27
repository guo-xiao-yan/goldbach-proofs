import Mathlib

private lemma szpiro_local (a b p : ℕ) (ha : 0 < a) (hb : 0 < b) (hp : p.Prime) (hodd : Odd p) :
    multiplicity p (16*a^2*b^2*(a+b)^2) = 2 * multiplicity p (a*b*(a+b)) := by
  have hn : a*b*(a+b) ≠ 0 := by positivity
  have hpp : Prime p := hp.prime
  have h16 : 16*a^2*b^2*(a+b)^2 = 16 * (a*b*(a+b))^2 := by ring
  have hfin : FiniteMultiplicity p (16 * (a*b*(a+b))^2) :=
    Nat.finiteMultiplicity_iff.mpr ⟨hp.ne_one, by positivity⟩
  have h0 : multiplicity p 16 = 0 := by
    apply multiplicity_eq_zero_of_not_dvd
    intro hd
    have : p ∣ 2 ^ 4 := by simpa using hd
    have := hp.dvd_of_dvd_pow this
    have h2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
    subst h2
    exact (Nat.not_even_iff_odd.mpr hodd) even_two
  rw [h16, multiplicity_mul hpp hfin, h0, multiplicity_pow hpp]
  ring

theorem Conjectures.JoshiAbc.BoundedLocalSzpiro :
    ∀ (a b M : ℕ) (S : Finset ℕ), 0<a → 0<b → Nat.Coprime a b → (∀ p ∈ S, p.Prime ∧ Odd p ∧ multiplicity p (a*b*(a+b)) ≤ M) → S.sum (fun p => (multiplicity p (16*a^2*b^2*(a+b)^2):ℝ)*Real.log p) ≤ 2*(M:ℝ)*S.sum (fun p => Real.log p) := by
  intro a b M S ha hb _ h
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hpS
  obtain ⟨hp, hodd, hM⟩ := h p hpS
  rw [szpiro_local a b p ha hb hp hodd]
  have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have : ((2 * multiplicity p (a*b*(a+b)) : ℕ) : ℝ) ≤ 2 * (M:ℝ) := by
    have : 2 * multiplicity p (a*b*(a+b)) ≤ 2 * M := by omega
    exact_mod_cast this
  nlinarith

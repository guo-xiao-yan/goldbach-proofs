import Mathlib

theorem Conjectures.JoshiAbc.FreyFixedPrime :
    ∀ p N : ℕ, p.Prime → Odd p → 0 < N → multiplicity p (16*(p^N)^2*(p^N+1)^2) = 2*N := by
  intro p N hp hodd hN
  haveI := Fact.mk hp
  have h1 : ¬ p ∣ 16 := by
    intro h
    have : p ∣ 2^4 := by norm_num; exact h
    have := hp.dvd_of_dvd_pow this
    have h2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this
    subst h2; exact absurd hodd (by decide)
  have h2 : ¬ p ∣ (p^N+1) := by
    intro h
    have : p ∣ p^N := dvd_pow_self p hN.ne'
    have : p ∣ 1 := (Nat.dvd_add_right this).1 h
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  have h3 : ¬ p ∣ (p^N+1)^2 := fun h => h2 (hp.dvd_of_dvd_pow h)
  have h16 : multiplicity p 16 = 0 := multiplicity_eq_zero_of_not_dvd h1
  have h4 : multiplicity p ((p^N+1)^2) = 0 := multiplicity_eq_zero_of_not_dvd h3
  have hp0 : 0 < p := hp.pos
  rw [multiplicity_mul hp.prime, multiplicity_mul hp.prime, h16, h4, multiplicity_pow hp.prime,
    multiplicity_pow hp.prime, Nat.multiplicity_self hp.one_lt]
  all_goals first | exact Nat.finiteMultiplicity_iff.2 ⟨hp.ne_one, by positivity⟩ | ring

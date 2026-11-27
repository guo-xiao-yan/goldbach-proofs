import Mathlib.Data.Nat.Prime.Basic

theorem PEqualNP.Outside.L_goldbach_pp_base_unique :
    ∀ p q a b : ℕ, p.Prime → q.Prime → 0<a → 0<b → p^a=q^b → p=q := by
  intro p q a b hp hq ha hb h
  have h1 : p ∣ q ^ b := h ▸ dvd_pow_self p ha.ne'
  have h2 : p ∣ q := hp.dvd_of_dvd_pow h1
  exact (Nat.prime_dvd_prime_iff_eq hp hq).mp h2

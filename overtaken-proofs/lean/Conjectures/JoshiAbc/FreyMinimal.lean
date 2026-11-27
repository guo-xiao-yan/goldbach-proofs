import Mathlib

theorem Conjectures.JoshiAbc.FreyMinimal :
    ∀ a b p : ℕ, 0<a → 0<b → Nat.Coprime a b → p.Prime → Odd p → p ∣ a*b*(a+b) → ¬ p ∣ 16*(a^2+a*b+b^2) := by
  intro a b p ha hb hc hp hodd hdiv hq
  have hne : ¬ p ∣ 16 := by
    intro h
    have : p ∣ 2 := hp.dvd_of_dvd_pow (n := 4) (by simpa using h)
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this
    subst this
    exact absurd hodd (by decide)
  have hq' : p ∣ a^2+a*b+b^2 := (hp.dvd_mul.1 hq).resolve_left hne
  have key : ¬ (p ∣ a ∧ p ∣ b) := by
    rintro ⟨h1, h2⟩
    have := Nat.dvd_gcd h1 h2
    rw [hc] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  rcases hp.dvd_mul.1 hdiv with h | h
  · rcases hp.dvd_mul.1 h with h | h
    · apply key; refine ⟨h, ?_⟩
      have : p ∣ b^2 := by
        have h3 : p ∣ a^2 + a*b := dvd_add (dvd_pow h (by norm_num)) (dvd_mul_of_dvd_left h _)
        exact (Nat.dvd_add_right h3).1 hq'
      exact hp.dvd_of_dvd_pow this
    · apply key; refine ⟨?_, h⟩
      have : p ∣ a^2 := by
        have h3 : p ∣ a*b + b^2 := dvd_add (dvd_mul_of_dvd_right h _) (dvd_pow h (by norm_num))
        have : a^2+a*b+b^2 = a^2 + (a*b+b^2) := by ring
        rw [this] at hq'
        exact (Nat.dvd_add_left h3).1 hq'
      exact hp.dvd_of_dvd_pow this
  · have : p ∣ a*b := by
      have h3 : p ∣ (a+b)^2 := dvd_pow h (by norm_num)
      have e : (a+b)^2 = (a^2+a*b+b^2) + a*b := by ring
      rw [e] at h3
      exact (Nat.dvd_add_right hq').1 h3
    rcases hp.dvd_mul.1 this with h1 | h1
    · exact key ⟨h1, (Nat.dvd_add_right h1).1 h⟩
    · exact key ⟨(Nat.dvd_add_left h1).1 h, h1⟩

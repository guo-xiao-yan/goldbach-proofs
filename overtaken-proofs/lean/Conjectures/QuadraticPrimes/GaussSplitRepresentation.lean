import Mathlib

private theorem gss_uniq (p a b c d : ℕ) (hp : p.Prime) (h4 : p % 4 = 1)
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d)
    (h1 : a^2 + b^2 = p) (h2 : c^2 + d^2 = p) : a = c ∧ b = d := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hd : 0 < d := lt_of_lt_of_le hc hcd
  have hpz : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : (0:ℤ) < p := by exact_mod_cast hp.pos
  have h1z : (a:ℤ)^2 + b^2 = p := by exact_mod_cast h1
  have h2z : (c:ℤ)^2 + d^2 = p := by exact_mod_cast h2
  have haz : (0:ℤ) < a := by exact_mod_cast ha
  have hbz : (0:ℤ) < b := by exact_mod_cast hb
  have hcz : (0:ℤ) < c := by exact_mod_cast hc
  have hdz : (0:ℤ) < d := by exact_mod_cast hd
  have habz : (a:ℤ) ≤ b := by exact_mod_cast hab
  have hcdz : (c:ℤ) ≤ d := by exact_mod_cast hcd
  have hprod : (p:ℤ) ∣ ((a:ℤ)*d - b*c) * ((a:ℤ)*d + b*c) := by
    refine ⟨(a:ℤ)^2 - c^2, ?_⟩
    have : ((a:ℤ)*d - b*c) * ((a:ℤ)*d + b*c) = (a:ℤ)^2*d^2 - b^2*c^2 := by ring
    rw [this]
    have e1 : (d:ℤ)^2 = p - c^2 := by linarith
    have e2 : (b:ℤ)^2 = p - a^2 := by linarith
    rw [e1, e2]; ring
  rcases hpz.dvd_or_dvd hprod with hx | hy
  · have hsq : ((a:ℤ)*d - b*c)^2 + (a*c + b*d)^2 = (p:ℤ)^2 := by
      have e : ((a:ℤ)*d - b*c)^2 + (a*c + b*d)^2 = ((a:ℤ)^2 + b^2) * (c^2 + d^2) := by ring
      rw [e, h1z, h2z]; ring
    obtain ⟨k, hk⟩ := hx
    have hpos : (0:ℤ) < a*c + b*d := by positivity
    have hk0 : k = 0 := by
      by_contra hne
      have : (1:ℤ) ≤ k^2 := by
        have : 0 < k^2 := by positivity
        omega
      have hh : ((a:ℤ)*d - b*c)^2 = (p:ℤ)^2 * k^2 := by rw [hk]; ring
      have hq : 0 < ((a:ℤ)*c + b*d)^2 := by positivity
      have hm := mul_le_mul_of_nonneg_left this (sq_nonneg (p:ℤ))
      linarith
    rw [hk0] at hk
    have hx0 : (a:ℤ)*d = b*c := by linarith
    have hsq2 : (a:ℤ)^2 = c^2 := by
      have : (a:ℤ)^2 * (c^2 + d^2) = c^2 * (a^2 + b^2) := by
        have : (a:ℤ)^2*d^2 = (b*c)^2 := by rw [← hx0]; ring
        nlinarith
      rw [h1z, h2z] at this
      have := mul_right_cancel₀ hp0.ne' (by linarith : (a:ℤ)^2 * p = c^2 * p)
      exact this
    have hac : (a:ℤ) = c := by nlinarith
    have hbd : (b:ℤ)^2 = d^2 := by rw [hac] at h1z; linarith
    have hbd' : (b:ℤ) = d := by nlinarith
    exact ⟨by exact_mod_cast hac, by exact_mod_cast hbd'⟩
  · exfalso
    have hsq : ((a:ℤ)*d + b*c)^2 + (a*c - b*d)^2 = (p:ℤ)^2 := by
      have e : ((a:ℤ)*d + b*c)^2 + (a*c - b*d)^2 = ((a:ℤ)^2 + b^2) * (c^2 + d^2) := by ring
      rw [e, h1z, h2z]; ring
    obtain ⟨k, hk⟩ := hy
    have hpos : (0:ℤ) < a*d + b*c := by positivity
    have hk1 : k = 1 := by
      have hk0 : 0 < k := by
        by_contra hne
        push Not at hne
        have := mul_nonneg hp0.le (neg_nonneg.mpr hne)
        linarith
      by_contra hne
      have h2k : 2 ≤ k := by omega
      have hm := mul_le_mul_of_nonneg_left h2k hp0.le
      have hy : (p:ℤ) < a*d + b*c := by linarith
      have hz2 := sq_nonneg ((a:ℤ)*c - b*d)
      have h3 : (p:ℤ)^2 < ((a:ℤ)*d + b*c)^2 := by rw [sq, sq]; exact mul_self_lt_mul_self hp0.le hy
      linarith
    rw [hk1] at hk
    have hz : (a:ℤ)*c - b*d = 0 := by
      have : ((a:ℤ)*c - b*d)^2 = 0 := by rw [hk] at hsq; linarith
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    have hz' : (a:ℤ)*c = b*d := by linarith
    have hab' : a = b := by
      by_contra hne
      have hlt : (a:ℤ) < b := by
        have : a < b := lt_of_le_of_ne hab hne
        exact_mod_cast this
      have h5 := mul_lt_mul_of_pos_right hlt hcz
      have h6 := mul_le_mul_of_nonneg_left hcdz hbz.le
      linarith
    subst hab'
    have : p = 2 * a^2 := by omega
    omega

theorem Conjectures.QuadraticPrimes.GaussSplitRepresentation :
    ∀ p : ℕ, p.Prime → p % 4 = 1 →
  ∃ a b : ℕ, (0<a ∧ a≤b ∧ a^2+b^2=p) ∧
    ∀ a' b' : ℕ, 0<a' → a'≤b' → a'^2+b'^2=p → a'=a ∧ b'=b := by
  intro p hp h4
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, y, hxy⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
  have key : ∀ x y : ℕ, x^2 + y^2 = p → x ≤ y → ∃ a b : ℕ, (0<a ∧ a≤b ∧ a^2+b^2=p) ∧
      ∀ a' b' : ℕ, 0<a' → a'≤b' → a'^2+b'^2=p → a'=a ∧ b'=b := by
    intro x y h hle
    have hx : 0 < x := by
      rcases Nat.eq_zero_or_pos x with h0 | h0
      · subst h0
        have h5 : y * y = p := by nlinarith
        have h6 : y ∣ p := ⟨y, h5.symm⟩
        rcases (Nat.dvd_prime hp).mp h6 with h7 | h7
        · subst h7; simp at h5; exact absurd h5.symm hp.one_lt.ne'
        · rw [h7] at h5
          have := hp.pos
          nlinarith [hp.one_lt]
      · exact h0
    refine ⟨x, y, ⟨hx, hle, h⟩, ?_⟩
    intro a' b' ha' hab' h'
    exact gss_uniq p a' b' x y hp h4 ha' hab' hx hle h' h
  rcases le_total x y with h | h
  · exact key x y hxy h
  · exact key y x (by linarith) h

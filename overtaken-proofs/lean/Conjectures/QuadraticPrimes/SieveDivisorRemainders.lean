import Mathlib

private lemma res_count (A B d r : ℕ) (hd : 0 < d) (hAB : A ≤ B) :
    |(((Finset.Ioc A B).filter (fun k => k ≡ r [MOD d])).card : ℝ) - ((B - A : ℕ) : ℝ) / d| ≤ 1 := by
  have h := Nat.Ioc_filter_modEq_card A B hd r
  have e1 : (⌊((B : ℚ) - r) / (d : ℚ)⌋ : ℤ) = ⌊((B : ℝ) - r) / (d : ℝ)⌋ := by
    have := Rat.floor_cast (α := ℝ) (((B : ℚ) - r) / (d : ℚ))
    push_cast at this
    rw [this]
  have e2 : (⌊((A : ℚ) - r) / (d : ℚ)⌋ : ℤ) = ⌊((A : ℝ) - r) / (d : ℝ)⌋ := by
    have := Rat.floor_cast (α := ℝ) (((A : ℚ) - r) / (d : ℚ))
    push_cast at this
    rw [this]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hl1 := Int.floor_le (((B : ℝ) - r) / d)
  have hl2 := Int.lt_floor_add_one (((B : ℝ) - r) / d)
  have hl3 := Int.floor_le (((A : ℝ) - r) / d)
  have hl4 := Int.lt_floor_add_one (((A : ℝ) - r) / d)
  have hsub : ((B - A : ℕ) : ℝ) = (B : ℝ) - A := by rw [Nat.cast_sub hAB]
  have hq : ((B : ℝ) - r) / d - ((A : ℝ) - r) / d = ((B - A : ℕ) : ℝ) / d := by
    rw [hsub]; ring
  have hge : (0 : ℝ) ≤ ((B - A : ℕ) : ℝ) / d := by positivity
  set F1 := ⌊((B : ℝ) - r) / (d : ℝ)⌋
  set F2 := ⌊((A : ℝ) - r) / (d : ℝ)⌋
  have hnn : 0 ≤ F1 - F2 := by
    have : ((F1 : ℤ) : ℝ) - F2 > -1 := by linarith
    have : ((F1 - F2 : ℤ) : ℝ) > -1 := by push_cast; linarith
    have : F1 - F2 > -1 := by exact_mod_cast this
    omega
  have hc : ((((Finset.Ioc A B).filter (fun k => k ≡ r [MOD d])).card : ℕ) : ℝ) = (F1 : ℝ) - F2 := by
    have h' : ((((Finset.Ioc A B).filter (fun k => k ≡ r [MOD d])).card : ℕ) : ℤ) = F1 - F2 := by
      rw [h, e1, e2, max_eq_left hnn]
    have := congrArg (fun t : ℤ => (t : ℝ)) h'
    simpa using this
  rw [hc, abs_le]
  constructor <;> linarith

private lemma count_close (A B d : ℕ) (hd : 0 < d) (hAB : A ≤ B) :
    |(((Finset.Ioc A B).filter (fun k => d ∣ 4 * k ^ 2 + 1)).card : ℝ)
      - ((B - A : ℕ) : ℝ) * (((Finset.range d).filter (fun r => d ∣ 4 * r ^ 2 + 1)).card : ℝ) / d|
      ≤ (((Finset.range d).filter (fun r => d ∣ 4 * r ^ 2 + 1)).card : ℝ) := by
  set roots := (Finset.range d).filter (fun r => d ∣ 4 * r ^ 2 + 1) with hroots
  have hmod : ∀ k : ℕ, d ∣ 4 * k ^ 2 + 1 ↔ d ∣ 4 * (k % d) ^ 2 + 1 := by
    intro k
    have h : k ≡ k % d [MOD d] := (Nat.mod_modEq k d).symm
    have h2 : 4 * k ^ 2 + 1 ≡ 4 * (k % d) ^ 2 + 1 [MOD d] := ((h.pow 2).mul_left 4).add_right 1
    exact h2.dvd_iff dvd_rfl
  have hsum : (((Finset.Ioc A B).filter (fun k => d ∣ 4 * k ^ 2 + 1)).card : ℕ)
      = ∑ r ∈ roots, ((Finset.Ioc A B).filter (fun k => k ≡ r [MOD d])).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun k => k % d) (t := roots)]
    · apply Finset.sum_congr rfl
      intro r hr
      have hr' : r < d ∧ d ∣ 4 * r ^ 2 + 1 := by
        simpa [hroots] using hr
      congr 1
      ext k
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hk, _⟩, h2⟩
        refine ⟨hk, ?_⟩
        show k % d = r % d
        rw [h2, Nat.mod_eq_of_lt hr'.1]
      · rintro ⟨hk, h2⟩
        have h3 : k % d = r := by
          have : k % d = r % d := h2
          rw [this, Nat.mod_eq_of_lt hr'.1]
        refine ⟨⟨hk, ?_⟩, h3⟩
        rw [hmod, h3]; exact hr'.2
    · intro k hk
      have hk' := Finset.mem_filter.1 hk
      show k % d ∈ roots
      rw [hroots, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.mod_lt _ hd, (hmod k).1 hk'.2⟩
  rw [hsum]
  push_cast
  have : ((B - A : ℕ) : ℝ) * (roots.card : ℝ) / d = ∑ r ∈ roots, ((B - A : ℕ) : ℝ) / d := by
    rw [Finset.sum_const, nsmul_eq_mul]; ring
  rw [this, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ r ∈ roots, |(((Finset.Ioc A B).filter (fun k => k ≡ r [MOD d])).card : ℝ) - ((B - A : ℕ) : ℝ) / d| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ roots, (1 : ℝ) := Finset.sum_le_sum (fun r _ => res_count A B d r hd hAB)
    _ = roots.card := by simp

private lemma rho_le (d : ℕ) (hd : 0 < d) (hsq : Squarefree d) :
    ((Finset.range d).filter (fun r => d ∣ 4 * r ^ 2 + 1)).card ≤ (Nat.divisors d).card := by
  set roots := (Finset.range d).filter (fun r => d ∣ 4 * r ^ 2 + 1) with hroots
  rcases roots.eq_empty_or_nonempty with he | ⟨r0, hr0⟩
  · rw [he]; simp
  have hr0' : r0 < d ∧ d ∣ 4 * r0 ^ 2 + 1 := by simpa [hroots] using hr0
  have key : ∀ s ∈ roots, ∀ p : ℕ, p.Prime → p ∣ d → ((p : ℤ) ∣ (s : ℤ) - r0 ∨ (p : ℤ) ∣ (s : ℤ) + r0) := by
    intro s hs p hp hpd
    have hs' : s < d ∧ d ∣ 4 * s ^ 2 + 1 := by simpa [hroots] using hs
    have h1 : (p : ℤ) ∣ 4 * (s : ℤ) ^ 2 + 1 := by exact_mod_cast hpd.trans hs'.2
    have h2 : (p : ℤ) ∣ 4 * (r0 : ℤ) ^ 2 + 1 := by exact_mod_cast hpd.trans hr0'.2
    have h3 : (p : ℤ) ∣ 4 * (((s : ℤ) - r0) * ((s : ℤ) + r0)) := by
      have := dvd_sub h1 h2
      convert this using 1; ring
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hn4 : ¬ (p : ℤ) ∣ 4 := by
      intro h4
      have h5 : (p : ℤ) ∣ 1 := by
        have := dvd_sub h1 (dvd_mul_of_dvd_left h4 ((s : ℤ) ^ 2))
        simpa using this
      exact hpz.not_dvd_one h5
    rcases hpz.dvd_or_dvd h3 with h4 | h4
    · exact absurd h4 hn4
    · exact hpz.dvd_or_dvd h4
  have hgp : ∀ s : ℕ, ∀ p : ℕ, p ∣ d → (p ∣ Nat.gcd d (((s : ℤ) - r0).natAbs) ↔ (p : ℤ) ∣ (s : ℤ) - r0) := by
    intro s p hpd
    rw [Nat.dvd_gcd_iff, Int.natCast_dvd]
    exact ⟨fun h => h.2, fun h => ⟨hpd, h⟩⟩
  have hdvdall : ∀ n : ℕ, (∀ p : ℕ, p.Prime → p ∣ d → p ∣ n) → d ∣ n := by
    intro n hn
    have h1 := Finset.prod_primes_dvd (s := d.primeFactors) n
      (fun a ha => (Nat.prime_of_mem_primeFactors ha).prime)
      (fun a ha => hn a (Nat.prime_of_mem_primeFactors ha) (Nat.dvd_of_mem_primeFactors ha))
    rwa [Nat.prod_primeFactors_of_squarefree hsq] at h1
  refine Finset.card_le_card_of_injOn (fun s => Nat.gcd d (((s : ℤ) - r0).natAbs)) ?_ ?_
  · intro s _
    simp only [Finset.mem_coe, Nat.mem_divisors]
    exact ⟨Nat.gcd_dvd_left _ _, hd.ne'⟩
  · intro s hs t ht hst
    have hs' : s < d ∧ d ∣ 4 * s ^ 2 + 1 := by simpa [hroots] using hs
    have ht' : t < d ∧ d ∣ 4 * t ^ 2 + 1 := by simpa [hroots] using ht
    have hst' : Nat.gcd d (((s : ℤ) - r0).natAbs) = Nat.gcd d (((t : ℤ) - r0).natAbs) := hst
    have hdiv : d ∣ ((s : ℤ) - t).natAbs := by
      apply hdvdall
      intro p hp hpd
      rw [← Int.natCast_dvd]
      have e1 := hgp s p hpd
      have e2 := hgp t p hpd
      rw [hst'] at e1
      have e3 : (p : ℤ) ∣ (s : ℤ) - r0 ↔ (p : ℤ) ∣ (t : ℤ) - r0 := e1.symm.trans e2
      by_cases h1 : (p : ℤ) ∣ (s : ℤ) - r0
      · have h2 := e3.1 h1
        have := dvd_sub h1 h2
        convert this using 1; ring
      · have h2 : ¬ (p : ℤ) ∣ (t : ℤ) - r0 := fun h => h1 (e3.2 h)
        have h3 := (key s hs p hp hpd).resolve_left h1
        have h4 := (key t ht p hp hpd).resolve_left h2
        have := dvd_sub h3 h4
        convert this using 1; ring
    have hdz : (d : ℤ) ∣ (s : ℤ) - t := Int.natCast_dvd.2 hdiv
    have hlt : |(s : ℤ) - t| < d := by
      rw [abs_lt]; constructor <;> omega
    have := Int.eq_zero_of_abs_lt_dvd hdz hlt
    omega

private lemma tau_sum (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, ((Nat.divisors d).card : ℝ)) ≤ (D : ℝ) * (1 + Real.log D) := by
  have h1 : ∀ d ∈ Finset.Icc 1 D, (Nat.divisors d).card = ∑ e ∈ Finset.Icc 1 D, if e ∣ d then 1 else 0 := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    rw [← Finset.card_filter]
    congr 1
    ext e
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨h, _⟩
      have := Nat.le_of_dvd (by omega) h
      have := Nat.pos_of_dvd_of_pos h (by omega)
      exact ⟨⟨by omega, by omega⟩, h⟩
    · rintro ⟨_, h⟩
      exact ⟨h, by omega⟩
  have h2 : ∑ d ∈ Finset.Icc 1 D, (Nat.divisors d).card = ∑ e ∈ Finset.Icc 1 D, D / e := by
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    rw [← Finset.card_filter]
    have : Finset.Icc 1 D = Finset.Ioc 0 D := by ext; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    rw [this, Nat.Ioc_filter_dvd_card_eq_div]
  have h3 : (∑ d ∈ Finset.Icc 1 D, ((Nat.divisors d).card : ℝ)) = ∑ e ∈ Finset.Icc 1 D, ((D / e : ℕ) : ℝ) := by
    exact_mod_cast h2
  rw [h3]
  have h4 : ∀ e ∈ Finset.Icc 1 D, ((D / e : ℕ) : ℝ) ≤ (D : ℝ) * (1 / (e : ℝ)) := by
    intro e he
    rw [Finset.mem_Icc] at he
    have : (0 : ℝ) < e := by exact_mod_cast he.1
    rw [← div_eq_mul_one_div, le_div_iff₀ this]
    exact_mod_cast Nat.div_mul_le_self D e
  refine (Finset.sum_le_sum h4).trans ?_
  rw [← Finset.mul_sum]
  have h5 : ∑ e ∈ Finset.Icc 1 D, (1 / (e : ℝ)) = (harmonic D : ℝ) := by
    have : Finset.Icc 1 D = Finset.Ico 1 (D + 1) := by ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [this, Finset.sum_Ico_eq_sum_range]
    simp only [harmonic, Rat.cast_sum]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    rw [add_comm, one_div]
  rw [h5]
  exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log D) (by positivity)

theorem Conjectures.QuadraticPrimes.SieveDivisorRemainders :
    let f := fun k : ℕ => 4*k^2+1; let roots := fun (q : ℕ) => (Finset.range q).filter (fun r => q ∣ f r); let rho := fun q : ℕ => ((roots q).card : ℝ); let count := fun A B d : ℕ => ((Finset.Ioc A B).filter (fun k => d ∣ f k)).card;
∀ A B D : ℕ, A≤B → 1≤D →
  (∑ d ∈ (Finset.Icc 1 D).filter (fun d => Odd d ∧ Squarefree d),
    |(count A B d : ℝ) - ((B-A : ℕ) : ℝ) * rho d / d|) ≤
    (D : ℝ) * (1 + Real.log D) := by
  intro f roots rho count A B D hAB hD
  have hterm : ∀ d ∈ (Finset.Icc 1 D).filter (fun d => Odd d ∧ Squarefree d),
      |(count A B d : ℝ) - ((B-A : ℕ) : ℝ) * rho d / d| ≤ ((Nat.divisors d).card : ℝ) := by
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_Icc] at hd
    have h1 := count_close A B d (by omega) hAB
    have h2 : (((Finset.range d).filter (fun r => d ∣ 4 * r ^ 2 + 1)).card : ℝ) ≤ ((Nat.divisors d).card : ℝ) := by
      exact_mod_cast rho_le d (by omega) hd.2.2
    exact le_trans h1 h2
  calc _ ≤ ∑ d ∈ (Finset.Icc 1 D).filter (fun d => Odd d ∧ Squarefree d), ((Nat.divisors d).card : ℝ) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ d ∈ Finset.Icc 1 D, ((Nat.divisors d).card : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
    _ ≤ _ := tau_sum D

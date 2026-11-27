import Mathlib

private lemma qp_key (z N : ℕ) (hz : z < N) (hN : N ≤ z ^ 3)
    (hns : ∀ m, m * m ≠ N) (hq : ∀ q, q.Prime → q ∣ N → z < q) :
    N.Prime ∨ ArithmeticFunction.moebius N = 1 := by
  have hN1 : N ≠ 1 := by
    intro h
    subst h
    have : z = 0 := by omega
    subst this
    simp at hN
  have hN0 : N ≠ 0 := by omega
  have hp : (N.minFac).Prime := Nat.minFac_prime hN1
  obtain ⟨m, hm⟩ := Nat.minFac_dvd N
  have hzp : z < N.minFac := hq _ hp (Nat.minFac_dvd N)
  by_cases hm1 : m = 1
  · left
    have : N = N.minFac := by rw [hm1] at hm; omega
    rw [this]; exact hp
  · right
    have hm0 : m ≠ 0 := by
      rintro rfl
      simp at hm
      exact hN0 hm
    have hmd : m ∣ N := Dvd.intro_left _ hm.symm
    have hmp : m.Prime := by
      by_contra hnp
      have h1 := Nat.minFac_sq_le_self (Nat.pos_of_ne_zero hm0) hnp
      have hqp : (m.minFac).Prime := Nat.minFac_prime hm1
      have h2 : z < m.minFac := hq _ hqp ((Nat.minFac_dvd m).trans hmd)
      have h3 : z ^ 2 < m := by nlinarith
      have : z * z ^ 2 < N.minFac * m := Nat.mul_lt_mul'' hzp h3
      rw [← hm] at this
      nlinarith
    have hne : N.minFac ≠ m := by
      intro h
      apply hns m
      rw [hm]; nth_rewrite 1 [← h]; rfl
    have hcop : Nat.Coprime N.minFac m := (Nat.coprime_primes hp hmp).2 hne
    rw [hm, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      ArithmeticFunction.moebius_apply_prime hp, ArithmeticFunction.moebius_apply_prime hmp]
    norm_num

theorem Conjectures.QuadraticPrimes.SieveFinalSign :
    let f := fun k : ℕ => 4*k^2+1; let block := fun x : ℕ => Finset.Ioc (x/2) x; let primes := fun z : ℕ => (Finset.Icc 3 z).filter (fun p => Nat.Prime p); let wheel := fun z : ℕ => ∏ p ∈ primes z, p; let rough := fun x z : ℕ => (block x).filter (fun k => Nat.Coprime (f k) (wheel z)); ∀ x z : ℕ, 2≤x → z≤2*x → (2*x)^2+1≤z^3 →
  (∑ k ∈ (block x).filter (fun k => (f k).Prime), Real.log (f k : ℝ)) =
    ∑ k ∈ rough x z, (1 - (ArithmeticFunction.moebius (f k) : ℝ))/2 * Real.log (f k : ℝ) := by
  intro f block primes wheel rough x z hx hz h
  have hb : ∀ k, k ∈ block x → 1 ≤ k ∧ k ≤ x ∧ z < f k ∧ f k ≤ z ^ 3 := by
    intro k hk
    simp only [block, Finset.mem_Ioc] at hk
    obtain ⟨h1, h2⟩ := hk
    have h3 : 1 ≤ k := by omega
    have h4 : x + 1 ≤ 2 * k := by omega
    refine ⟨h3, h2, ?_, ?_⟩
    · show z < 4 * k ^ 2 + 1
      nlinarith
    · show 4 * k ^ 2 + 1 ≤ z ^ 3
      have : k ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left h2 2
      nlinarith
  have hA : ∀ k ∈ block x, (f k).Prime → Nat.Coprime (f k) (wheel z) := by
    intro k hk hpr
    obtain ⟨_, _, hzk, _⟩ := hb k hk
    show Nat.Coprime (f k) (∏ p ∈ primes z, p)
    apply Nat.Coprime.prod_right
    intro p hp
    simp only [primes, Finset.mem_filter, Finset.mem_Icc] at hp
    apply (Nat.coprime_primes hpr hp.2).2
    omega
  have hB : ∀ k ∈ rough x z, (f k).Prime ∨ ArithmeticFunction.moebius (f k) = 1 := by
    intro k hk
    simp only [rough, Finset.mem_filter] at hk
    obtain ⟨hk1, hk2⟩ := hk
    obtain ⟨h1, h2, h3, h4⟩ := hb k hk1
    apply qp_key z (f k) h3 h4
    · intro m hm
      have : m * m = 4 * k ^ 2 + 1 := hm
      have h5 : (2 * k) ^ 2 < m ^ 2 := by nlinarith
      have h6 : m ^ 2 < (2 * k + 1) ^ 2 := by nlinarith
      have h7 := lt_of_pow_lt_pow_left₀ 2 (by positivity) h5
      have h8 := lt_of_pow_lt_pow_left₀ 2 (by positivity) h6
      omega
    · intro q hq hqd
      by_contra hle
      push_neg at hle
      have hq2 : q ≠ 2 := by
        rintro rfl
        have : 2 ∣ 4 * k ^ 2 + 1 := hqd
        omega
      have hqw : q ∣ wheel z := by
        show q ∣ ∏ p ∈ primes z, p
        apply Finset.dvd_prod_of_mem
        simp only [primes, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨by have := hq.two_le; omega, hle⟩, hq⟩
      have := Nat.dvd_gcd hqd hqw
      rw [hk2] at this
      exact hq.one_lt.ne' (Nat.dvd_one.1 this)
  have step1 : ∑ k ∈ rough x z, (1 - (ArithmeticFunction.moebius (f k) : ℝ))/2 * Real.log (f k : ℝ)
      = ∑ k ∈ rough x z, if (f k).Prime then Real.log (f k : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro k hk
    rcases hB k hk with hpr | hmu
    · have : ArithmeticFunction.moebius (f k) = -1 := ArithmeticFunction.moebius_apply_prime hpr
      rw [if_pos hpr, this]; push_cast; ring
    · by_cases hpr : (f k).Prime
      · have : ArithmeticFunction.moebius (f k) = -1 := ArithmeticFunction.moebius_apply_prime hpr
        rw [if_pos hpr, this]; push_cast; ring
      · rw [if_neg hpr, hmu]; push_cast; ring
  rw [step1, ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext k
  simp only [rough, Finset.mem_filter]
  constructor
  · rintro ⟨hk, hp⟩
    exact ⟨⟨hk, hA k hk hp⟩, hp⟩
  · rintro ⟨⟨hk, _⟩, hp⟩
    exact ⟨hk, hp⟩

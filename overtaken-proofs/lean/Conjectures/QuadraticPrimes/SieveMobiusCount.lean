import Mathlib

private theorem qm_sum_mu (n : ℕ) (_hn : n ≠ 0) :
    ∑ d ∈ n.divisors, ArithmeticFunction.moebius d = if n = 1 then 1 else 0 := by
  have h := congrArg (fun g : ArithmeticFunction ℤ => g n) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  rw [h]

private theorem qm_point (a W : ℕ) (hW : W ≠ 0) :
    (if Nat.Coprime a W then (1 : ℤ) else 0)
      = ∑ d ∈ W.divisors, if d ∣ a then ArithmeticFunction.moebius d else 0 := by
  have hg : Nat.gcd a W ≠ 0 := by
    intro h; exact hW (Nat.gcd_eq_zero_iff.mp h).2
  rw [← Finset.sum_filter]
  have : W.divisors.filter (fun d => d ∣ a) = (Nat.gcd a W).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨⟨h2, h1⟩, hg⟩
    · rintro ⟨⟨h2, h1⟩, _⟩; exact ⟨⟨h1, hW⟩, h2⟩
  rw [this, qm_sum_mu _ hg]

theorem Conjectures.QuadraticPrimes.SieveMobiusCount :
    let f := fun k : ℕ => 4*k^2+1; let block := fun x : ℕ => Finset.Ioc (x/2) x; let primes := fun z : ℕ => (Finset.Icc 3 z).filter (fun p => Nat.Prime p); let wheel := fun z : ℕ => ∏ p ∈ primes z, p; let rough := fun x z : ℕ => (block x).filter (fun k => Nat.Coprime (f k) (wheel z)); let hitCount := fun x d : ℕ => ((block x).filter (fun k => d ∣ f k)).card;
    ∀ x z : ℕ, ((rough x z).card : ℤ) = ∑ d ∈ (wheel z).divisors, ArithmeticFunction.moebius d * (hitCount x d : ℤ) := by
  intro f block primes wheel rough hitCount x z
  have hW : wheel z ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact (Nat.Prime.pos (Finset.mem_filter.mp hp).2).ne'
  have h1 : ((rough x z).card : ℤ) = ∑ k ∈ block x, if Nat.Coprime (f k) (wheel z) then (1 : ℤ) else 0 := by
    simp only [rough, Finset.card_filter]
    push_cast
    rfl
  rw [h1]
  simp_rw [qm_point _ _ hW]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  simp only [hitCount, Finset.card_filter]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp

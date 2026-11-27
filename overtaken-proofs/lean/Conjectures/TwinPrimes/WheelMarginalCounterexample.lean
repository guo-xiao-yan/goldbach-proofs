import Mathlib

private lemma wheel_cop_aux (m a q : ℕ) (h : m % q = a % q) (hc : Nat.Coprime a q) :
    Nat.Coprime m q := by
  unfold Nat.Coprime at *
  rw [Nat.gcd_comm, Nat.gcd_rec, h, ← Nat.gcd_rec, Nat.gcd_comm]
  exact hc

private lemma wheel_marg_aux (S : Finset ℕ) (k1 k2 : ℕ) (h1 : k1 ∈ S) (h2 : k2 ∈ S)
    (hne : k1 ≠ k2) (q a : ℕ) :
    ((S.filter (fun n => n % q = a)).sum
      (fun n => (if n = k1 ∨ n = k2 then (1:ℝ) else 0))) =
      (if k1 % q = a then (1:ℝ) else 0) + (if k2 % q = a then (1:ℝ) else 0) := by
  have key : ∀ n : ℕ, (if n = k1 ∨ n = k2 then (1:ℝ) else 0) =
      (if n = k1 then (1:ℝ) else 0) + (if n = k2 then (1:ℝ) else 0) := by
    intro n
    by_cases a1 : n = k1
    · have : n ≠ k2 := by omega
      simp [a1, this, hne]
    · by_cases a2 : n = k2 <;> simp [a1, a2, hne, hne.symm]
  rw [Finset.sum_congr rfl (fun n _ => key n), Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp [Finset.mem_filter, h1, h2]

theorem Conjectures.TwinPrimes.WheelMarginalCounterexample :
    let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); ∀ (q X : ℕ), 0 < q → 200*(q+1) ≤ X → (∃ a : ℕ, a < q ∧ Nat.Coprime a q ∧ Nat.Coprime (a+2) q) → (∃ f g : ℕ → ℝ, (∀ n, (f n=0 ∨ f n=1) ∧ (g n=0 ∨ g n=1) ∧ (¬ (n ∈ w X ∧ Nat.Coprime n q) → f n=0 ∧ g n=0)) ∧ (∀ a : ℕ, a < q → ((w X).filter (fun n => n % q=a)).sum f = ((w X).filter (fun n => n % q=a)).sum g) ∧ (w X).sum (fun n => f n * f (n+2))=1 ∧ (w X).sum (fun n => g n * g (n+2))=0) := by
  intro w q X hq hX ⟨a, haq, ha1, ha2⟩
  set k := (X / q + 1) * q + a with hk
  have hkmod : k % q = a := by
    rw [hk, Nat.mul_comm, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt haq
  have hdiv : X < (X / q + 1) * q := by
    rw [Nat.add_mul, Nat.one_mul]
    have := Nat.lt_div_mul_add (a := X) hq
    omega
  have hdiv2 : X / q * q ≤ X := Nat.div_mul_le_self X q
  have hk1 : X < k := by omega
  have hk2 : k ≤ X + 2 * q := by
    rw [hk, Nat.add_mul, Nat.one_mul]; omega
  have hmem : ∀ m, m ∈ w X ↔ (m < 2*X+1 ∧ X < m ∧ 50*m < 51*X) := by
    intro m
    simp only [w, Finset.mem_filter, Finset.mem_range]
  have hm1 : k ∈ w X := (hmem k).2 ⟨by omega, by omega, by omega⟩
  have hm2 : k + 2 ∈ w X := (hmem _).2 ⟨by omega, by omega, by omega⟩
  have hm3 : k + 2 + 2 * q ∈ w X := (hmem _).2 ⟨by omega, by omega, by omega⟩
  have c1 : Nat.Coprime k q := wheel_cop_aux k a q (by rw [hkmod]; exact (Nat.mod_eq_of_lt haq).symm) ha1
  have c2 : Nat.Coprime (k + 2) q := wheel_cop_aux (k+2) (a+2) q (by
    rw [Nat.add_mod k 2 q, hkmod, Nat.add_mod_mod]) ha2
  have c3 : Nat.Coprime (k + 2 + 2 * q) q := wheel_cop_aux (k+2+2*q) (a+2) q (by
    rw [Nat.add_mul_mod_self_right, Nat.add_mod k 2 q, hkmod, Nat.add_mod_mod]) ha2
  refine ⟨fun n => if n = k ∨ n = k + 2 then 1 else 0,
    fun n => if n = k ∨ n = k + 2 + 2 * q then 1 else 0, ?_, ?_, ?_, ?_⟩
  · intro n
    refine ⟨?_, ?_, ?_⟩
    · by_cases h : n = k ∨ n = k + 2 <;> simp [h]
    · by_cases h : n = k ∨ n = k + 2 + 2 * q <;> simp [h]
    · intro hn
      constructor
      · by_cases h : n = k ∨ n = k + 2
        · exfalso; apply hn
          rcases h with rfl | rfl
          · exact ⟨hm1, c1⟩
          · exact ⟨hm2, c2⟩
        · simp [h]
      · by_cases h : n = k ∨ n = k + 2 + 2 * q
        · exfalso; apply hn
          rcases h with rfl | rfl
          · exact ⟨hm1, c1⟩
          · exact ⟨hm3, c3⟩
        · simp [h]
  · intro a' _
    rw [wheel_marg_aux _ k (k+2) hm1 hm2 (by omega),
      wheel_marg_aux _ k (k+2+2*q) hm1 hm3 (by omega)]
    rw [Nat.add_mul_mod_self_right]
  · rw [Finset.sum_eq_single k]
    · have e1 : k + 2 ≠ k := by omega
      simp
    · intro n _ hn
      beta_reduce
      split_ifs <;> first | omega | simp
    · intro h; exact absurd hm1 h
  · apply Finset.sum_eq_zero
    intro n _
    beta_reduce
    split_ifs <;> first | omega | simp

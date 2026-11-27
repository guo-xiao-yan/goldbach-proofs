import Mathlib

theorem Conjectures.Goldbach.DynModularMirage :
    ∀ N : ℕ, Even N → 4 ≤ N → ∃ A : Set ℕ, (∀ a ∈ A, Odd a) ∧ (∀ m : ℕ, 0 < m → ∃ a ∈ A, ∃ b ∈ A, (a+b) % m = N % m) ∧ ¬ (∃ a ∈ A, ∃ b ∈ A, a+b=N) := by
  intro N hN h4
  obtain ⟨k, hk⟩ := hN
  refine ⟨{a | Odd a ∧ N < a}, fun a ha => ha.1, ?_, ?_⟩
  · intro m hm
    have hmN : 1 ≤ m * N := Nat.mul_pos hm (by omega)
    have e : 2*m*N = 2*(m*N) := by ring
    have h1 : Odd (2*m*N+1) := ⟨m*N, by omega⟩
    have h2 : Odd (N-1+2*m*N) := ⟨k-1+m*N, by omega⟩
    have h3 : N < 2*m*N+1 := by nlinarith
    have h4' : N < N-1+2*m*N := by omega
    refine ⟨2*m*N+1, ⟨h1, h3⟩, N-1+2*m*N, ⟨h2, h4'⟩, ?_⟩
    have : 2*m*N+1+(N-1+2*m*N) = N + m*(4*N) := by
      have : 1 ≤ N := by omega
      zify [this]; ring
    rw [this, Nat.add_mul_mod_self_left]
  · rintro ⟨a, ha, b, hb, hab⟩
    have := ha.2; have := hb.2; omega

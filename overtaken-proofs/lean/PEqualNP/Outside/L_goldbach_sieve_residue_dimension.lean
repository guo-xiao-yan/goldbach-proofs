import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat

theorem PEqualNP.Outside.L_goldbach_sieve_residue_dimension :
    ∀ n p : ℕ, p.Prime → ((Finset.range p).filter (fun k => k % p=0 ∨ k % p=n % p)).card = if p∣n then 1 else 2 := by
  intro n p hp
  have hp0 : 0 < p := hp.pos
  have hnp : n % p < p := Nat.mod_lt _ hp0
  have h : (Finset.range p).filter (fun k => k % p=0 ∨ k % p=n % p) = {0, n % p} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, h⟩
      rw [Nat.mod_eq_of_lt hk] at h
      exact h
    · rintro (h | h)
      · subst h; simp [hp0]
      · subst h; refine ⟨hnp, Or.inr ?_⟩; rw [Nat.mod_eq_of_lt hnp]
  rw [h]
  by_cases hd : p ∣ n
  · have : n % p = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
    simp [this, hd]
  · have : n % p ≠ 0 := fun h0 => hd (Nat.dvd_iff_mod_eq_zero.mpr h0)
    rw [if_neg hd, Finset.card_insert_of_notMem (by simpa [eq_comm] using this)]
    simp

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat

theorem PEqualNP.Outside.L_goldbach_theta_coset_factor :
    ∀ (p n : ℕ), p.Prime → ((Finset.range p).filter (fun k => k % p≠0 ∧ k % p≠n % p)).card = if p∣n then p-1 else p-2 := by
  intro p n hp
  have hp0 : 0 < p := hp.pos
  have hp2 := hp.two_le
  have hnp : n % p < p := Nat.mod_lt _ hp0
  have h : (Finset.range p).filter (fun k => k % p≠0 ∧ k % p≠n % p) =
      ((Finset.range p).erase 0).erase (n % p) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
    constructor
    · rintro ⟨hk, h1, h2⟩
      rw [Nat.mod_eq_of_lt hk] at h1 h2
      exact ⟨h2, h1, hk⟩
    · rintro ⟨h2, h1, hk⟩
      rw [Nat.mod_eq_of_lt hk]
      exact ⟨hk, h1, h2⟩
  rw [h]
  by_cases hd : p ∣ n
  · have h0 : n % p = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
    rw [h0, if_pos hd, Finset.erase_eq_of_notMem (by simp), Finset.card_erase_of_mem (by simp [hp0])]
    simp
  · have h0 : n % p ≠ 0 := fun h0 => hd (Nat.dvd_iff_mod_eq_zero.mpr h0)
    rw [if_neg hd, Finset.card_erase_of_mem (by simp [h0, hnp]), Finset.card_erase_of_mem (by simp [hp0])]
    simp
    omega

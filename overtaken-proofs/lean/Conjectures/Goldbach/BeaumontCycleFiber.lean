import Mathlib

theorem Conjectures.Goldbach.BeaumontCycleFiber :
    ∀ (m a : ℕ), 0 < m → ((Finset.range m).filter (fun k => (a*k) % m=0)).card = Nat.gcd m a := by
  intro m a hm
  set g := Nat.gcd m a with hg
  have gpos : 0 < g := Nat.gcd_pos_of_pos_left _ hm
  obtain ⟨d, hd⟩ : g ∣ m := Nat.gcd_dvd_left m a
  obtain ⟨e, he⟩ : g ∣ a := Nat.gcd_dvd_right m a
  have hcop : Nat.Coprime d e := by
    have := Nat.coprime_div_gcd_div_gcd (m := m) (n := a) gpos
    rw [← hg, hd, he, Nat.mul_div_cancel_left _ gpos, Nat.mul_div_cancel_left _ gpos] at this
    exact this
  have dpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h; omega
    · exact h
  have key : ∀ k, (a*k) % m = 0 ↔ d ∣ k := by
    intro k
    rw [← Nat.dvd_iff_mod_eq_zero, he, hd, mul_assoc]
    rw [Nat.mul_dvd_mul_iff_left gpos]
    exact ⟨fun h => hcop.dvd_of_dvd_mul_left h, fun h => Dvd.dvd.mul_left h _⟩
  have : (Finset.range m).filter (fun k => (a*k) % m=0) = (Finset.range g).image (fun j => d*j) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, key]
    constructor
    · rintro ⟨hk, j, rfl⟩
      refine ⟨j, ?_, rfl⟩
      rw [hd] at hk
      exact lt_of_mul_lt_mul_left (by linarith) (Nat.zero_le d)
    · rintro ⟨j, hj, rfl⟩
      refine ⟨?_, ⟨j, rfl⟩⟩
      rw [hd]
      calc d * j < d * g := Nat.mul_lt_mul_of_pos_left hj dpos
        _ = g * d := mul_comm _ _
  rw [this, Finset.card_image_of_injective _ (fun x y h => Nat.eq_of_mul_eq_mul_left dpos h)]
  simp

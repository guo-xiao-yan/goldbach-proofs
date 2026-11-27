import Mathlib

private lemma bsmc_aux (a b c d : ℕ) (hab : a ≤ b) (hcd : c ≤ d) (hac : a < c)
    (h : 2^a + 2^b = 2^c + 2^d) : False := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_lt hac
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hab
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le (show a + i + 1 ≤ d from by omega)
  have h2 : 2^a * (1 + 2^j) = 2^a * (2^(i+1) + 2^(i+1+l)) := by
    rw [mul_add, mul_add, ← pow_add, ← pow_add, ← pow_add]
    rw [show a + i + 1 + l = a + (i + 1 + l) by ring] at h
    rw [show a + i + 1 = a + (i + 1) by ring] at h
    simpa using h
  have h3 : 1 + 2^j = 2^(i+1) + 2^(i+1+l) := Nat.eq_of_mul_eq_mul_left (by positivity) h2
  have e1 : 2 ∣ 2^(i+1) + 2^(i+1+l) :=
    dvd_add (dvd_pow_self 2 (by omega)) (dvd_pow_self 2 (by omega))
  rw [← h3] at e1
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have h4 : 2 ≤ 2^(i+1) := Nat.le_self_pow (by omega) 2
    have h5 : 2 ≤ 2^(i+1+l) := Nat.le_self_pow (by omega) 2
    simp at h3
    omega
  · have : 2 ∣ 2^j := dvd_pow_self 2 (by omega)
    omega

private lemma bsmc_key {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d)
    (h : 2^a + 2^b = 2^c + 2^d) : a = c ∧ b = d := by
  have hac : a = c := by
    rcases lt_trichotomy a c with h1 | h1 | h1
    · exact (bsmc_aux a b c d hab hcd h1 h).elim
    · exact h1
    · exact (bsmc_aux c d a b hcd hab h1 h.symm).elim
  subst hac
  refine ⟨rfl, ?_⟩
  exact Nat.pow_right_injective (le_refl 2) (Nat.add_left_cancel h)

private lemma bsmc_mem {e k e0 k0 : ℕ} (h : 2^e + 2^k = 2^e0 + 2^k0) :
    e = min e0 k0 ∨ e = max e0 k0 := by
  have h1 : 2^(min e k) + 2^(max e k) = 2^e + 2^k := by
    rcases le_total e k with h | h
    · simp [min_eq_left h, max_eq_right h]
    · simp [min_eq_right h, max_eq_left h, add_comm]
  have h2 : 2^(min e0 k0) + 2^(max e0 k0) = 2^e0 + 2^k0 := by
    rcases le_total e0 k0 with h | h
    · simp [min_eq_left h, max_eq_right h]
    · simp [min_eq_right h, max_eq_left h, add_comm]
  obtain ⟨x, y⟩ := bsmc_key (min_le_max) (min_le_max) (h1.trans (h.trans h2.symm))
  rcases le_total e k with hk | hk
  · left; simpa [min_eq_left hk] using x
  · right; simpa [max_eq_left hk] using y

theorem Conjectures.Goldbach.BinaryShiftMissedCenter :
    ∀ n L : ℕ, ((Finset.Icc 1 L).filter (fun e => n = 2^e + 2^(Nat.log 2 (n-2^e)))).card ≤ 2 := by
  intro n L
  by_cases hne : ((Finset.Icc 1 L).filter (fun e => n = 2^e + 2^(Nat.log 2 (n-2^e)))).Nonempty
  · obtain ⟨e0, he0⟩ := hne
    rw [Finset.mem_filter] at he0
    set k0 := Nat.log 2 (n - 2^e0)
    have hsub : ((Finset.Icc 1 L).filter (fun e => n = 2^e + 2^(Nat.log 2 (n-2^e)))) ⊆
        {min e0 k0, max e0 k0} := by
      intro e he
      rw [Finset.mem_filter] at he
      have := bsmc_mem (e := e) (k := Nat.log 2 (n - 2^e)) (e0 := e0) (k0 := k0)
        (he.2.symm.trans he0.2)
      simpa using this
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]; simp

import Mathlib

private lemma eb_parseval (n : ℕ) [NeZero n] (G : ZMod n → ℂ) :
    ∑ k : ZMod n, (ZMod.stdAddChar (N := n) (2 * k)).re * ‖ZMod.dft G k‖ ^ 2
      = ((n : ℂ) * ∑ j : ZMod n, G (j + 2) * (starRingEnd ℂ) (G j)).re := by
  classical
  have key : ∑ k : ZMod n, ZMod.stdAddChar (N := n) (2 * k)
        * (ZMod.dft G k * (starRingEnd ℂ) (ZMod.dft G k))
      = (n : ℂ) * ∑ j : ZMod n, G (j + 2) * (starRingEnd ℂ) (G j) := by
    have h1 : ∀ k : ZMod n, ZMod.stdAddChar (N := n) (2 * k)
        * (ZMod.dft G k * (starRingEnd ℂ) (ZMod.dft G k))
        = ∑ j : ZMod n, ∑ i : ZMod n,
          ZMod.stdAddChar (N := n) (k * (2 - i + j)) * (G i * (starRingEnd ℂ) (G j)) := by
      intro k
      simp only [ZMod.dft_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      have hc : (starRingEnd ℂ) (ZMod.stdAddChar (N := n) (-(j * k)))
          = ZMod.stdAddChar (N := n) (j * k) := by
        rw [← AddChar.map_neg_eq_conj, neg_neg]
      rw [hc]
      have : ZMod.stdAddChar (N := n) (k * (2 - i + j))
          = ZMod.stdAddChar (N := n) (2 * k) * ZMod.stdAddChar (N := n) (-(i * k))
            * ZMod.stdAddChar (N := n) (j * k) := by
        rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
        congr 1
        ring
      rw [this]
      ring
    simp only [h1]
    rw [Finset.sum_comm]
    refine Eq.trans (Finset.sum_congr rfl fun j _ => Finset.sum_comm) ?_
    have h2 : ∀ j i : ZMod n, ∑ k : ZMod n,
        ZMod.stdAddChar (N := n) (k * (2 - i + j)) * (G i * (starRingEnd ℂ) (G j))
        = if i = j + 2 then (n : ℂ) * (G i * (starRingEnd ℂ) (G j)) else 0 := by
      intro j i
      rw [← Finset.sum_mul, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar n)]
      have hiff : (2 - i + j = 0) ↔ (i = j + 2) := by
        constructor
        · intro h
          linear_combination -h
        · intro h
          rw [h]
          ring
      by_cases h : i = j + 2
      · rw [if_pos (hiff.2 h), if_pos h]
        simp [ZMod.card]
      · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]
        simp
    simp only [h2, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
  have hre : ∀ k : ZMod n, (ZMod.stdAddChar (N := n) (2 * k)).re * ‖ZMod.dft G k‖ ^ 2
      = (ZMod.stdAddChar (N := n) (2 * k)
        * (ZMod.dft G k * (starRingEnd ℂ) (ZMod.dft G k))).re := by
    intro k
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [Complex.re_mul_ofReal]
  simp only [hre]
  rw [← key, Complex.re_sum]

private lemma eb_extract (X a b : ℕ)
    (hj : 0 < (if a ∈ (Finset.range (2 * X + 1)).filter (fun n => X < n ∧ 50 * n < 51 * X)
        ∧ a.Prime then Real.log a else 0)
      * (if b ∈ (Finset.range (2 * X + 1)).filter (fun n => X < n ∧ 50 * n < 51 * X)
        ∧ b.Prime then Real.log b else 0)) :
    (a ∈ (Finset.range (2 * X + 1)).filter (fun n => X < n ∧ 50 * n < 51 * X) ∧ a.Prime)
    ∧ (b ∈ (Finset.range (2 * X + 1)).filter (fun n => X < n ∧ 50 * n < 51 * X) ∧ b.Prime) := by
  by_cases h1 : a ∈ (Finset.range (2 * X + 1)).filter (fun n => X < n ∧ 50 * n < 51 * X)
        ∧ a.Prime
  · by_cases h2 : b ∈ (Finset.range (2 * X + 1)).filter (fun n => X < n ∧ 50 * n < 51 * X)
        ∧ b.Prime
    · exact ⟨h1, h2⟩
    · rw [if_neg h2, mul_zero] at hj
      exact absurd hj (lt_irrefl _)
  · rw [if_neg h1, zero_mul] at hj
    exact absurd hj (lt_irrefl _)

theorem Conjectures.TwinPrimes.EnergyBridgeV2 :
    (let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let N := fun (X : ℕ) => 2*X+5; let f := fun (X n : ℕ) => if n ∈ w X ∧ n.Prime then Real.log n else 0; let energy := fun (X : ℕ) => letI : NeZero (N X) := ⟨Nat.succ_ne_zero _⟩; ∑ k : ZMod (N X), (ZMod.stdAddChar (N:=N X) (2*k)).re * ‖ZMod.dft (fun j : ZMod (N X) => ((f X j.val:ℝ):ℂ)) k‖^2; ∀ B : ℕ, ∃ X : ℕ, B<X ∧ 0<energy X) → (∀ B : ℕ, ∃ p : ℕ, B < p ∧ p.Prime ∧ (p+2).Prime) := by
  intro h B
  dsimp only at h
  obtain ⟨X, hX, hpos⟩ := h B
  have : NeZero (2 * X + 5) := ⟨Nat.succ_ne_zero _⟩
  rw [eb_parseval] at hpos
  have hterm : ∀ j : ZMod (2 * X + 5),
      (((if (j + 2).val ∈ (Finset.range (2 * X + 1)).filter (fun n => X < n ∧ 50 * n < 51 * X)
          ∧ (j + 2).val.Prime then Real.log (j + 2).val else 0 : ℝ) : ℂ)
        * (starRingEnd ℂ) ((if j.val ∈ (Finset.range (2 * X + 1)).filter
          (fun n => X < n ∧ 50 * n < 51 * X) ∧ j.val.Prime then Real.log j.val else 0 : ℝ) : ℂ))
      = ((((if (j + 2).val ∈ (Finset.range (2 * X + 1)).filter (fun n => X < n ∧ 50 * n < 51 * X)
          ∧ (j + 2).val.Prime then Real.log (j + 2).val else 0 : ℝ)
        * (if j.val ∈ (Finset.range (2 * X + 1)).filter
          (fun n => X < n ∧ 50 * n < 51 * X) ∧ j.val.Prime then Real.log j.val else 0 : ℝ)) : ℝ) : ℂ) := by
    intro j
    rw [Complex.conj_ofReal, Complex.ofReal_mul]
  simp only [hterm] at hpos
  rw [← Complex.ofReal_sum] at hpos
  rw [show ((2 * X + 5 : ℕ) : ℂ) = (((2 * X + 5 : ℕ) : ℝ) : ℂ) by simp, Complex.re_ofReal_mul] at hpos
  simp only [Complex.ofReal_re] at hpos
  replace hpos := (mul_pos_iff_of_pos_left (by positivity)).1 hpos
  obtain ⟨j, -, hj⟩ := Finset.exists_lt_of_sum_lt <| Finset.sum_const_zero.trans_lt hpos
  obtain ⟨⟨hm2, hp2⟩, ⟨hm1, hp1⟩⟩ := eb_extract X _ _ hj
  simp only [Finset.mem_filter, Finset.mem_range] at hm1 hm2
  have hv : (j + 2).val = j.val + 2 := by
    have e : j + 2 = ((j.val + 2 : ℕ) : ZMod (2 * X + 5)) := by
      push_cast
      rw [ZMod.natCast_zmod_val]
    rw [e, ZMod.val_natCast, Nat.mod_eq_of_lt]
    omega
  rw [hv] at hp2
  exact ⟨j.val, by omega, hp1, hp2⟩

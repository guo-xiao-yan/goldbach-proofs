import Mathlib

private theorem pell_spacing_aux :
    ∀ (m a b u v : ℕ), (0 < m) → (0 < a) → (a < b) → (a^2 + 1 = m*u^2) → (b^2 + 1 = m*v^2) → 2*a < b := by
  intro m a b u v hm ha hab hA hB
  have hm1 : 1 ≤ m := by omega
  have hu1 : 1 ≤ u := by
    by_contra h
    have hu0 : u = 0 := Nat.eq_zero_of_le_zero (by omega)
    subst hu0
    simp at hA
  have haz : (0:ℤ) < a := by exact_mod_cast ha
  have habz : (a:ℤ) < b := by exact_mod_cast hab
  have hm1z : (1:ℤ) ≤ (m:ℤ) := by exact_mod_cast hm1
  have hu1z : (1:ℤ) ≤ (u:ℤ) := by exact_mod_cast hu1
  have hAz : (a:ℤ)^2 + 1 = (m:ℤ)*(u:ℤ)^2 := by exact_mod_cast hA
  have hBz : (b:ℤ)^2 + 1 = (m:ℤ)*(v:ℤ)^2 := by exact_mod_cast hB
  have ha0 : (0:ℤ) ≤ a := Nat.cast_nonneg a
  have hb0 : (0:ℤ) ≤ b := Nat.cast_nonneg b
  have hu0 : (0:ℤ) ≤ u := Nat.cast_nonneg u
  have hv0 : (0:ℤ) ≤ v := Nat.cast_nonneg v
  have hm0 : (0:ℤ) ≤ m := Nat.cast_nonneg m
  have hsqvu : (u:ℤ)^2 < (v:ℤ)^2 := by
    have hmv : (0:ℤ) < (m:ℤ)*((v:ℤ)^2 - (u:ℤ)^2) := by
      have hkey : (b:ℤ)^2 - (a:ℤ)^2 = (m:ℤ)*((v:ℤ)^2 - (u:ℤ)^2) := by
        linear_combination hBz - hAz
      have hsqab : (a:ℤ)^2 < (b:ℤ)^2 := (sq_lt_sq₀ ha0 hb0).mpr habz
      rw [← hkey]
      exact sub_pos.mpr hsqab
    have hpos : (0:ℤ) < (v:ℤ)^2 - (u:ℤ)^2 := by
      by_contra hcon
      have hle : (v:ℤ)^2 - (u:ℤ)^2 ≤ 0 := not_lt.mp hcon
      exact absurd hmv (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hm0 hle))
    exact sub_pos.mp hpos
  have hkeyB : ((b:ℤ)*(u:ℤ))^2 = ((a:ℤ)*(v:ℤ))^2 + ((v:ℤ)^2 - (u:ℤ)^2) := by
    linear_combination ((u:ℤ)^2) * hBz - ((v:ℤ)^2) * hAz
  have hBpos : (0:ℤ) < (b:ℤ)*(u:ℤ) - (a:ℤ)*(v:ℤ) := by
    have hsq : ((a:ℤ)*(v:ℤ))^2 < ((b:ℤ)*(u:ℤ))^2 := by
      rw [hkeyB]
      exact lt_add_of_pos_right _ (sub_pos.mpr hsqvu)
    exact sub_pos.mpr ((sq_lt_sq₀ (mul_nonneg ha0 hv0) (mul_nonneg hb0 hu0)).mp hsq)
  have hkeyA : ((m:ℤ)*(u:ℤ)*(v:ℤ))^2 = ((a:ℤ)*(b:ℤ))^2 + ((a:ℤ)^2 + (b:ℤ)^2 + 1) := by
    linear_combination (-((b:ℤ)^2 + 1)) * hAz + (-((m:ℤ)*(u:ℤ)^2)) * hBz
  have hApos : (0:ℤ) < (m:ℤ)*(u:ℤ)*(v:ℤ) - (a:ℤ)*(b:ℤ) := by
    have hpos : (0:ℤ) < (a:ℤ)^2 + (b:ℤ)^2 + 1 := by positivity
    have hsq : ((a:ℤ)*(b:ℤ))^2 < ((m:ℤ)*(u:ℤ)*(v:ℤ))^2 := by
      rw [hkeyA]
      exact lt_add_of_pos_right _ hpos
    exact sub_pos.mpr ((sq_lt_sq₀ (mul_nonneg ha0 hb0)
      (mul_nonneg (mul_nonneg hm0 hu0) hv0)).mp hsq)
  obtain ⟨A, hAdef⟩ : ∃ A : ℤ, A = (m:ℤ)*(u:ℤ)*(v:ℤ) - (a:ℤ)*(b:ℤ) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℤ, B = (b:ℤ)*(u:ℤ) - (a:ℤ)*(v:ℤ) := ⟨_, rfl⟩
  have hA1 : (1:ℤ) ≤ A := by rw [hAdef]; omega
  have hB1 : (1:ℤ) ≤ B := by rw [hBdef]; omega
  have hnorm : A^2 = (m:ℤ)*B^2 + 1 := by
    rw [hAdef, hBdef]
    linear_combination ((a:ℤ)^2 - (m:ℤ)*(u:ℤ)^2) * hBz - hAz
  have hB2 : (1:ℤ) ≤ B^2 := by nlinarith only [hB1]
  have hmB : (1:ℤ) ≤ (m:ℤ)*B^2 := by nlinarith only [hm1z, hB2]
  have hAsq : (2:ℤ) ≤ A^2 := by linarith only [hnorm, hmB]
  have hA2 : (2:ℤ) ≤ A := by
    by_contra h
    have hlt : A < 2 := not_le.mp h
    have heq : A = 1 := by omega
    rw [heq] at hAsq
    norm_num at hAsq
  have hrec : (b:ℤ) = (a:ℤ)*A + (m:ℤ)*(u:ℤ)*B := by
    rw [hAdef, hBdef]
    linear_combination (b:ℤ) * hAz
  have hlo : (2:ℤ)*(a:ℤ) ≤ (a:ℤ)*A := by nlinarith only [hA2, ha0]
  have hmu : (1:ℤ) ≤ (m:ℤ)*(u:ℤ) := by nlinarith only [hm1z, hu1z]
  have hmuB : (1:ℤ) ≤ (m:ℤ)*(u:ℤ)*B := by nlinarith only [hmu, hB1]
  have hfinal : (2:ℤ)*(a:ℤ) < (b:ℤ) := by linarith only [hrec, hlo, hmuB]
  exact_mod_cast hfinal

private lemma two_classes_aux (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (a b : ℤ)
    (ha : (p:ℤ)^2 ∣ 4*a^2+1) (hb : (p:ℤ)^2 ∣ 4*b^2+1) :
    (p:ℤ)^2 ∣ a - b ∨ (p:ℤ)^2 ∣ a + b := by
  have hpz : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  have hn4 : ¬ (p:ℤ) ∣ 4 := by
    intro h
    have h' : p ∣ 4 := by exact_mod_cast h
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2^2 by norm_num; exact h')
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  have hprod : (p:ℤ)^2 ∣ 4*((a-b)*(a+b)) := by
    have : 4*((a-b)*(a+b)) = (4*a^2+1) - (4*b^2+1) := by ring
    rw [this]; exact dvd_sub ha hb
  have hprod' : (p:ℤ)^2 ∣ (a-b)*(a+b) := hpz.pow_dvd_of_dvd_mul_left 2 hn4 hprod
  by_cases h1 : (p:ℤ) ∣ a + b
  · by_cases h2 : (p:ℤ) ∣ a - b
    · exfalso
      have h3 : (p:ℤ) ∣ 2 * a := by
        have : 2 * a = (a+b) + (a-b) := by ring
        rw [this]; exact dvd_add h1 h2
      have hn2 : ¬ (p:ℤ) ∣ 2 := by
        intro h
        have h' : p ∣ 2 := by exact_mod_cast h
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
      have h4 : (p:ℤ) ∣ a := (hpz.dvd_or_dvd h3).resolve_left hn2
      have h5 : (p:ℤ) ∣ 4*a^2 := by
        exact Dvd.dvd.mul_left (dvd_pow h4 (by norm_num)) 4
      have h6 : (p:ℤ) ∣ 4*a^2+1 := dvd_trans (dvd_pow_self _ (by norm_num)) ha
      have h7 : (p:ℤ) ∣ 1 := (dvd_add_right h5).mp h6
      exact hpz.not_dvd_one h7
    · right; exact hpz.pow_dvd_of_dvd_mul_left 2 h2 hprod'
  · left; exact hpz.pow_dvd_of_dvd_mul_right 2 h1 hprod'

private lemma cnt_aux (x q c : ℕ) (hq : 0 < q) :
    ((Finset.range (x+1)).filter (fun k => k ≡ c [MOD q])).card ≤ x / q + 1 := by
  have : ((Finset.range (x+1)).filter (fun k => k ≡ c [MOD q])).card ≤
      (Finset.range (x / q + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun k => k / q)
    · intro k hk
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hk
      simp only [Finset.coe_range, Set.mem_Iio]
      have : k / q ≤ x / q := Nat.div_le_div_right (by omega)
      omega
    · intro k hk k' hk' h
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hk hk'
      have hm : k % q = k' % q := hk.2.trans hk'.2.symm
      simp only at h
      calc k = q * (k / q) + k % q := (Nat.div_add_mod k q).symm
        _ = q * (k' / q) + k' % q := by rw [h, hm]
        _ = k' := Nat.div_add_mod k' q
  simpa using this

private lemma slice_aux (x p : ℕ) (hp : p.Prime) :
    (((Finset.range (x+1)).filter (fun k => 1 ≤ k ∧ p^2 ∣ 4*k^2+1))).card ≤ 2 * (x / p^2 + 1) := by
  by_cases hp2 : p = 2
  · subst hp2
    have : ((Finset.range (x+1)).filter (fun k => 1 ≤ k ∧ 2^2 ∣ 4*k^2+1)) = ∅ := by
      apply Finset.filter_false_of_mem
      intro k _ ⟨_, h⟩
      omega
    rw [this]; simp
  have hq : 0 < p^2 := by positivity [hp.pos]
  by_cases hne : ((Finset.range (x+1)).filter (fun k => 1 ≤ k ∧ p^2 ∣ 4*k^2+1)).Nonempty
  · obtain ⟨k0, hk0⟩ := hne
    simp only [Finset.mem_filter, Finset.mem_range] at hk0
    have hsub : ((Finset.range (x+1)).filter (fun k => 1 ≤ k ∧ p^2 ∣ 4*k^2+1)) ⊆
        ((Finset.range (x+1)).filter (fun k => k ≡ k0 [MOD p^2])) ∪
        ((Finset.range (x+1)).filter (fun k => k ≡ (p^2-1)*k0 [MOD p^2])) := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union] at hk ⊢
      have ha : ((p^2 : ℕ):ℤ) ∣ 4*(k:ℤ)^2+1 := by exact_mod_cast hk.2.2
      have hb : ((p^2 : ℕ):ℤ) ∣ 4*(k0:ℤ)^2+1 := by exact_mod_cast hk0.2.2
      push_cast at ha hb
      rcases two_classes_aux p hp hp2 k k0 ha hb with h | h
      · left
        refine ⟨hk.1, ?_⟩
        apply (Nat.modEq_iff_dvd).mpr
        push_cast
        have : (k0:ℤ) - k = -((k:ℤ) - k0) := by ring
        rw [this]; exact (dvd_neg).mpr h
      · right
        refine ⟨hk.1, ?_⟩
        have h' : p^2 ∣ k + k0 := by
          have : ((p^2 : ℕ):ℤ) ∣ ((k + k0 : ℕ):ℤ) := by push_cast; exact h
          exact_mod_cast this
        have h0 : k + k0 ≡ 0 [MOD p^2] := (Nat.modEq_zero_iff_dvd).mpr h'
        have h1 : k0 + (p^2-1)*k0 ≡ 0 [MOD p^2] := by
          have : k0 + (p^2-1)*k0 = p^2 * k0 := by
            have : 1 ≤ p^2 := hq
            zify [this]; ring
          rw [this]; exact (Nat.modEq_zero_iff_dvd).mpr (dvd_mul_right _ _)
        have h2 : k + k0 ≡ (p^2-1)*k0 + k0 [MOD p^2] := by
          have := h0.trans h1.symm
          simpa [add_comm] using this
        exact Nat.ModEq.add_right_cancel' k0 h2
    calc _ ≤ (((Finset.range (x+1)).filter (fun k => k ≡ k0 [MOD p^2])) ∪
        ((Finset.range (x+1)).filter (fun k => k ≡ (p^2-1)*k0 [MOD p^2]))).card :=
          Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ (x / p^2 + 1) + (x / p^2 + 1) := add_le_add (cnt_aux x _ _ hq) (cnt_aux x _ _ hq)
      _ = _ := by ring
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]; simp

private lemma inv_sq_sum_aux (y M : ℕ) (hy : 1 ≤ y) (hM : y ≤ M) :
    ∑ n ∈ Finset.Ioc y M, (1 : ℝ) / (n:ℝ)^2 ≤ 1 / (y:ℝ) - 1 / (M:ℝ) := by
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [Finset.sum_Ioc_succ_top hM]
    have hM1 : (1:ℝ) ≤ M := by exact_mod_cast (le_trans hy hM)
    have hM0 : (0:ℝ) < M := by linarith
    have : (1:ℝ) / ((M+1 : ℕ):ℝ)^2 ≤ 1 / (M:ℝ) - 1 / ((M+1 : ℕ) : ℝ) := by
      push_cast
      rw [div_sub_div _ _ hM0.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

private lemma inj_aux (x k k' m u v : ℕ) (hk : x / 2 < k) (hk' : k' ≤ x) (hkk : k < k')
    (hm : 0 < m) (hu : 4*k^2+1 = m*u^2) (hv : 4*k'^2+1 = m*v^2) : False := by
  have := pell_spacing_aux m (2*k) (2*k') u v hm (by omega) (by omega)
    (by rw [← hu]; ring) (by rw [← hv]; ring)
  omega

private lemma exists_T_aux (x : ℕ) : ∃ T : ℕ, T^3 ≤ x^2 ∧ x^2 < (T+1)^3 := by
  have h : ∃ s, x^2 < s^3 := ⟨x^2+1, by nlinarith [Nat.zero_le (x^2), Nat.pos_of_ne_zero (show x^2+1 ≠ 0 by omega), pow_pos (Nat.succ_pos (x^2)) 2, Nat.succ_le_succ (Nat.zero_le (x^2))]⟩
  have hs0 : Nat.find h ≠ 0 := by
    intro h0
    have := Nat.find_spec h
    rw [h0] at this; simp at this
  refine ⟨Nat.find h - 1, ?_, ?_⟩
  · have := Nat.find_min h (m := Nat.find h - 1) (by omega)
    exact not_lt.mp this
  · have : Nat.find h - 1 + 1 = Nat.find h := by omega
    rw [this]; exact Nat.find_spec h

theorem Conjectures.QuadraticPrimes.SieveSquareTail :
    let f := fun k : ℕ => 4*k^2+1; let block := fun x : ℕ => Finset.Ioc (x/2) x; let flagged := fun x y : ℕ => (block x).filter (fun k =>
  ((Finset.Ioc y (2*x)).filter (fun p => Nat.Prime p ∧ p^2 ∣ f k)).Nonempty);
    ∃ C : ℝ, 0<C ∧ ∀ x y : ℕ, 2≤x → 2≤y →
  ((flagged x y).card : ℝ) ≤ C*((x : ℝ)/y + (x : ℝ)^(2/3 : ℝ)) := by
  intro f block flagged
  classical
  refine ⟨12, by norm_num, ?_⟩
  intro x y hx hy
  obtain ⟨T, hT1, hT2⟩ := exists_T_aux x
  have hTle : (T:ℝ) ≤ (x:ℝ)^(2/3 : ℝ) := by
    by_contra hcon
    push_neg at hcon
    have hx0 : (0:ℝ) ≤ (x:ℝ)^(2/3 : ℝ) := by positivity
    have h3 : ((x:ℝ)^(2/3 : ℝ))^3 < (T:ℝ)^3 := pow_lt_pow_left₀ hcon hx0 (by norm_num)
    have h4 : ((x:ℝ)^(2/3 : ℝ))^3 = (x:ℝ)^2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    have h5 : (T:ℝ)^3 ≤ (x:ℝ)^2 := by exact_mod_cast hT1
    linarith
  have hx1 : (1:ℝ) ≤ (x:ℝ)^(2/3 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ x)) (by norm_num)
  set A := (block x).filter (fun k => ∃ p, p.Prime ∧ y < p ∧ p ≤ T ∧ p^2 ∣ f k) with hA
  set B := (block x).filter (fun k => ∃ p, p.Prime ∧ T < p ∧ p^2 ∣ f k) with hB
  have hsub : flagged x y ⊆ A ∪ B := by
    intro k hk
    simp only [flagged, block, Finset.mem_filter, Finset.mem_Ioc] at hk
    obtain ⟨hkb, p, hp⟩ := hk
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
    rw [Finset.mem_union]
    by_cases hpT : p ≤ T
    · left
      simp only [hA, block, Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨hkb, p, hp.2.1, hp.1.1, hpT, hp.2.2⟩
    · right
      simp only [hB, block, Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨hkb, p, hp.2.1, by omega, hp.2.2⟩
  -- B bound
  have hBcard : B.card ≤ 5*(T+1) := by
    have hex : ∀ k ∈ B, ∃ m ∈ Finset.Icc 1 (5*(T+1)), ∃ u, f k = m*u^2 ∧ 0 < m := by
      intro k hk
      simp only [hB, block, Finset.mem_filter, Finset.mem_Ioc] at hk
      obtain ⟨⟨hk1, hk2⟩, p, hp, hTp, hdvd⟩ := hk
      obtain ⟨m, hm⟩ := hdvd
      have hfk : f k = 4*k^2+1 := rfl
      have hmpos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [h0] at hm; simp at hm
        · exact h0
      have hp2 : (T+1)^2 ≤ p^2 := Nat.pow_le_pow_left hTp 2
      have hkx : k^2 ≤ x^2 := Nat.pow_le_pow_left hk2 2
      have hx2 : 1 ≤ x^2 := Nat.one_le_pow _ _ (by omega)
      have h1 : m*(T+1)^2 ≤ 5*x^2 := by
        calc m*(T+1)^2 ≤ m*p^2 := Nat.mul_le_mul_left _ hp2
          _ = 4*k^2+1 := by rw [hfk] at hm; rw [hm]; ring
          _ ≤ 5*x^2 := by omega
      have h2 : m*(T+1)^2 < 5*(T+1)*(T+1)^2 := by
        calc m*(T+1)^2 ≤ 5*x^2 := h1
          _ < 5*(T+1)^3 := by omega
          _ = 5*(T+1)*(T+1)^2 := by ring
      have h3 : m < 5*(T+1) := Nat.lt_of_mul_lt_mul_right h2
      refine ⟨m, Finset.mem_Icc.mpr ⟨hmpos, by omega⟩, p, ?_, hmpos⟩
      rw [hfk] at hm ⊢; rw [hm]; ring
    choose! g hg using hex
    calc B.card ≤ (Finset.Icc 1 (5*(T+1))).card := by
          apply Finset.card_le_card_of_injOn g
          · intro k hk; exact (hg k hk).1
          · intro k hk k' hk' hgg
            by_contra hne
            obtain ⟨_, u, hu, hmpos⟩ := hg k hk
            obtain ⟨_, v, hv, _⟩ := hg k' hk'
            simp only [hB, block, Finset.coe_filter, Finset.mem_Ioc, Set.mem_setOf_eq] at hk hk'
            rw [hgg] at hu hmpos
            rcases lt_or_gt_of_ne hne with h | h
            · exact inj_aux x k k' (g k') u v hk.1.1 hk'.1.2 h hmpos hu hv
            · exact inj_aux x k' k (g k') v u hk'.1.1 hk.1.2 h hmpos hv hu
      _ = 5*(T+1) := by simp
  -- A bound
  have hAcard : A.card ≤ ∑ n ∈ Finset.Ioc y T, 2 * (x / n^2 + 1) := by
    have hsubA : A ⊆ (((Finset.Ioc y T).filter Nat.Prime)).biUnion
        (fun p => (Finset.range (x+1)).filter (fun k => 1 ≤ k ∧ p^2 ∣ 4*k^2+1)) := by
      intro k hk
      simp only [hA, block, Finset.mem_filter, Finset.mem_Ioc] at hk
      obtain ⟨⟨hk1, hk2⟩, p, hp, hyp, hpT, hdvd⟩ := hk
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]
      refine ⟨p, ⟨⟨hyp, hpT⟩, hp⟩, by omega, by omega, hdvd⟩
    calc A.card ≤ _ := Finset.card_le_card hsubA
      _ ≤ ∑ p ∈ (Finset.Ioc y T).filter Nat.Prime,
          ((Finset.range (x+1)).filter (fun k => 1 ≤ k ∧ p^2 ∣ 4*k^2+1)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ p ∈ (Finset.Ioc y T).filter Nat.Prime, 2 * (x / p^2 + 1) := by
          apply Finset.sum_le_sum
          intro p hp
          exact slice_aux x p (Finset.mem_filter.mp hp).2
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hsumR : ((∑ n ∈ Finset.Ioc y T, 2 * (x / n^2 + 1) : ℕ) : ℝ) ≤ 2 * ((x:ℝ)/y) + 2 * T := by
    push_cast
    have hcard : ((Finset.Ioc y T).card : ℝ) ≤ T := by
      have : (Finset.Ioc y T).card ≤ T := by simp
      exact_mod_cast this
    have h1 : ∀ n ∈ Finset.Ioc y T, (2 * (((x / n^2 : ℕ) : ℝ) + 1)) ≤
        2 * ((x:ℝ) * (1 / (n:ℝ)^2)) + 2 := by
      intro n hn
      have hn0 : (0:ℝ) < (n:ℝ)^2 := by
        have : 0 < n := by simp [Finset.mem_Ioc] at hn; omega
        positivity
      have : ((x / n^2 : ℕ) : ℝ) ≤ (x:ℝ) / (n:ℝ)^2 := by
        have := Nat.cast_div_le (α := ℝ) (m := x) (n := n^2)
        simpa using this
      rw [mul_one_div]
      linarith
    calc ∑ n ∈ Finset.Ioc y T, 2 * (((x / n^2 : ℕ) : ℝ) + 1)
        ≤ ∑ n ∈ Finset.Ioc y T, (2 * ((x:ℝ) * (1 / (n:ℝ)^2)) + 2) := Finset.sum_le_sum h1
      _ = 2 * ((x:ℝ) * ∑ n ∈ Finset.Ioc y T, 1 / (n:ℝ)^2) + 2 * (Finset.Ioc y T).card := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          simp; ring
      _ ≤ 2 * ((x:ℝ) / y) + 2 * T := by
          have hx0 : (0:ℝ) ≤ x := by positivity
          have hs : ∑ n ∈ Finset.Ioc y T, 1 / (n:ℝ)^2 ≤ 1 / (y:ℝ) := by
            by_cases hyT : y ≤ T
            · have := inv_sq_sum_aux y T (by omega) hyT
              have : (0:ℝ) ≤ 1 / (T:ℝ) := by positivity
              linarith
            · rw [Finset.Ioc_eq_empty (by omega)]; simp
          have := mul_le_mul_of_nonneg_left hs hx0
          rw [mul_one_div] at this
          linarith
  have htot : (flagged x y).card ≤ A.card + B.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hAR : (A.card : ℝ) ≤ 2 * ((x:ℝ)/y) + 2 * T :=
    le_trans (by exact_mod_cast hAcard) hsumR
  have hBR : (B.card : ℝ) ≤ 5*((T:ℝ)+1) := by exact_mod_cast hBcard
  have htotR : ((flagged x y).card : ℝ) ≤ A.card + B.card := by exact_mod_cast htot
  have hxy : (0:ℝ) ≤ (x:ℝ)/y := by positivity
  nlinarith

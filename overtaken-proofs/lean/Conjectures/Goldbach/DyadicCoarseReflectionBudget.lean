import Mathlib

private theorem kernelCriterionRF :
∀ (k : ℕ) (χ : DirichletCharacter ℂ (2^(k+1))), 1 ≤ k →
  (χ.IsPrimitive ↔ χ ((1 + 2^k : ℕ) : ZMod (2^(k+1))) = -1) := by
  intro k χ hk
  haveI : NeZero (2^(k+1)) := ⟨by positivity⟩
  have hd : 2^k ∣ 2^(k+1) := pow_dvd_pow 2 (Nat.le_succ k)
  have hlt : 1 < 2^k := by
    calc (1:ℕ) < 2^1 := by norm_num
      _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hk
  have hodd : Odd (1 + 2^k) := by
    rw [add_comm, Nat.odd_add_one, Nat.not_odd_iff_even]
    exact ⟨2^(k-1), by rw [← two_mul, ← pow_succ', Nat.sub_add_cancel hk]⟩
  have hcop : Nat.Coprime (1 + 2^k) (2^(k+1)) :=
    Nat.Coprime.pow_right (k+1) hodd.coprime_two_right
  have hker : ∀ x : (ZMod (2^(k+1)))ˣ, ZMod.unitsMap hd x = 1 →
      (x : ZMod (2^(k+1))) = 1 ∨
        (x : ZMod (2^(k+1))) = ((1 + 2^k : ℕ) : ZMod (2^(k+1))) := by
    intro x hx
    have hcast : (((x : ZMod (2^(k+1))).cast : ZMod (2^k))) = 1 := by
      have h := congrArg (fun y : (ZMod (2^k))ˣ => (y : ZMod (2^k))) hx
      simpa [ZMod.unitsMap_val] using h
    set a : ℕ := (x : ZMod (2^(k+1))).val with ha
    have haval : (a : ZMod (2^(k+1))) = (x : ZMod (2^(k+1))) := by
      rw [ha]
      exact ZMod.natCast_zmod_val _
    have hamod : a % 2^k = 1 := by
      have h1 : (a : ZMod (2^k)) = 1 := by
        rw [← ZMod.cast_natCast hd a, haval]
        exact hcast
      have h2 : a ≡ 1 [MOD 2^k] := (ZMod.natCast_eq_natCast_iff a 1 (2^k)).mp (by simpa using h1)
      simpa [Nat.ModEq, Nat.mod_eq_of_lt hlt] using h2
    have haeq : a = 2^k * (a / 2^k) + 1 := by
      have h := Nat.div_add_mod a (2^k)
      rw [hamod] at h
      omega
    have hq : a / 2^k < 2 := by
      have halt : a < 2^k * 2 := by
        have h := ZMod.val_lt (x : ZMod (2^(k+1)))
        rw [← ha, pow_succ] at h
        exact h
      have h1 : 2^k * (a / 2^k) < 2^k * 2 := by omega
      exact Nat.lt_of_mul_lt_mul_left h1
    have hq2 : a / 2^k = 0 ∨ a / 2^k = 1 := by
      rcases Nat.eq_zero_or_pos (a / 2^k) with h0 | hpos
      · exact Or.inl h0
      · exact Or.inr (by omega)
    rcases hq2 with h0 | h1
    · left
      rw [← haval, haeq, h0, mul_zero, zero_add]
      norm_num
    · right
      rw [← haval, haeq, h1, mul_one]
      norm_num [Nat.add_comm]
  have hfac_iff : χ.FactorsThrough (2^k) ↔
      χ ((1 + 2^k : ℕ) : ZMod (2^(k+1))) = 1 := by
    have hu : ZMod.unitsMap hd (ZMod.unitOfCoprime (1 + 2^k) hcop) = 1 := by
      refine Units.ext ?_
      rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, Units.val_one, ZMod.cast_natCast hd]
      rw [Nat.cast_add, Nat.cast_one]
      have h : (((2:ℕ)^k : ℕ) : ZMod (2^k)) = 0 := ZMod.natCast_self _
      rw [h]
      ring
    constructor
    · intro hf
      have hker' := (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).mp hf
      have hmem : χ.toUnitHom (ZMod.unitOfCoprime (1 + 2^k) hcop) = 1 :=
        MonoidHom.mem_ker.mp (hker' (MonoidHom.mem_ker.mpr hu))
      have h := congrArg (fun y : ℂˣ => (y : ℂ)) hmem
      simpa [MulChar.coe_toUnitHom, ZMod.coe_unitOfCoprime] using h
    · intro hv
      rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
      intro x hx
      apply MonoidHom.mem_ker.mpr
      apply Units.ext
      rw [MulChar.coe_toUnitHom, Units.val_one]
      rcases hker x (MonoidHom.mem_ker.mp hx) with h | h
      · rw [h]
        exact MulChar.map_one χ
      · rw [h, hv]
  constructor
  ·
    intro hprim
    have hne : ¬ χ.FactorsThrough (2^k) := by
      intro hf
      have hmem : 2^k ∈ χ.conductorSet := (DirichletCharacter.mem_conductorSet_iff χ).mpr hf
      have hdvd : χ.conductor ∣ 2^k :=
        (DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ hd).mp hmem
      rw [(DirichletCharacter.isPrimitive_def χ).mp hprim] at hdvd
      have hle : k + 1 ≤ k := (Nat.pow_dvd_pow_iff_le_right (x := 2) (by norm_num)).mp hdvd
      omega
    have hne1 : χ ((1 + 2^k : ℕ) : ZMod (2^(k+1))) ≠ 1 := fun h => hne (hfac_iff.mpr h)
    have hsq : χ ((1 + 2^k : ℕ) : ZMod (2^(k+1))) ^ 2 = 1 := by
      have hkey : (((1 + 2^k : ℕ) : ZMod (2^(k+1))) ^ 2) = 1 := by
        have hnat : (1 + 2^k : ℕ) ^ 2 = 1 + 2^(k+1) * (1 + 2^(k-1)) := by
          have hm : 2 * 2^(k-1) = 2^k := by rw [← pow_succ', Nat.sub_add_cancel hk]
          have hA : 2^(k+1) = 2 * 2^k := pow_succ' 2 k
          nlinarith
        calc (((1 + 2^k : ℕ) : ZMod (2^(k+1))) ^ 2)
            = (((1 + 2^k : ℕ) ^ 2 : ℕ) : ZMod (2^(k+1))) := (Nat.cast_pow _ _).symm
          _ = ((1 + 2^(k+1) * (1 + 2^(k-1)) : ℕ) : ZMod (2^(k+1))) := by rw [hnat]
          _ = 1 := by
            rw [Nat.cast_add, Nat.cast_one, Nat.cast_mul]
            have h : (((2:ℕ)^(k+1) : ℕ) : ZMod (2^(k+1))) = 0 := ZMod.natCast_self _
            rw [h]
            ring
      calc χ ((1 + 2^k : ℕ) : ZMod (2^(k+1))) ^ 2
          = χ (((1 + 2^k : ℕ) : ZMod (2^(k+1))) ^ 2) := (map_pow χ _ 2).symm
        _ = χ 1 := by rw [hkey]
        _ = 1 := MulChar.map_one χ
    rcases (sq_eq_one_iff.mp hsq) with h | h
    · exact absurd h hne1
    · exact h
  ·
    intro hv
    rw [DirichletCharacter.isPrimitive_def]
    have hnot : ¬ χ.FactorsThrough (2^k) := by
      intro hf
      have h1 : χ ((1 + 2^k : ℕ) : ZMod (2^(k+1))) = 1 := hfac_iff.mp hf
      rw [hv] at h1
      norm_num at h1
    have hdvd : χ.conductor ∣ 2^(k+1) := DirichletCharacter.conductor_dvd_level χ
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp hdvd
    rw [hjeq]
    by_cases hjk : j = k + 1
    · rw [hjk]
    · exfalso
      have hjk' : j ≤ k := by omega
      have hdvd' : χ.conductor ∣ 2^k := by
        rw [hjeq]
        exact (Nat.pow_dvd_pow_iff_le_right (x := 2) (by norm_num)).mpr hjk'
      exact hnot ((DirichletCharacter.mem_conductorSet_iff χ).mp
        ((DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ hd).mpr hdvd'))


private theorem extendUnitsRF {m : ℕ} [NeZero m] {β : Type*} [AddCommMonoid β]
    (f : ZMod m → β) (h : ∀ x, ¬IsUnit x → f x = 0) :
    (∑ x : (ZMod m)ˣ, f (x:ZMod m)) = ∑ x, f x :=
  Fintype.sum_of_injective _ Units.val_injective _ _ (fun i hi => h i (fun ⟨u,hu⟩ => hi ⟨u,hu⟩)) (fun _ => rfl)



private theorem kernelSumRF (m : ℕ) [NeZero m] (a b : ZMod m) :
    (∑ χ : DirichletCharacter ℂ m, star (χ a) * χ b) =
      if IsUnit a ∧ a=b then (m.totient : ℂ) else 0 := by
  classical
  by_cases ha : IsUnit a
  · have h (χ : DirichletCharacter ℂ m) : star (χ a) = χ a⁻¹ := by
      obtain ⟨u,rfl⟩ := ha
      rw [MulChar.star_apply',MulChar.inv_apply,ZMod.inv_coe_unit,Ring.inverse_unit]
    simp_rw [h]
    simpa [ha] using DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha b
  · simp [MulChar.map_nonunit _ ha,ha]

private theorem unitRangeRF {m : ℕ} [NeZero m] {β : Type*} [AddCommMonoid β] (w : ZMod m → β)
    (hw : ∀ x, ¬IsUnit x → w x = 0) :
    (∑ x : (ZMod m)ˣ, w x) = ∑ j ∈ Finset.range m, w (j:ZMod m) := by
  rw [extendUnitsRF w hw, ← Fin.sum_univ_eq_sum_range]
  let e : Fin m ≃ ZMod m := {
    toFun := fun x => (x.val : ZMod m)
    invFun := fun x => ⟨x.val,ZMod.val_lt x⟩
    left_inv := fun x => Fin.ext (ZMod.val_natCast_of_lt x.isLt)
    right_inv := fun x => ZMod.natCast_zmod_val x }
  exact (e.sum_comp w).symm

private theorem pickRF {m : ℕ} [NeZero m] (y : ZMod m) (g : ZMod m → ℂ) :
    (∑ a : (ZMod m)ˣ, g a * (if y = (a : ZMod m) then 1 else 0)) = if IsUnit y then g y else 0 := by
  by_cases hy : IsUnit y
  · obtain ⟨u, rfl⟩ := hy
    simp only [mul_ite, mul_one, mul_zero, Units.val_inj]
    rw [Finset.sum_ite_eq]
    simp
  · rw [if_neg hy]
    apply Finset.sum_eq_zero
    intro a _
    have : y ≠ (a : ZMod m) := fun h => hy (h ▸ a.isUnit)
    simp [this]

private theorem pickRF' {m : ℕ} [NeZero m] (y : ZMod m) (g : ZMod m → ℂ) :
    (∑ a : (ZMod m)ˣ, g a * (if (a : ZMod m) = y then 1 else 0)) = if IsUnit y then g y else 0 := by
  rw [← pickRF y g]
  apply Finset.sum_congr rfl
  intro a _
  simp only [eq_comm (a := y)]

private theorem sliceRF (N q m r : ℕ) [NeZero m] (hm : m = 2 * q) (hq : 0 < q) (hr : r < q)
    (f : ZMod m → ℝ) :
    f ((N : ZMod m) - (r : ZMod m)) -
        f ((N : ZMod m) - (r : ZMod m) + (q : ZMod m)) =
      (if (N + 2 * q - r) % (2 * q) < q then (1 : ℝ) else -1) *
        (f (((N + q - r) % q : ℕ) : ZMod m) -
          f ((((N + q - r) % q + q : ℕ)) : ZMod m)) := by
  subst hm
  have qzero : (q : ZMod (2 * q)) + (q : ZMod (2 * q)) = 0 := by
    rw [← Nat.cast_add, ← two_mul, ZMod.natCast_self]
  have hdef : N + 2 * q - r = (N + q - r) + q := by omega
  have hmod : (N + 2 * q - r) % q = (N + q - r) % q := by
    rw [hdef, Nat.add_mod_right]
  have htlt : (N + 2 * q - r) % (2 * q) < 2 * q := Nat.mod_lt _ (by omega)
  have hcast : (N : ZMod (2 * q)) - (r : ZMod (2 * q)) = (((N + 2 * q - r) % (2 * q) : ℕ) : ZMod (2 * q)) := by
    rw [ZMod.natCast_mod, Nat.cast_sub (by omega)]
    have : ((2 * q : ℕ) : ZMod (2 * q)) = 0 := ZMod.natCast_self _
    push_cast at this ⊢
    linear_combination (-1 : ZMod (2 * q)) * this
  rw [hcast]
  set t := (N + 2 * q - r) % (2 * q) with ht
  set r' := (N + q - r) % q with hr'
  by_cases h : t < q
  · have : t % q = t := Nat.mod_eq_of_lt h
    have htr : t = r' := by
      have h2 : t % q = r' := by
        rw [← hmod]; rw [ht, Nat.mod_mod_of_dvd _ (dvd_mul_left q 2)]
      omega
    rw [if_pos h, htr]
    push_cast
    ring
  · push_cast at h
    have htr : t = r' + q := by
      have h2 : t % q = r' := by
        rw [← hmod]; rw [ht, Nat.mod_mod_of_dvd _ (dvd_mul_left q 2)]
      have h3 : t % q = t - q := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    rw [if_neg h, htr]
    have e : (((r' + q : ℕ) : ZMod (2 * q)) + (q : ZMod (2 * q))) = (r' : ZMod (2 * q)) := by
      push_cast
      linear_combination qzero
    push_cast
    rw [show ((r' : ZMod (2 * q)) + q + q) = r' by linear_combination qzero]
    ring

set_option maxHeartbeats 1000000 in
private theorem primFormRF :
    ∀ (N k : ℕ), Even N → 1 ≤ k →
  let q : ℕ := 2^k
  let m : ℕ := 2^(k+1)
  ∀ f : ZMod m → ℝ,
    let D := fun r : ℕ => f (r : ZMod m) - f ((r+q : ℕ) : ZMod m)
    let s := (Finset.univ : Finset (DirichletCharacter ℂ m)).filter (fun χ => χ.conductor = m)
    let v := fun χ : DirichletCharacter ℂ m =>
      (∑ x : (ZMod m)ˣ, (f (x : ZMod m) : ℂ) * star (χ (x : ZMod m))) /
        (Real.sqrt (m.totient : ℝ) : ℂ)
    let H := fun χ ψ : DirichletCharacter ℂ m =>
      (∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ ((N : ZMod m) - (x : ZMod m))) / (m.totient : ℂ)
    (∑ r ∈ (Finset.range q).filter (fun r => Odd r),
      (if (N+2*q-r) % (2*q) < q then (1 : ℝ) else -1) * D r * D ((N+q-r) % q)) =
      2 * (∑ χ ∈ s, ∑ ψ ∈ s, star (v χ) * H χ ψ * v ψ).re := by
  classical
  intro N k hN hk q m f D s v H
  have hm : m = q + q := by dsimp [m, q]; rw [pow_succ]; omega
  have hq0 : 0 < q := by dsimp [q]; positivity
  haveI : NeZero m := ⟨by dsimp [m]; positivity⟩
  let T : ZMod m := ((1 + q : ℕ) : ZMod m)
  let S := (Finset.range q).filter Odd
  have evenq : Even q := by exact even_two.pow_of_ne_zero (by omega : k ≠ 0)
  have unitOdd (r : ℕ) : IsUnit (r : ZMod m) ↔ Odd r := by
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (by omega : 0 < k + 1), Nat.coprime_two_right]
  have qzero : (q : ZMod m) + (q : ZMod m) = 0 := by
    rw [← Nat.cast_add, ← hm, ZMod.natCast_self]
  have shift (r : ℕ) (hr : Odd r) : ((r + q : ℕ) : ZMod m) = T * r := by
    obtain ⟨j, hj⟩ := hr
    have er : (r : ZMod m) = 2 * (j : ZMod m) + 1 := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using
        congrArg (fun x : ℕ => (x : ZMod m)) hj
    dsimp [T]; push_cast; rw [er]; linear_combination -(j : ZMod m) * qzero
  have hsquare : T * T = 1 := by
    have term : (q : ZMod m) * (q : ZMod m) = 0 := by
      obtain ⟨j, hj⟩ := evenq
      have ej : (q : ZMod m) = (j : ZMod m) + (j : ZMod m) := by
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using
          congrArg (fun x : ℕ => (x : ZMod m)) hj
      calc _ = (q : ZMod m) * ((j : ZMod m) + j) := congrArg _ ej
           _ = _ := by linear_combination (j : ZMod m) * qzero
    dsimp [T]; push_cast; linear_combination term + qzero
  have sign (χ : DirichletCharacter ℂ m) : χ T = if χ ∈ s then -1 else 1 := by
    have prim : χ ∈ s ↔ χ.IsPrimitive := by simp [s, DirichletCharacter.isPrimitive_def]
    by_cases hc : χ ∈ s
    · rw [if_pos hc]; exact (kernelCriterionRF k χ hk).mp (prim.mp hc)
    · rw [if_neg hc]
      have sqχ : χ T ^ 2 = 1 := by rw [sq, ← map_mul, hsquare, map_one]
      exact (sq_eq_one_iff.mp sqχ).resolve_right
        (fun h => hc (prim.mpr ((kernelCriterionRF k χ hk).mpr h)))
  have hTunit : IsUnit T := ⟨⟨T, T, hsquare, hsquare⟩, rfl⟩
  have shiftU (y : ZMod m) (hy : IsUnit y) : y + (q : ZMod m) = T * y := by
    have hy' : (y.val : ZMod m) = y := ZMod.natCast_zmod_val y
    have hodd : Odd y.val := by rw [← unitOdd, hy']; exact hy
    have := shift y.val hodd
    push_cast at this
    rw [hy'] at this
    exact this
  have hsum : ∀ g : DirichletCharacter ℂ m → ℂ,
      ∑ ψ ∈ s, g ψ = ∑ ψ, if ψ ∈ s then g ψ else 0 := by
    intro g
    simp only [s, Finset.sum_filter, Finset.mem_filter, Finset.mem_univ, true_and]
  have K (j y : ZMod m) (hj : IsUnit j) :
      (∑ ψ ∈ s, star (ψ j) * ψ y) =
        (m.totient : ℂ) / 2 * ((if j = y then 1 else 0) - (if T * j = y then 1 else 0)) := by
    have twice : 2 * (∑ ψ ∈ s, star (ψ j) * ψ y) =
        (∑ ψ : DirichletCharacter ℂ m, star (ψ j) * ψ y) -
          ∑ ψ : DirichletCharacter ℂ m, star (ψ (T * j)) * ψ y := by
      rw [hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro ψ _
      rw [map_mul, sign]
      by_cases hh : ψ ∈ s <;> simp [hh] <;> ring
    rw [kernelSumRF, kernelSumRF] at twice
    have h2 : IsUnit (T * j) := hTunit.mul hj
    simp only [hj, h2, true_and] at twice
    have hne : (2 : ℂ) ≠ 0 := two_ne_zero
    apply mul_left_cancel₀ hne
    rw [twice]
    split_ifs <;> ring
  have hφ : (m.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos m)).ne'
  obtain ⟨ca, hca⟩ : ∃ ca : ℂ, ca = ((Real.sqrt (m.totient : ℝ) : ℝ) : ℂ) := ⟨_, rfl⟩
  have hca2 : ca * ca = (m.totient : ℂ) := by
    rw [hca, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; simp
  have hca0 : ca ≠ 0 := by intro h; apply hφ; rw [← hca2, h, zero_mul]
  obtain ⟨SA, hSA⟩ : ∃ SA : DirichletCharacter ℂ m → ℂ,
      ∀ χ, SA χ = ∑ a : (ZMod m)ˣ, (f a : ℂ) * χ a := ⟨_, fun _ => rfl⟩
  obtain ⟨SB, hSB⟩ : ∃ SB : DirichletCharacter ℂ m → ℂ,
      ∀ ψ, SB ψ = ∑ b : (ZMod m)ˣ, (f b : ℂ) * star (ψ b) := ⟨_, fun _ => rfl⟩
  have hv (ψ : DirichletCharacter ℂ m) : v ψ = ca⁻¹ * SB ψ := by
    rw [hSB, hca]; simp only [v]; rw [div_eq_inv_mul]
  have hsv (χ : DirichletCharacter ℂ m) : star (v χ) = ca⁻¹ * SA χ := by
    rw [hv, hSB, hSA, hca]
    simp [star_sum, star_mul', Complex.star_def]
  have hH (χ ψ : DirichletCharacter ℂ m) : H χ ψ =
      (m.totient : ℂ)⁻¹ * ∑ x : (ZMod m)ˣ, star (χ x) * ψ ((N : ZMod m) - x) := by
    simp only [H]; rw [div_eq_inv_mul]
  have e1 : ∀ χ ψ : DirichletCharacter ℂ m, star (v χ) * H χ ψ * v ψ =
      (ca⁻¹ * ca⁻¹ * (m.totient : ℂ)⁻¹) *
        ∑ x : (ZMod m)ˣ, (SA χ * star (χ x)) * (ψ ((N : ZMod m) - x) * SB ψ) := by
    intro χ ψ
    rw [hsv, hv, hH]
    generalize SA χ = A
    generalize SB ψ = B
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hF : (∑ χ ∈ s, ∑ ψ ∈ s, star (v χ) * H χ ψ * v ψ) =
      (ca⁻¹ * ca⁻¹ * (m.totient : ℂ)⁻¹) * ∑ x : (ZMod m)ˣ,
        (∑ χ ∈ s, SA χ * star (χ x)) * (∑ ψ ∈ s, ψ ((N : ZMod m) - x) * SB ψ) := by
    simp only [e1]
    simp only [← Finset.mul_sum]
    congr 1
    calc _ = ∑ χ ∈ s, ∑ x : (ZMod m)ˣ, ∑ ψ ∈ s,
          (SA χ * star (χ x)) * (ψ ((N : ZMod m) - x) * SB ψ) :=
          Finset.sum_congr rfl (fun χ _ => Finset.sum_comm)
      _ = ∑ x : (ZMod m)ˣ, ∑ χ ∈ s, ∑ ψ ∈ s,
          (SA χ * star (χ x)) * (ψ ((N : ZMod m) - x) * SB ψ) := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl (fun x _ => by rw [Finset.sum_mul_sum])
  have hP (x : (ZMod m)ˣ) : (∑ χ ∈ s, SA χ * star (χ x)) =
      (m.totient : ℂ) / 2 * ((f x : ℂ) - (f (T * x) : ℂ)) := by
    have hTx : IsUnit (T * (x : ZMod m)) := hTunit.mul x.isUnit
    calc (∑ χ ∈ s, SA χ * star (χ x))
        = ∑ χ ∈ s, ∑ a : (ZMod m)ˣ, (f a : ℂ) * (star (χ x) * χ a) := by
          apply Finset.sum_congr rfl
          intro χ _
          rw [hSA, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro a _
          ring
      _ = ∑ a : (ZMod m)ˣ, (f a : ℂ) * ∑ χ ∈ s, star (χ x) * χ a := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
      _ = ∑ a : (ZMod m)ˣ, (m.totient : ℂ) / 2 *
            ((f a : ℂ) * (if (x : ZMod m) = a then 1 else 0) -
              (f a : ℂ) * (if T * (x : ZMod m) = a then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [K x a x.isUnit]
          ring
      _ = _ := by
          rw [← Finset.mul_sum, Finset.sum_sub_distrib]
          rw [pickRF (x : ZMod m) (fun y => (f y : ℂ)), pickRF (T * (x : ZMod m)) (fun y => (f y : ℂ))]
          simp [x.isUnit, hTx]
  have hNunit (x : ZMod m) (hx : IsUnit x) : IsUnit ((N : ZMod m) - x) := by
    have hy' : (x.val : ZMod m) = x := ZMod.natCast_zmod_val x
    have hodd : Odd x.val := (unitOdd _).mp (by rw [hy']; exact hx)
    have hlt := ZMod.val_lt x
    have h1 : (N : ZMod m) - x = ((N + (m - x.val) : ℕ) : ZMod m) := by
      rw [Nat.cast_add, Nat.cast_sub hlt.le, ZMod.natCast_self, hy']; ring
    rw [h1, unitOdd]
    obtain ⟨c, hc⟩ := hN
    rw [Nat.odd_iff] at hodd ⊢
    omega
  have hQ (x : (ZMod m)ˣ) : (∑ ψ ∈ s, ψ ((N : ZMod m) - x) * SB ψ) =
      (m.totient : ℂ) / 2 * ((f ((N : ZMod m) - x) : ℂ) - (f (T * ((N : ZMod m) - x)) : ℂ)) := by
    have hy := hNunit x x.isUnit
    have hTy : IsUnit (T * ((N : ZMod m) - x)) := hTunit.mul hy
    calc (∑ ψ ∈ s, ψ ((N : ZMod m) - x) * SB ψ)
        = ∑ ψ ∈ s, ∑ b : (ZMod m)ˣ, (f b : ℂ) * (star (ψ b) * ψ ((N : ZMod m) - x)) := by
          apply Finset.sum_congr rfl
          intro ψ _
          rw [hSB, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          ring
      _ = ∑ b : (ZMod m)ˣ, (f b : ℂ) * ∑ ψ ∈ s, star (ψ b) * ψ ((N : ZMod m) - x) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
      _ = ∑ b : (ZMod m)ˣ, (m.totient : ℂ) / 2 *
            ((f b : ℂ) * (if (b : ZMod m) = (N : ZMod m) - x then 1 else 0) -
              (f b : ℂ) * (if (b : ZMod m) = T * ((N : ZMod m) - x) then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro b _
          rw [K b ((N : ZMod m) - x) b.isUnit]
          have hcond : (T * (b : ZMod m) = (N : ZMod m) - x) ↔
              ((b : ZMod m) = T * ((N : ZMod m) - x)) := by
            constructor
            · intro h
              rw [← h, ← mul_assoc, hsquare, one_mul]
            · intro h
              rw [h, ← mul_assoc, hsquare, one_mul]
          rw [if_congr hcond rfl rfl]
          ring
      _ = _ := by
          rw [← Finset.mul_sum, Finset.sum_sub_distrib]
          rw [pickRF' ((N : ZMod m) - (x : ZMod m)) (fun y => (f y : ℂ)),
            pickRF' (T * ((N : ZMod m) - (x : ZMod m))) (fun y => (f y : ℂ))]
          simp [hy, hTy]
  obtain ⟨Dt, hDt⟩ : ∃ Dt : ZMod m → ℝ, ∀ y, Dt y = f y - f (y + (q : ZMod m)) :=
    ⟨_, fun _ => rfl⟩
  have hDtq : ∀ y, Dt (y + (q : ZMod m)) = - Dt y := by
    intro y
    have h : y + (q : ZMod m) + (q : ZMod m) = y := by linear_combination qzero
    rw [hDt, hDt, h]; ring
  have hDtq2 : ∀ y, Dt ((N : ZMod m) - (y + (q : ZMod m))) = - Dt ((N : ZMod m) - y) := by
    intro y
    have h : (N : ZMod m) - (y + (q : ZMod m)) = ((N : ZMod m) - y) + (q : ZMod m) := by
      linear_combination (-1 : ZMod m) * qzero
    rw [h, hDtq]
  have hterm (x : (ZMod m)ˣ) :
      (m.totient : ℂ) / 2 * ((f x : ℂ) - (f (T * x) : ℂ)) *
        ((m.totient : ℂ) / 2 * ((f ((N : ZMod m) - x) : ℂ) - (f (T * ((N : ZMod m) - x)) : ℂ))) =
      (m.totient : ℂ) ^ 2 / 4 * ((Dt x * Dt ((N : ZMod m) - x) : ℝ) : ℂ) := by
    rw [← shiftU _ x.isUnit, ← shiftU _ (hNunit _ x.isUnit), hDt, hDt]
    push_cast
    ring
  have hFR : (∑ χ ∈ s, ∑ ψ ∈ s, star (v χ) * H χ ψ * v ψ) =
      (((∑ x : (ZMod m)ˣ, Dt x * Dt ((N : ZMod m) - x)) / 4 : ℝ) : ℂ) := by
    rw [hF]
    simp only [hP, hQ, hterm]
    rw [← Finset.mul_sum]
    push_cast
    have hc : ca⁻¹ * ca⁻¹ * (m.totient : ℂ)⁻¹ * ((m.totient : ℂ) ^ 2 / 4) = 1 / 4 := by
      rw [← hca2]
      field_simp
    rw [← mul_assoc, hc]
    ring
  have hR : (∑ x : (ZMod m)ˣ, Dt x * Dt ((N : ZMod m) - x)) =
      2 * ∑ r ∈ S, Dt (r : ZMod m) * Dt ((N : ZMod m) - r) := by
    obtain ⟨w, hw⟩ : ∃ w : ZMod m → ℝ,
        ∀ x, w x = if IsUnit x then Dt x * Dt ((N : ZMod m) - x) else 0 := ⟨_, fun _ => rfl⟩
    have h1 : (∑ x : (ZMod m)ˣ, Dt x * Dt ((N : ZMod m) - x)) = ∑ x : (ZMod m)ˣ, w x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [hw, if_pos x.isUnit]
    have hrange : Finset.range m = Finset.range (q + q) := by rw [hm]
    rw [h1, unitRangeRF w (fun x hx => by rw [hw, if_neg hx]), hrange, Finset.sum_range_add,
      ← Finset.sum_add_distrib, Finset.mul_sum]
    simp only [S, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    by_cases hr : Odd r
    · have hqr : Odd (q + r) := Even.add_odd evenq hr
      rw [if_pos hr, hw, hw, if_pos ((unitOdd r).mpr hr), if_pos ((unitOdd (q + r)).mpr hqr)]
      have e : ((q + r : ℕ) : ZMod m) = (r : ZMod m) + (q : ZMod m) := by
        push_cast; ring
      rw [e, hDtq, hDtq2]
      ring
    · have hr' : ¬Odd (q + r) := fun h => hr (by
        obtain ⟨j, hj⟩ := evenq
        obtain ⟨u, hu⟩ := h
        exact Nat.odd_iff.mpr (by omega))
      rw [if_neg hr, hw, hw, if_neg (fun h => hr ((unitOdd r).mp h)),
        if_neg (fun h => hr' ((unitOdd (q + r)).mp h))]
      ring
  have hm2 : m = 2 * q := by omega
  have hL : (∑ r ∈ (Finset.range q).filter (fun r => Odd r),
      (if (N+2*q-r) % (2*q) < q then (1 : ℝ) else -1) * D r * D ((N+q-r) % q)) =
      ∑ r ∈ S, Dt (r : ZMod m) * Dt ((N : ZMod m) - r) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hrq := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    have h := sliceRF N q m r hm2 hq0 hrq f
    rw [hDt, hDt, h]
    simp only [D]
    push_cast
    ring
  rw [hL, hFR, Complex.ofReal_re, hR]
  ring

open scoped Classical in
private lemma rcc_totient_pos_real {m : ℕ} [NeZero m] : (0 : ℝ) < (m.totient : ℝ) := by
  exact_mod_cast Nat.totient_pos.mpr (NeZero.pos m)

open scoped Classical in
private lemma rcc_totient_cast {m : ℕ} [NeZero m] : ((m.totient : ℕ) : ℂ) = ((m.totient : ℝ) : ℂ) := by
  simp

open scoped Classical in
private lemma rcc_star_mul_self (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]

open scoped Classical in
private lemma rcc_sum_interchange {α β : Type*} [Fintype α] [Fintype β] {M : Type*} [AddCommMonoid M]
    (f : α → β → M) : (∑ a : α, ∑ b : β, f a b) = ∑ b : β, ∑ a : α, f a b := by
  conv_lhs => rw [Finset.sum_comm]

open scoped Classical in
private lemma rcc_sum_units_eq_sum {m : ℕ} [NeZero m] {M : Type*} [AddCommMonoid M] (f : ZMod m → M)
    (hf : ∀ a, ¬IsUnit a → f a = 0) :
    ∑ x : (ZMod m)ˣ, f (x : ZMod m) = ∑ a : ZMod m, f a := by
  classical
  have key : ∀ a : ZMod m,
      a ∈ (Finset.univ : Finset (ZMod m)ˣ).map ⟨((↑) : (ZMod m)ˣ → ZMod m), Units.val_injective⟩
        ↔ IsUnit a := by
    intro a
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, rfl⟩
      exact x.isUnit
    · intro h
      exact ⟨h.unit, by simpa using h.unit_spec⟩
  have hmap : ∑ a ∈ (Finset.univ : Finset (ZMod m)ˣ).map
        ⟨((↑) : (ZMod m)ˣ → ZMod m), Units.val_injective⟩, f a = ∑ x : (ZMod m)ˣ, f (x : ZMod m) := by
    rw [Finset.sum_map]
    rfl
  rw [← hmap]
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro a _ hna
  exact hf a (fun hu => hna ((key a).mpr hu))

open scoped Classical in
private lemma rcc_sum_char_units {m : ℕ} [NeZero m] (θ : DirichletCharacter ℂ m) :
    ∑ x : (ZMod m)ˣ, θ (x : ZMod m) = if θ = 1 then ((m.totient : ℝ) : ℂ) else 0 := by
  have hz : ∀ a : ZMod m, ¬IsUnit a → θ a = 0 := fun a ha => MulChar.map_nonunit θ ha
  rw [rcc_sum_units_eq_sum (fun a => θ a) hz]
  by_cases h : θ = 1
  · rw [if_pos h, h, MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient, rcc_totient_cast]
  · rw [if_neg h, MulChar.sum_eq_zero_of_ne_one h]

open scoped Classical in
private lemma rcc_star_char {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (x : (ZMod m)ˣ) :
    star (χ (x : ZMod m)) = χ ((x : ZMod m)⁻¹) := by
  rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]

open scoped Classical in
private lemma rcc_orth1 {m : ℕ} [NeZero m] (x y : (ZMod m)ˣ) :
    ∑ χ : DirichletCharacter ℂ m, star (χ (x : ZMod m)) * χ (y : ZMod m)
      = if x = y then ((m.totient : ℝ) : ℂ) else 0 := by
  simp_rw [rcc_star_char]
  rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ x.isUnit (y : ZMod m)]
  by_cases hxy : (x : ZMod m) = (y : ZMod m)
  · rw [if_pos hxy, if_pos (Units.val_inj.mp hxy), rcc_totient_cast]
  · rw [if_neg hxy, if_neg (fun h => hxy (Units.val_inj.mpr h))]

open scoped Classical in
private lemma rcc_orth2 {m : ℕ} [NeZero m] (χ ψ : DirichletCharacter ℂ m) :
    ∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (x : ZMod m)
      = if χ = ψ then ((m.totient : ℝ) : ℂ) else 0 := by
  have h1 (x : (ZMod m)ˣ) :
      star (χ (x : ZMod m)) * ψ (x : ZMod m) = (χ⁻¹ * ψ) (x : ZMod m) := by
    rw [MulChar.mul_apply, MulChar.star_apply']
  have h2 : ∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (x : ZMod m)
      = ∑ x : (ZMod m)ˣ, (χ⁻¹ * ψ) (x : ZMod m) := Finset.sum_congr rfl (fun x _ => h1 x)
  rw [h2, rcc_sum_char_units]
  by_cases h : χ = ψ
  · subst h
    simp
  · rw [if_neg h, if_neg (fun h2 => h (inv_mul_eq_one.mp h2))]

open scoped Classical in
private lemma rcc_parseval_complex {m : ℕ} [NeZero m] (g : (ZMod m)ˣ → ℂ) :
    ∑ χ : DirichletCharacter ℂ m, star (∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * g x)
        * (∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * g x)
      = ((m.totient : ℝ) : ℂ) * ∑ x : (ZMod m)ˣ, star (g x) * g x := by
  have hex (χ : DirichletCharacter ℂ m) :
      star (∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * g x)
          * (∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * g x)
        = ∑ x : (ZMod m)ˣ, ∑ y : (ZMod m)ˣ,
            (star (g x) * g y) * (star (χ (y : ZMod m)) * χ (x : ZMod m)) := by
    rw [star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [star_mul, star_star]
    ring
  simp_rw [hex]
  have hstep (x : (ZMod m)ˣ) :
      ∑ χ : DirichletCharacter ℂ m, ∑ y : (ZMod m)ˣ,
          (star (g x) * g y) * (star (χ (y : ZMod m)) * χ (x : ZMod m))
        = star (g x) * g x * ((m.totient : ℝ) : ℂ) := by
    have h1 : ∑ χ : DirichletCharacter ℂ m, ∑ y : (ZMod m)ˣ,
        (star (g x) * g y) * (star (χ (y : ZMod m)) * χ (x : ZMod m))
        = ∑ y : (ZMod m)ˣ, (star (g x) * g y)
            * ∑ χ : DirichletCharacter ℂ m, (star (χ (y : ZMod m)) * χ (x : ZMod m)) := by
      conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [Finset.mul_sum]
    rw [h1]
    simp_rw [rcc_orth1]
    have h2 : ∀ y : (ZMod m)ˣ,
        (star (g x) * g y) * (if y = x then ((m.totient : ℝ) : ℂ) else 0)
          = if y = x then star (g x) * g x * ((m.totient : ℝ) : ℂ) else 0 := by
      intro y
      by_cases hy : y = x
      · rw [if_pos hy, if_pos hy, hy]
      · rw [if_neg hy, if_neg hy, mul_zero]
    simp_rw [h2]
    simp
  conv_lhs => rw [Finset.sum_comm]
  have h3 : ∑ x : (ZMod m)ˣ, ∑ χ : DirichletCharacter ℂ m, ∑ y : (ZMod m)ˣ,
      (star (g x) * g y) * (star (χ (y : ZMod m)) * χ (x : ZMod m))
      = ∑ x : (ZMod m)ˣ, star (g x) * g x * ((m.totient : ℝ) : ℂ) :=
    Finset.sum_congr rfl (fun x _ => hstep x)
  rw [h3, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun x _ => by ring)

open scoped Classical in
private lemma rcc_parseval {m : ℕ} [NeZero m] (g : (ZMod m)ˣ → ℂ) :
    ∑ χ : DirichletCharacter ℂ m, ‖∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * g x‖ ^ 2
      = (m.totient : ℝ) * ∑ x : (ZMod m)ˣ, ‖g x‖ ^ 2 := by
  have h := rcc_parseval_complex g
  simp_rw [rcc_star_mul_self] at h
  have h2 : ((∑ χ : DirichletCharacter ℂ m,
        ‖∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * g x‖ ^ 2 : ℝ) : ℂ)
      = (((m.totient : ℝ) * ∑ x : (ZMod m)ˣ, ‖g x‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_sum]
    exact h
  exact Complex.ofReal_injective h2

open scoped Classical in
private lemma rcc_sum_swap {m : ℕ} [NeZero m] (N : ZMod m) (A B : ZMod m → ℂ)
    (hA : ∀ a, ¬IsUnit a → A a = 0) (hB : ∀ a, ¬IsUnit a → B a = 0) :
    ∑ x : (ZMod m)ˣ, A (x : ZMod m) * B (N - (x : ZMod m))
      = ∑ x : (ZMod m)ˣ, B (x : ZMod m) * A (N - (x : ZMod m)) := by
  have h1 : ∀ a : ZMod m, ¬IsUnit a → A a * B (N - a) = 0 := by
    intro a ha
    rw [hA a ha, zero_mul]
  have h2 : ∀ a : ZMod m, ¬IsUnit a → B a * A (N - a) = 0 := by
    intro a ha
    rw [hB a ha, zero_mul]
  rw [rcc_sum_units_eq_sum (fun a => A a * B (N - a)) h1,
    rcc_sum_units_eq_sum (fun a => B a * A (N - a)) h2]
  have hinv : ∀ z : ZMod m, N - (N - z) = z := fun z => by ring
  have hbij : Function.Bijective (fun z : ZMod m => N - z) := by
    constructor
    · intro a b hab
      have h3 := congrArg (fun t : ZMod m => N - t) hab
      rw [hinv, hinv] at h3
      exact h3
    · intro b
      exact ⟨N - b, hinv b⟩
  have hkey : ∑ a : ZMod m, A a * B (N - a) = ∑ b : ZMod m, A (N - b) * B b :=
    Fintype.sum_bijective (fun z : ZMod m => N - z) hbij
      (fun a : ZMod m => A a * B (N - a)) (fun b : ZMod m => A (N - b) * B b) (fun b => by simp)
  rw [hkey]
  exact Finset.sum_congr rfl (fun b _ => by ring)

open scoped Classical in
private lemma rcc_sum_reflect_le {m : ℕ} [NeZero m] (N : ZMod m) (F : ZMod m → ℂ) (hF : ∀ a, ¬IsUnit a → F a = 0) :
    ∑ x : (ZMod m)ˣ, ‖F (N - (x : ZMod m))‖ ^ 2 ≤ ∑ x : (ZMod m)ˣ, ‖F (x : ZMod m)‖ ^ 2 := by
  classical
  have hinv : ∀ z : ZMod m, N - (N - z) = z := fun z => by ring
  have hinj : Function.Injective (fun x : (ZMod m)ˣ => N - (x : ZMod m)) := by
    intro a b hab
    have h3 := congrArg (fun t : ZMod m => N - t) hab
    rw [hinv, hinv] at h3
    exact Units.val_injective h3
  have hf0 : ∀ a : ZMod m, ¬IsUnit a → ‖F a‖ ^ 2 = (0 : ℝ) := by
    intro a ha
    simp [hF a ha]
  have hmap : ∑ a ∈ (Finset.univ : Finset (ZMod m)ˣ).map
        ⟨fun x : (ZMod m)ˣ => N - (x : ZMod m), hinj⟩, ‖F a‖ ^ 2
      = ∑ x : (ZMod m)ˣ, ‖F (N - (x : ZMod m))‖ ^ 2 := by
    rw [Finset.sum_map]
    rfl
  calc ∑ x : (ZMod m)ˣ, ‖F (N - (x : ZMod m))‖ ^ 2
      = ∑ a ∈ (Finset.univ : Finset (ZMod m)ˣ).map
          ⟨fun x : (ZMod m)ˣ => N - (x : ZMod m), hinj⟩, ‖F a‖ ^ 2 := hmap.symm
    _ ≤ ∑ a : ZMod m, ‖F a‖ ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
        intro a _ _
        exact sq_nonneg _
    _ = ∑ x : (ZMod m)ˣ, ‖F (x : ZMod m)‖ ^ 2 :=
        (rcc_sum_units_eq_sum (fun a : ZMod m => ‖F a‖ ^ 2) hf0).symm

open scoped Classical in
private lemma rcc_synth_norm {m : ℕ} [NeZero m] (w : DirichletCharacter ℂ m → ℂ) :
    ∑ x : (ZMod m)ˣ, ‖∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (x : ZMod m)‖ ^ 2
      = (m.totient : ℝ) * ∑ ψ : DirichletCharacter ℂ m, ‖w ψ‖ ^ 2 := by
  have hB (χ : DirichletCharacter ℂ m) :
      ∑ x : (ZMod m)ˣ, star (χ (x : ZMod m))
          * ∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (x : ZMod m)
        = ((m.totient : ℝ) : ℂ) * w χ := by
    calc ∑ x : (ZMod m)ˣ, star (χ (x : ZMod m))
            * ∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (x : ZMod m)
        = ∑ x : (ZMod m)ˣ, ∑ ψ : DirichletCharacter ℂ m,
            star (χ (x : ZMod m)) * (w ψ * ψ (x : ZMod m)) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [Finset.mul_sum]
      _ = ∑ ψ : DirichletCharacter ℂ m, ∑ x : (ZMod m)ˣ,
            star (χ (x : ZMod m)) * (w ψ * ψ (x : ZMod m)) := rcc_sum_interchange _
      _ = ∑ ψ : DirichletCharacter ℂ m, w ψ
            * ∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (x : ZMod m) := by
          refine Finset.sum_congr rfl (fun ψ _ => ?_)
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun x _ => by ring)
      _ = ∑ ψ : DirichletCharacter ℂ m,
            w ψ * (if χ = ψ then ((m.totient : ℝ) : ℂ) else 0) := by
          simp_rw [rcc_orth2]
      _ = ((m.totient : ℝ) : ℂ) * w χ := by
          have h2 : ∀ ψ : DirichletCharacter ℂ m,
              w ψ * (if χ = ψ then ((m.totient : ℝ) : ℂ) else 0)
                = if ψ = χ then ((m.totient : ℝ) : ℂ) * w χ else 0 := by
            intro ψ
            by_cases hψ : ψ = χ
            · rw [if_pos hψ, if_pos hψ.symm, hψ]
              ring
            · rw [if_neg hψ, if_neg (fun h => hψ h.symm), mul_zero]
          simp_rw [h2]
          simp
  have hp := rcc_parseval (fun x : (ZMod m)ˣ => ∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (x : ZMod m))
  have hkey1 : ∀ χ : DirichletCharacter ℂ m,
      ‖∑ x : (ZMod m)ˣ, star (χ (x : ZMod m))
        * ∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (x : ZMod m)‖ ^ 2
      = (m.totient : ℝ) ^ 2 * ‖w χ‖ ^ 2 := by
    intro χ
    rw [hB χ, norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt rcc_totient_pos_real), mul_pow]
  have hkey : ∑ χ : DirichletCharacter ℂ m,
      ‖∑ x : (ZMod m)ˣ, star (χ (x : ZMod m))
        * ∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (x : ZMod m)‖ ^ 2
      = (m.totient : ℝ) ^ 2 * ∑ ψ : DirichletCharacter ℂ m, ‖w ψ‖ ^ 2 := by
    rw [Finset.sum_congr rfl (fun χ _ => hkey1 χ), Finset.mul_sum]
  rw [hkey] at hp
  have h3 : (m.totient : ℝ) * ((m.totient : ℝ) * ∑ ψ : DirichletCharacter ℂ m, ‖w ψ‖ ^ 2)
      = (m.totient : ℝ)
        * ∑ x : (ZMod m)ˣ, ‖∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (x : ZMod m)‖ ^ 2 := by
    rw [← hp]
    ring
  exact (mul_left_cancel₀ (ne_of_gt rcc_totient_pos_real) h3).symm

open scoped Classical in
private lemma rcc_main_bound {m : ℕ} [NeZero m] (N : ZMod m) (w : DirichletCharacter ℂ m → ℂ) :
    ∑ χ : DirichletCharacter ℂ m,
        ‖∑ ψ : DirichletCharacter ℂ m,
            ((∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (N - (x : ZMod m)))
              / (m.totient : ℂ)) * w ψ‖ ^ 2
      ≤ ∑ ψ : DirichletCharacter ℂ m, ‖w ψ‖ ^ 2 := by
  have hφ : (m.totient : ℝ) ≠ 0 := ne_of_gt rcc_totient_pos_real
  have hFz (a : ZMod m) (ha : ¬IsUnit a) :
      ∑ ψ : DirichletCharacter ℂ m, w ψ * ψ a = 0 := by
    refine Finset.sum_eq_zero (fun ψ _ => ?_)
    rw [MulChar.map_nonunit ψ ha, mul_zero]
  have step1 (χ : DirichletCharacter ℂ m) :
      ∑ ψ : DirichletCharacter ℂ m,
          ((∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (N - (x : ZMod m)))
            / (m.totient : ℂ)) * w ψ
        = (∑ x : (ZMod m)ˣ, star (χ (x : ZMod m))
            * ∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (N - (x : ZMod m))) / (m.totient : ℂ) := by
    have hinner : ∑ ψ : DirichletCharacter ℂ m,
        (∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (N - (x : ZMod m))) * w ψ
        = ∑ x : (ZMod m)ˣ, star (χ (x : ZMod m))
            * ∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (N - (x : ZMod m)) := by
      calc ∑ ψ : DirichletCharacter ℂ m,
            (∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (N - (x : ZMod m))) * w ψ
          = ∑ ψ : DirichletCharacter ℂ m, ∑ x : (ZMod m)ˣ,
              (star (χ (x : ZMod m)) * ψ (N - (x : ZMod m))) * w ψ := by
            refine Finset.sum_congr rfl (fun ψ _ => ?_)
            rw [Finset.sum_mul]
        _ = ∑ x : (ZMod m)ˣ, ∑ ψ : DirichletCharacter ℂ m,
              (star (χ (x : ZMod m)) * ψ (N - (x : ZMod m))) * w ψ := rcc_sum_interchange _
        _ = ∑ x : (ZMod m)ˣ, star (χ (x : ZMod m))
              * ∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (N - (x : ZMod m)) := by
            refine Finset.sum_congr rfl (fun x _ => ?_)
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun ψ _ => by ring)
    calc ∑ ψ : DirichletCharacter ℂ m,
          ((∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (N - (x : ZMod m)))
            / (m.totient : ℂ)) * w ψ
        = (∑ ψ : DirichletCharacter ℂ m,
            (∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (N - (x : ZMod m))) * w ψ)
            / (m.totient : ℂ) := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl (fun ψ _ => by ring)
      _ = (∑ x : (ZMod m)ˣ, star (χ (x : ZMod m))
            * ∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (N - (x : ZMod m))) / (m.totient : ℂ) := by
          rw [hinner]
  have step2 (z : ℂ) : ‖z / (m.totient : ℂ)‖ ^ 2 = ‖z‖ ^ 2 / (m.totient : ℝ) ^ 2 := by
    rw [norm_div, div_pow, Complex.norm_natCast]
  calc ∑ χ : DirichletCharacter ℂ m,
        ‖∑ ψ : DirichletCharacter ℂ m,
          ((∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (N - (x : ZMod m)))
            / (m.totient : ℂ)) * w ψ‖ ^ 2
      = ∑ χ : DirichletCharacter ℂ m, ‖∑ x : (ZMod m)ˣ, star (χ (x : ZMod m))
          * ∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (N - (x : ZMod m))‖ ^ 2
          / (m.totient : ℝ) ^ 2 := by
        refine Finset.sum_congr rfl (fun χ _ => ?_)
        rw [step1 χ, step2]
    _ = ((m.totient : ℝ) * ∑ x : (ZMod m)ˣ,
          ‖∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (N - (x : ZMod m))‖ ^ 2) / (m.totient : ℝ) ^ 2 := by
        rw [← Finset.sum_div,
          rcc_parseval (fun x : (ZMod m)ˣ => ∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (N - (x : ZMod m)))]
    _ ≤ ((m.totient : ℝ) * ∑ x : (ZMod m)ˣ,
          ‖∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (x : ZMod m)‖ ^ 2) / (m.totient : ℝ) ^ 2 := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt rcc_totient_pos_real)
        exact rcc_sum_reflect_le N (fun a : ZMod m => ∑ ψ : DirichletCharacter ℂ m, w ψ * ψ a) hFz
    _ = ∑ ψ : DirichletCharacter ℂ m, ‖w ψ‖ ^ 2 := by
        rw [rcc_synth_norm w]
        field_simp


private lemma ep2_arith_key (N q : ℕ) (h4 : 4 ≤ N) (hq4 : 4 ≤ q) :
    (if (N+q-2)%q = 2 then (if (N+2*q-2)%(2*q) < q then (1:ℝ) else -1) else 0)
      = (if N %(2*q)=4 %(2*q) then (1:ℝ) else if N %(2*q)=(4+q)%(2*q) then -1 else 0) := by
  have hqpos : 0 < q := by omega
  have harg : (N+q-2)%q = (N-2)%q := by
    have h1 : N + q - 2 = (N-2) + q*1 := by
      rw [Nat.sub_eq_iff_eq_add (by omega : 2 ≤ N + q)]
      omega
    rw [h1, Nat.add_mul_mod_self_left]
  obtain ⟨c, r0, hr0lt, hN⟩ : ∃ c r0, r0 < q ∧ N - 4 = c*q + r0 := by
    refine ⟨(N-4)/q, (N-4)%q, Nat.mod_lt _ hqpos, ?_⟩
    rw [Nat.mul_comm ((N-4)/q) q, add_comm]
    exact (Nat.mod_add_div (N-4) q).symm
  have hN4 : N = 4 + c*q + r0 := by omega
  have harg2 : ((N+q-2)%q = 2) ↔ (r0 = 0) := by
    have harg' : (N+q-2)%q = (r0+2)%q := by
      have h1 : N + q - 2 = (r0 + 2) + (c+1)*q := by
        rw [hN4, Nat.sub_eq_iff_eq_add (by omega : 2 ≤ 4 + c*q + r0 + q)]
        ring
      rw [h1, Nat.mul_comm (c+1) q]
      exact Nat.add_mul_mod_self_left (r0+2) q (c+1)
    rw [harg']
    constructor
    · intro h
      by_cases hc : r0 + 2 < q
      · rw [Nat.mod_eq_of_lt hc] at h; omega
      · push_neg at hc
        rw [Nat.mod_eq_sub_mod hc] at h
        have h1 : r0 + 2 - q < q := by omega
        rw [Nat.mod_eq_of_lt h1] at h
        omega
    · intro h
      subst h
      rw [Nat.mod_eq_of_lt (by omega : 0 + 2 < q)]
  have hpar : c % 2 = 0 ∨ c % 2 = 1 := by
    have := Nat.mod_lt c (by norm_num : 0 < 2); omega
  have hq_dvd_2q : q ∣ 2*q := by
    rw [Nat.mul_comm 2 q]; exact dvd_mul_right q 2
  have hcond1 : (N %(2*q) = 4 %(2*q)) ↔ (r0 = 0 ∧ c % 2 = 0) := by
    have h4lt : 4 < 2*q := by omega
    constructor
    · intro hmod
      have hmodeq : N ≡ 4 [MOD (2*q)] := by
        unfold Nat.ModEq
        rw [hmod, Nat.mod_eq_of_lt h4lt]
      have hdvd : (2*q) ∣ N - 4 := (Nat.modEq_iff_dvd' (by omega : 4 ≤ N)).mp hmodeq.symm
      rw [hN] at hdvd
      have hq_dvd : q ∣ c*q + r0 := dvd_trans hq_dvd_2q hdvd
      have hq_r0 : q ∣ r0 := by
        have h1 : q ∣ r0 + q*c := by
          have h2 := hq_dvd
          simpa [mul_comm, add_comm] using h2
        exact (Nat.dvd_add_iff_left (dvd_mul_right q c)).mpr h1
      have hr0 : r0 = 0 := Nat.eq_zero_of_dvd_of_lt hq_r0 hr0lt
      have hc2 : 2 ∣ c := by
        have h : (2*q) ∣ c*q := by rw [hr0, add_zero] at hdvd; exact hdvd
        have h' : 2*q ∣ c*q := h
        rw [Nat.mul_comm 2 q, Nat.mul_comm c q] at h'
        exact (Nat.mul_dvd_mul_iff_left hqpos).mp h'
      exact ⟨hr0, Nat.dvd_iff_mod_eq_zero.mp hc2⟩
    · rintro ⟨rfl, hc2⟩
      obtain ⟨d, rfl⟩ := Nat.dvd_iff_mod_eq_zero.mpr hc2
      have hNc : N = 4 + d*(2*q) := by rw [hN4]; ring
      rw [hNc, Nat.mul_comm d (2*q)]
      exact Nat.add_mul_mod_self_left 4 (2*q) d
  have hcond2 : (N %(2*q) = (4+q)%(2*q)) ↔ (r0 = 0 ∧ c % 2 = 1) := by
    constructor
    · intro hmod
      by_cases hc0 : c = 0
      · have hNc : N = 4 + r0 := by rw [hN4, hc0]; ring
        have hNlt : N < 2*q := by omega
        have hNm : N % (2*q) = N := Nat.mod_eq_of_lt hNlt
        rw [hNm] at hmod
        have hv : (4+q) % (2*q) = 0 ∨ (4+q) % (2*q) = 4+q := by
          by_cases hq : q = 4
          · left; subst hq; norm_num
          · right; exact Nat.mod_eq_of_lt (by omega)
        rcases hv with hv | hv
        · rw [hv] at hmod; omega
        · rw [hv] at hmod; omega
      · have hc1 : 1 ≤ c := by omega
        have hge : 4 + q ≤ N := by
          rw [hN4]
          have h1 : 1*q ≤ c*q := Nat.mul_le_mul_right q hc1
          have h2 : q ≤ c*q := by simpa using h1
          omega
        have hmodeq : N ≡ (4+q) [MOD (2*q)] := by
          unfold Nat.ModEq
          rw [hmod]
        have hdvd : (2*q) ∣ N - (4+q) := (Nat.modEq_iff_dvd' hge).mp hmodeq.symm
        have hsub : N - (4+q) = (c-1)*q + r0 := by
          have hc' : c = (c-1) + 1 := by omega
          have h1 : N = 4 + ((c-1)+1)*q + r0 := by
            have h2 : c*q = ((c-1)+1)*q := by
              conv_lhs => rw [hc']
            omega
          rw [h1]
          have hexp : ((c-1)+1)*q = (c-1)*q + q := by ring
          rw [hexp]
          omega
        rw [hsub] at hdvd
        have hq_dvd : q ∣ (c-1)*q + r0 := dvd_trans hq_dvd_2q hdvd
        have hq_r0 : q ∣ r0 := by
          have h1 : q ∣ r0 + q*(c-1) := by
            have h2 := hq_dvd
            rw [mul_comm (c-1) q, add_comm] at h2
            exact h2
          exact (Nat.dvd_add_iff_left (dvd_mul_right q (c-1))).mpr h1
        have hr0 : r0 = 0 := Nat.eq_zero_of_dvd_of_lt hq_r0 hr0lt
        have hc_odd : c % 2 = 1 := by
          have h : (2*q) ∣ (c-1)*q := by rw [hr0, add_zero] at hdvd; exact hdvd
          have h' : 2*q ∣ (c-1)*q := h
          rw [Nat.mul_comm 2 q, Nat.mul_comm (c-1) q] at h'
          have h2 : 2 ∣ c-1 := (Nat.mul_dvd_mul_iff_left hqpos).mp h'
          have hmod2 : (c-1) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h2
          have hlt := Nat.mod_lt c (by norm_num : 0 < 2)
          omega
        exact ⟨hr0, hc_odd⟩
    · rintro ⟨rfl, hcodd⟩
      obtain ⟨d, hc⟩ : ∃ d, c = 2*d + 1 := by
        refine ⟨c/2, ?_⟩
        have h1 := Nat.div_add_mod c 2
        omega
      have hNc : N = (4+q) + d*(2*q) := by rw [hN4, hc]; ring
      rw [hNc, Nat.mul_comm d (2*q)]
      exact Nat.add_mul_mod_self_left (4+q) (2*q) d
  have hsign_even : r0 = 0 → c % 2 = 0 → (N+2*q-2)%(2*q) < q := by
    intro hr hr2
    obtain ⟨d, hc⟩ : ∃ d, c = 2*d := Nat.dvd_iff_mod_eq_zero.mpr hr2
    have hNc : N = 4 + d*(2*q) := by rw [hN4, hr, hc]; ring
    have h1 : N + 2*q - 2 = 2 + (d+1)*(2*q) := by
      rw [hNc, Nat.sub_eq_iff_eq_add (by omega : 2 ≤ 4 + d*(2*q) + 2*q)]
      ring
    rw [h1, Nat.mul_comm (d+1) (2*q)]
    rw [Nat.add_mul_mod_self_left]
    have h2 : 2 % (2*q) = 2 := Nat.mod_eq_of_lt (by omega)
    rw [h2]; omega
  have hsign_odd : r0 = 0 → c % 2 = 1 → ¬ ((N+2*q-2)%(2*q) < q) := by
    intro hr hr2
    obtain ⟨d, hc⟩ : ∃ d, c = 2*d + 1 := by
      refine ⟨c/2, ?_⟩
      have h1 := Nat.div_add_mod c 2
      omega
    have hNc : N = 4 + (2*d+1)*q := by rw [hN4, hr, hc]; ring
    have h1 : N + 2*q - 2 = (q+2) + (d+1)*(2*q) := by
      rw [hNc, Nat.sub_eq_iff_eq_add (by omega : 2 ≤ 4 + (2*d+1)*q + 2*q)]
      ring
    rw [h1, Nat.mul_comm (d+1) (2*q)]
    rw [Nat.add_mul_mod_self_left]
    have h2 : (q+2) % (2*q) = q+2 := Nat.mod_eq_of_lt (by omega)
    rw [h2]; omega
  by_cases hr0 : r0 = 0
  · have hargval : (N+q-2)%q = 2 := harg2.mpr hr0
    rw [if_pos hargval]
    rcases hpar with hc2 | hc1
    · have hs : (N+2*q-2)%(2*q) < q := hsign_even hr0 hc2
      have hc1v : N %(2*q) = 4 %(2*q) := hcond1.mpr ⟨hr0, hc2⟩
      have hc2v : ¬ (N %(2*q) = (4+q)%(2*q)) := by
        intro hh
        have := (hcond2.mp hh).2
        omega
      rw [if_pos hs, if_pos hc1v]
    · have hs : ¬ ((N+2*q-2)%(2*q) < q) := hsign_odd hr0 hc1
      have hc2v : N %(2*q) = (4+q)%(2*q) := hcond2.mpr ⟨hr0, hc1⟩
      have hc1v : ¬ (N %(2*q) = 4 %(2*q)) := by
        intro hh
        have := (hcond1.mp hh).2
        omega
      rw [if_neg hs, if_neg hc1v, if_pos hc2v]
  · have hargval : ¬ ((N+q-2)%q = 2) := fun hh => hr0 (harg2.mp hh)
    rw [if_neg hargval]
    have hc1v : ¬ (N %(2*q) = 4 %(2*q)) := fun hh => hr0 (hcond1.mp hh).1
    have hc2v : ¬ (N %(2*q) = (4+q)%(2*q)) := fun hh => hr0 (hcond2.mp hh).1
    rw [if_neg hc1v, if_neg hc2v]

private theorem ep2_main :
    ∀ (N k : ℕ), 4 ≤ N → Even N → 1 ≤ k →
    let q : ℕ := 2^k
    let A := fun r : ℕ => ∑ n ∈ (Finset.range (N+1)).filter (fun n => n %(2*q)=r ∧ n.Prime), Real.log (n : ℝ)
    let D := fun r : ℕ => A r - A (r+q)
    (∑ r ∈ (Finset.range q).filter (fun r => Even r),
      (if (N+2*q-r)%(2*q) < q then (1 : ℝ) else -1) * D r * D ((N+q-r)%q)) =
      (if N %(2*q)=4 %(2*q) then (1 : ℝ) else if N %(2*q)=(4+q)%(2*q) then -1 else 0) * (Real.log 2)^2 := by
  intro N k h4 hEven hk
  let q : ℕ := 2^k
  let A : ℕ → ℝ := fun r => ∑ n ∈ (Finset.range (N+1)).filter (fun n => n %(2*q)=r ∧ n.Prime), Real.log (n : ℝ)
  let D : ℕ → ℝ := fun r => A r - A (r+q)
  have hq_even : Even q := by
    change Even (2^k)
    obtain ⟨j, hjk⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [hjk]
    refine ⟨2^j, ?_⟩
    rw [pow_succ]
    ring
  have hq2 : 2 ≤ q := by
    calc 2 = 2^1 := by norm_num
      _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hk
  have hN2 : Even (N-2) := by
    rw [Nat.even_iff]
    have h1 : N % 2 = 0 := Nat.even_iff.mp hEven
    have h2 : ((N-2) + 2*1) % 2 = (N-2) % 2 := Nat.add_mul_mod_self_left (N-2) 2 1
    have h3 : (N-2) + 2*1 = N := by omega
    rw [h3] at h2
    rw [← h2]
    exact h1
  have hprime_even : ∀ n, n.Prime → Even n → n = 2 := by
    intro n hp hn
    rcases hp.eq_two_or_odd with h | h
    · exact h
    · have : n % 2 = 0 := Nat.even_iff.mp hn
      omega
  have heven_of_mod : ∀ n r, Even r → n % (2*q) = r → Even n := by
    intro n r hr hmod
    rw [Nat.even_iff] at hr ⊢
    have h1 : n % 2 = (n % (2*q)) % 2 := (Nat.mod_mod_of_dvd n (dvd_mul_right 2 q)).symm
    rw [h1, hmod, hr]
  have h2q2 : 2 < 2*q := by omega
  have hA_even : ∀ r, Even r → A r = if r = 2 then Real.log 2 else 0 := by
    intro r hr
    have hmem2 : (2:ℕ) ∈ (Finset.range (N+1)).filter (fun n => n %(2*q)=2 ∧ n.Prime) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_, Nat.prime_two⟩
      exact Nat.mod_eq_of_lt h2q2
    have hfilter2 : (Finset.range (N+1)).filter (fun n => n %(2*q)=2 ∧ n.Prime) = {2} := by
      ext n
      constructor
      · intro hn
        obtain ⟨-, hmod, hp⟩ := Finset.mem_filter.mp hn
        have he : Even n := heven_of_mod n 2 even_two hmod
        rw [Finset.mem_singleton]
        exact hprime_even n hp he
      · intro hn
        rw [Finset.mem_singleton] at hn
        subst hn
        exact hmem2
    by_cases h2 : r = 2
    · subst h2
      change (∑ n ∈ (Finset.range (N+1)).filter (fun n => n %(2*q)=2 ∧ n.Prime), Real.log (n:ℝ)) = _
      rw [hfilter2]
      simp
    · have hempty : (Finset.range (N+1)).filter (fun n => n %(2*q)=r ∧ n.Prime) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro n hn
        obtain ⟨-, hmod, hp⟩ := Finset.mem_filter.mp hn
        have he : Even n := heven_of_mod n r hr hmod
        have hn2 : n = 2 := hprime_even n hp he
        subst hn2
        rw [Nat.mod_eq_of_lt h2q2] at hmod
        exact h2 hmod.symm
      change (∑ n ∈ (Finset.range (N+1)).filter (fun n => n %(2*q)=r ∧ n.Prime), Real.log (n:ℝ)) = _
      rw [hempty]
      simp [h2]
  have hD_even : ∀ r, Even r → D r = (if r = 2 then Real.log 2 else 0) - (if r+q = 2 then Real.log 2 else 0) := by
    intro r hr
    change A r - A (r+q) = _
    rw [hA_even r hr, hA_even (r+q) (hr.add hq_even)]
  have hD_k4 : 4 ≤ q → ∀ r, Even r → D r = if r = 2 then Real.log 2 else 0 := by
    intro hq4 r hr
    rw [hD_even r hr]
    have h1 : ¬ (r + q = 2) := by omega
    rw [if_neg h1]
    ring
  have hk1case : k = 1 → (∑ r ∈ (Finset.range q).filter (fun r => Even r),
      (if (N+2*q-r)%(2*q) < q then (1 : ℝ) else -1) * D r * D ((N+q-r)%q)) =
      (if N %(2*q)=4 %(2*q) then (1 : ℝ) else if N %(2*q)=(4+q)%(2*q) then -1 else 0) * (Real.log 2)^2 := by
    intro hk1
    have hq2 : q = 2 := by
      change 2^k = 2
      rw [hk1]
      norm_num
    rw [hq2] at hD_even ⊢
    have hfilter : (Finset.range 2).filter (fun r => Even r) = {0} := by decide
    rw [hfilter, Finset.sum_singleton]
    have hD0 : D 0 = - Real.log 2 := by
      rw [hD_even 0 (show Even 0 from ⟨0, by norm_num⟩)]
      norm_num
    have hNmod : (N + 2*2 - 0) % (2*2) = N % 4 := by
      have h : N + 2*2 - 0 = N + (2*2)*1 := by norm_num
      rw [h, Nat.add_mul_mod_self_left]
    have harg0 : (N+2-0)%2 = 0 := by
      have h1 : N % 2 = 0 := Nat.even_iff.mp hEven
      have h2 : (N + 2*1) % 2 = N % 2 := Nat.add_mul_mod_self_left N 2 1
      show (N+2) % 2 = 0
      rw [show N + 2 = N + 2*1 from rfl, h2, h1]
    rw [harg0, hD0]
    have hcases : N % 4 = 0 ∨ N % 4 = 2 := by
      have hlt : N % 4 < 4 := Nat.mod_lt N (by norm_num)
      have hmod : (N % 4) % 2 = N % 2 := Nat.mod_mod_of_dvd N (by norm_num : 2 ∣ 4)
      have hNm : N % 2 = 0 := Nat.even_iff.mp hEven
      rw [hNm] at hmod
      omega
    rcases hcases with h0 | h2
    · have hs : (N + 2*2 - 0) % (2*2) < 2 := by rw [hNmod, h0]; norm_num
      have hr1 : N % 4 = 4 % 4 := by rw [h0]
      rw [if_pos hs, if_pos hr1]
      ring
    · have hs : ¬ ((N + 2*2 - 0) % (2*2) < 2) := by rw [hNmod, h2]; norm_num
      have hr1 : N % 4 ≠ 4 % 4 := by rw [h2]; norm_num
      have hr2 : N % 4 = (4+2) % (2*2) := by rw [h2]
      rw [if_neg hs, if_neg hr1, if_pos hr2]
      ring
  have hk2case : 2 ≤ k → (∑ r ∈ (Finset.range q).filter (fun r => Even r),
      (if (N+2*q-r)%(2*q) < q then (1 : ℝ) else -1) * D r * D ((N+q-r)%q)) =
      (if N %(2*q)=4 %(2*q) then (1 : ℝ) else if N %(2*q)=(4+q)%(2*q) then -1 else 0) * (Real.log 2)^2 := by
    intro hk2
    have hq4 : 4 ≤ q := by
      calc 4 = 2^2 := by norm_num
        _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hk2
    have hqpos : 0 < q := by omega
    have hD_k2 := hD_k4 hq4
    have hmem2 : (2:ℕ) ∈ (Finset.range q).filter (fun r => Even r) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), even_two⟩
    have hsingle : (∑ r ∈ (Finset.range q).filter (fun r => Even r),
        (if (N+2*q-r)%(2*q) < q then (1 : ℝ) else -1) * D r * D ((N+q-r)%q))
        = (if (N+2*q-2)%(2*q) < q then (1 : ℝ) else -1) * D 2 * D ((N+q-2)%q) := by
      refine Finset.sum_eq_single 2 ?_ ?_
      · intro r hr hne
        obtain ⟨-, hre⟩ := Finset.mem_filter.mp hr
        have hDr : D r = 0 := by
          rw [hD_k2 r hre]
          exact if_neg hne
        simp [hDr]
      · intro hnot
        exact absurd hmem2 hnot
    rw [hsingle]
    have hD2 : D 2 = Real.log 2 := by
      rw [hD_k2 2 even_two]
      norm_num
    rw [hD2]
    have hargEven : Even ((N+q-2)%q) := by
      have harg_eq : (N+q-2)%q = (N-2)%q := by
        have h1 : N + q - 2 = (N-2) + q*1 := by
          rw [Nat.sub_eq_iff_eq_add (by omega : 2 ≤ N + q)]
          omega
        rw [h1, Nat.add_mul_mod_self_left]
      rw [harg_eq, Nat.even_iff]
      rw [Nat.mod_mod_of_dvd (N-2) (even_iff_two_dvd.mp hq_even), Nat.even_iff.mp hN2]
    rw [hD_k2 ((N+q-2)%q) hargEven]
    have hL : (if (N+2*q-2)%(2*q) < q then (1 : ℝ) else -1) * Real.log 2 *
        (if ((N+q-2)%q = 2) then Real.log 2 else 0)
        = (if ((N+q-2)%q = 2) then (if (N+2*q-2)%(2*q) < q then (1 : ℝ) else -1) else 0) *
          (Real.log 2)^2 := by
      by_cases ha : (N+q-2)%q = 2
      · rw [if_pos ha, if_pos ha]; ring
      · rw [if_neg ha, if_neg ha]; ring
    rw [hL, ep2_arith_key N q h4 hq4]
  by_cases hk1 : k = 1
  · exact hk1case hk1
  · exact hk2case (by omega)


private theorem primFormRF2 (N k : ℕ) (hN : Even N) (hk : 1 ≤ k)
    (f : ZMod (2^(k+1)) → ℝ)
    (s : Finset (DirichletCharacter ℂ (2^(k+1))))
    (v : DirichletCharacter ℂ (2^(k+1)) → ℂ)
    (H : DirichletCharacter ℂ (2^(k+1)) → DirichletCharacter ℂ (2^(k+1)) → ℂ)
    (hs : s = (Finset.univ : Finset (DirichletCharacter ℂ (2^(k+1)))).filter
      (fun χ => χ.conductor = 2^(k+1)))
    (hv : v = fun χ : DirichletCharacter ℂ (2^(k+1)) =>
      (∑ x : (ZMod (2^(k+1)))ˣ, (f (x : ZMod (2^(k+1))) : ℂ) * star (χ (x : ZMod (2^(k+1))))) /
        (Real.sqrt ((2^(k+1)).totient : ℝ) : ℂ))
    (hH : H = fun χ ψ : DirichletCharacter ℂ (2^(k+1)) =>
      (∑ x : (ZMod (2^(k+1)))ˣ, star (χ (x : ZMod (2^(k+1)))) *
        ψ ((N : ZMod (2^(k+1))) - (x : ZMod (2^(k+1))))) / ((2^(k+1)).totient : ℂ)) :
    (∑ r ∈ (Finset.range (2^k)).filter (fun r => Odd r),
      (if (N+2*2^k-r) % (2*2^k) < 2^k then (1 : ℝ) else -1) *
        (f (r : ZMod (2^(k+1))) - f ((r+2^k : ℕ) : ZMod (2^(k+1)))) *
        (f (((N+2^k-r) % 2^k : ℕ) : ZMod (2^(k+1))) -
          f ((((N+2^k-r) % 2^k) + 2^k : ℕ) : ZMod (2^(k+1))))) =
      2 * (∑ χ ∈ s, ∑ ψ ∈ s, star (v χ) * H χ ψ * v ψ).re := by
  subst hs hv hH
  exact primFormRF N k hN hk f

private theorem formBoundRF (m : ℕ) [NeZero m] (N : ZMod m)
    (s : Finset (DirichletCharacter ℂ m)) (v : DirichletCharacter ℂ m → ℂ)
    (H : DirichletCharacter ℂ m → DirichletCharacter ℂ m → ℂ)
    (hH : ∀ χ ψ, H χ ψ =
      (∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (N - (x : ZMod m))) / (m.totient : ℂ)) :
    |(∑ χ ∈ s, ∑ ψ ∈ s, star (v χ) * H χ ψ * v ψ).re| ≤ ∑ χ ∈ s, ‖v χ‖ ^ 2 := by
  classical
  obtain ⟨W, hW⟩ : ∃ W : DirichletCharacter ℂ m → ℂ, ∀ ψ, W ψ = if ψ ∈ s then v ψ else 0 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : DirichletCharacter ℂ m → ℂ, ∀ χ, G χ = ∑ ψ ∈ s, H χ ψ * v ψ :=
    ⟨_, fun _ => rfl⟩
  have hG2 : ∀ χ, G χ = ∑ ψ : DirichletCharacter ℂ m,
      ((∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (N - (x : ZMod m))) / (m.totient : ℂ)) * W ψ := by
    intro χ
    calc G χ = ∑ ψ ∈ s, H χ ψ * v ψ := hG χ
      _ = ∑ ψ, H χ ψ * W ψ := by
          refine Eq.trans (Finset.sum_congr rfl (fun ψ hψ => ?_))
            (Finset.sum_subset (Finset.subset_univ s) (f := fun ψ => H χ ψ * W ψ)
              (fun ψ _ hψ => ?_))
          · rw [hW, if_pos hψ]
          · rw [hW, if_neg hψ, mul_zero]
      _ = _ := by simp only [hH]
  have hmb := rcc_main_bound N W
  simp only [← hG2] at hmb
  have hWs : ∑ ψ : DirichletCharacter ℂ m, ‖W ψ‖ ^ 2 = ∑ ψ ∈ s, ‖v ψ‖ ^ 2 := by
    refine Eq.trans (Finset.sum_subset (Finset.subset_univ s) (f := fun ψ => ‖W ψ‖ ^ 2)
      (fun ψ _ hψ => by rw [hW, if_neg hψ]; simp)).symm ?_
    refine Finset.sum_congr rfl (fun ψ hψ => ?_)
    rw [hW, if_pos hψ]
  have hGs : ∑ χ ∈ s, ‖G χ‖ ^ 2 ≤ ∑ χ : DirichletCharacter ℂ m, ‖G χ‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun _ _ _ => sq_nonneg _)
  have hform : (∑ χ ∈ s, ∑ ψ ∈ s, star (v χ) * H χ ψ * v ψ) = ∑ χ ∈ s, star (v χ) * G χ := by
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    rw [hG, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun ψ _ => by ring)
  rw [hform]
  calc |(∑ χ ∈ s, star (v χ) * G χ).re| ≤ ‖∑ χ ∈ s, star (v χ) * G χ‖ :=
        Complex.abs_re_le_norm _
    _ ≤ ∑ χ ∈ s, ‖star (v χ) * G χ‖ := norm_sum_le _ _
    _ ≤ ∑ χ ∈ s, (‖v χ‖ ^ 2 + ‖G χ‖ ^ 2) / 2 := by
        refine Finset.sum_le_sum (fun χ _ => ?_)
        rw [norm_mul, norm_star]
        nlinarith [sq_nonneg (‖v χ‖ - ‖G χ‖)]
    _ = (∑ χ ∈ s, ‖v χ‖ ^ 2 + ∑ χ ∈ s, ‖G χ‖ ^ 2) / 2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ ≤ ∑ χ ∈ s, ‖v χ‖ ^ 2 := by
        rw [hWs] at hmb
        linarith

private theorem twistRF (m : ℕ) [NeZero m] (N : ℕ) (F : ZMod m → ℝ)
    (hF : ∀ y : ZMod m, F y = ∑ n ∈ (Finset.range (N+1)).filter (fun n => n % m = y.val),
      (if n.Prime then Real.log (n : ℝ) else 0))
    (χ : DirichletCharacter ℂ m) :
    (∑ x : (ZMod m)ˣ, (F (x : ZMod m) : ℂ) * star (χ (x : ZMod m))) =
      ∑ n ∈ (Finset.range (N+1)).filter Nat.Prime,
        (Real.log (n : ℝ) : ℂ) * star (χ (n : ZMod m)) := by
  classical
  have hiff : ∀ (n : ℕ) (y : ZMod m), (n % m = y.val) ↔ ((n : ZMod m) = y) := by
    intro n y
    rw [← (ZMod.val_injective m).eq_iff, ZMod.val_natCast]
  have hx : ∀ y : ZMod m, (F y : ℂ) * star (χ y) =
      ∑ n ∈ ((Finset.range (N+1)).filter Nat.Prime).filter (fun n : ℕ => (n : ZMod m) = y),
        (Real.log (n : ℝ) : ℂ) * star (χ (n : ZMod m)) := by
    intro y
    have hF2 : F y = ∑ n ∈ ((Finset.range (N+1)).filter Nat.Prime).filter
        (fun n : ℕ => (n : ZMod m) = y), Real.log (n : ℝ) := by
      rw [hF y, Finset.filter_filter, Finset.sum_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      simp only [← hiff n y]
      by_cases h1 : n % m = y.val <;> by_cases h2 : n.Prime <;> simp [h1, h2]
    rw [hF2, Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have h3 : (n : ZMod m) = y := (Finset.mem_filter.mp hn).2
    rw [h3]
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.range (N+1)).filter Nat.Prime) (t := (Finset.univ : Finset (ZMod m)))
    (g := fun n : ℕ => (n : ZMod m)) (fun _ _ => Finset.mem_univ _)
    (fun n => (Real.log (n : ℝ) : ℂ) * star (χ (n : ZMod m)))
  rw [← hfib]
  have h2 := extendUnitsRF (fun y : ZMod m => (F y : ℂ) * star (χ y))
    (fun y hy => by simp [MulChar.map_nonunit χ hy])
  rw [h2]
  exact Finset.sum_congr rfl (fun y _ => hx y)

private theorem ep2wrapRF (N k : ℕ) (h4 : 4 ≤ N) (hN : Even N) (hk : 1 ≤ k) (A : ℕ → ℕ → ℝ)
    (hA : ∀ d r, A d r = ∑ n ∈ (Finset.range (N+1)).filter (fun n => n % d = r),
      (if n.Prime then Real.log (n : ℝ) else 0)) :
    |∑ r ∈ (Finset.range (2^k)).filter (fun r => Even r),
      (if (N+2*2^k-r) % (2*2^k) < 2^k then (1 : ℝ) else -1) *
        (A (2*2^k) r - A (2*2^k) (r+2^k)) *
        (A (2*2^k) ((N+2^k-r) % 2^k) - A (2*2^k) ((N+2^k-r) % 2^k + 2^k))| ≤
      (Real.log 2)^2 := by
  obtain ⟨B, hB⟩ : ∃ B : ℕ → ℝ, ∀ r, B r = ∑ n ∈ (Finset.range (N+1)).filter
      (fun n => n % (2*2^k) = r ∧ n.Prime), Real.log (n : ℝ) := ⟨_, fun _ => rfl⟩
  have h2 : (∑ r ∈ (Finset.range (2^k)).filter (fun r => Even r),
      (if (N+2*2^k-r) % (2*2^k) < 2^k then (1 : ℝ) else -1) * (B r - B (r+2^k)) *
        (B ((N+2^k-r) % 2^k) - B ((N+2^k-r) % 2^k + 2^k))) =
      (if N % (2*2^k) = 4 % (2*2^k) then (1 : ℝ) else
        if N % (2*2^k) = (4+2^k) % (2*2^k) then -1 else 0) * (Real.log 2)^2 := by
    have hBf : B = fun r => ∑ n ∈ (Finset.range (N+1)).filter
        (fun n => n % (2*2^k) = r ∧ n.Prime), Real.log (n : ℝ) := funext hB
    subst hBf
    exact ep2_main N k h4 hN hk
  have hAB : ∀ r, A (2*2^k) r = B r := by
    intro r
    rw [hA, hB, Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases h1 : n % (2*2^k) = r <;> by_cases h3 : n.Prime <;> simp [h1, h3]
  simp only [hAB]
  rw [h2, abs_mul]
  have hs : |(if N % (2*2^k) = 4 % (2*2^k) then (1 : ℝ) else
        if N % (2*2^k) = (4+2^k) % (2*2^k) then -1 else 0)| ≤ 1 := by
    split_ifs <;> norm_num
  rw [abs_of_nonneg (sq_nonneg (Real.log 2))]
  calc _ ≤ 1 * (Real.log 2)^2 := mul_le_mul_of_nonneg_right hs (sq_nonneg _)
    _ = _ := one_mul _

private theorem layerRF (N k : ℕ) (C : ℝ) (h4 : 4 ≤ N) (hN : Even N) (hk : 1 ≤ k) (hC : 0 ≤ C)
    (htw : ∀ χ : DirichletCharacter ℂ (2^(k+1)), χ.IsPrimitive →
      ‖∑ n ∈ (Finset.range (N+1)).filter Nat.Prime,
        (Real.log (n : ℝ) : ℂ) * star (χ (n : ZMod (2^(k+1))))‖ ≤
          C * Real.sqrt (N : ℝ) * (Real.log (2*N : ℝ))^2)
    (A : ℕ → ℕ → ℝ)
    (hA : ∀ d r, A d r = ∑ n ∈ (Finset.range (N+1)).filter (fun n => n % d = r),
      (if n.Prime then Real.log (n : ℝ) else 0)) :
    |∑ r ∈ Finset.range (2^k),
      (if (N+2*2^k-r) % (2*2^k) < 2^k then (1 : ℝ) else -1) *
        (A (2*2^k) r - A (2*2^k) (r+2^k)) *
        (A (2*2^k) ((N+2^k-r) % 2^k) - A (2*2^k) ((N+2^k-r) % 2^k + 2^k))| ≤
      2 * C^2 * N * (Real.log (2*N : ℝ))^4 + (Real.log 2)^2 := by
  classical
  haveI : NeZero (2^(k+1)) := ⟨by positivity⟩
  have hq0 : 0 < 2^k := by positivity
  have h2q : 2 * 2^k = 2^(k+1) := by ring
  have hmq : 2^(k+1) = 2^k + 2^k := by ring
  obtain ⟨f, hf⟩ : ∃ f : ZMod (2^(k+1)) → ℝ, ∀ y, f y = A (2*2^k) y.val := ⟨_, fun _ => rfl⟩
  have hfr : ∀ r : ℕ, r < 2^(k+1) → f (r : ZMod (2^(k+1))) = A (2*2^k) r := by
    intro r hr
    rw [hf, ZMod.val_natCast, Nat.mod_eq_of_lt hr]
  have hF : ∀ y : ZMod (2^(k+1)), f y = ∑ n ∈ (Finset.range (N+1)).filter
      (fun n => n % 2^(k+1) = y.val), (if n.Prime then Real.log (n : ℝ) else 0) := by
    intro y
    rw [hf, hA, h2q]
  obtain ⟨s, hs⟩ : ∃ s : Finset (DirichletCharacter ℂ (2^(k+1))), s = (Finset.univ :
    Finset (DirichletCharacter ℂ (2^(k+1)))).filter (fun χ => χ.conductor = 2^(k+1)) :=
    ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : DirichletCharacter ℂ (2^(k+1)) → ℂ, v = fun χ =>
      (∑ x : (ZMod (2^(k+1)))ˣ, (f (x : ZMod (2^(k+1))) : ℂ) * star (χ (x : ZMod (2^(k+1))))) /
        (Real.sqrt ((2^(k+1)).totient : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : DirichletCharacter ℂ (2^(k+1)) → DirichletCharacter ℂ (2^(k+1)) → ℂ,
      H = fun χ ψ => (∑ x : (ZMod (2^(k+1)))ˣ, star (χ (x : ZMod (2^(k+1)))) *
        ψ ((N : ZMod (2^(k+1))) - (x : ZMod (2^(k+1))))) / ((2^(k+1)).totient : ℂ) :=
    ⟨_, rfl⟩
  have hpf := primFormRF2 N k hN hk f s v H hs hv hH
  have hHapp : ∀ χ ψ, H χ ψ = (∑ x : (ZMod (2^(k+1)))ˣ, star (χ (x : ZMod (2^(k+1)))) *
        ψ ((N : ZMod (2^(k+1))) - (x : ZMod (2^(k+1))))) / ((2^(k+1)).totient : ℂ) := by
    intro χ ψ; rw [hH]
  have hfb := formBoundRF (2^(k+1)) (N : ZMod (2^(k+1))) s v H hHapp
  have hφpos : (0 : ℝ) < ((2^(k+1)).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by positivity)
  have hvb : ∀ χ ∈ s, ‖v χ‖ ^ 2 ≤ C^2 * N * (Real.log (2*N : ℝ))^4 / ((2^(k+1)).totient : ℝ) := by
    intro χ hχ
    have hprim : χ.IsPrimitive := by
      rw [hs] at hχ
      exact (DirichletCharacter.isPrimitive_def χ).mpr (Finset.mem_filter.mp hχ).2
    have h1 := htw χ hprim
    rw [← twistRF (2^(k+1)) N f hF χ] at h1
    have h2 : ‖v χ‖ = ‖∑ x : (ZMod (2^(k+1)))ˣ, (f (x : ZMod (2^(k+1))) : ℂ) *
        star (χ (x : ZMod (2^(k+1))))‖ / Real.sqrt ((2^(k+1)).totient : ℝ) := by
      rw [hv, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    rw [h2, div_pow, Real.sq_sqrt hφpos.le]
    refine div_le_div_of_nonneg_right ?_ hφpos.le
    calc _ ≤ (C * Real.sqrt (N : ℝ) * (Real.log (2*N : ℝ))^2)^2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = C^2 * N * (Real.log (2*N : ℝ))^4 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
          ring
  have hcard : (s.card : ℝ) ≤ ((2^(k+1)).totient : ℝ) := by
    have h1 : s.card ≤ Fintype.card (DirichletCharacter ℂ (2^(k+1))) := Finset.card_le_univ s
    have h2 := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ (2^(k+1))
    rw [Nat.card_eq_fintype_card] at h2
    exact_mod_cast h2 ▸ h1
  have hsum : ∑ χ ∈ s, ‖v χ‖ ^ 2 ≤ C^2 * N * (Real.log (2*N : ℝ))^4 := by
    calc ∑ χ ∈ s, ‖v χ‖ ^ 2
        ≤ ∑ χ ∈ s, C^2 * N * (Real.log (2*N : ℝ))^4 / ((2^(k+1)).totient : ℝ) :=
          Finset.sum_le_sum hvb
      _ = s.card * (C^2 * N * (Real.log (2*N : ℝ))^4 / ((2^(k+1)).totient : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((2^(k+1)).totient : ℝ) *
            (C^2 * N * (Real.log (2*N : ℝ))^4 / ((2^(k+1)).totient : ℝ)) := by
          refine mul_le_mul_of_nonneg_right hcard ?_
          positivity
      _ = _ := by field_simp
  have hodd : |∑ r ∈ (Finset.range (2^k)).filter (fun r => Odd r),
      (if (N+2*2^k-r) % (2*2^k) < 2^k then (1 : ℝ) else -1) *
        (A (2*2^k) r - A (2*2^k) (r+2^k)) *
        (A (2*2^k) ((N+2^k-r) % 2^k) - A (2*2^k) ((N+2^k-r) % 2^k + 2^k))| ≤
      2 * (C^2 * N * (Real.log (2*N : ℝ))^4) := by
    have hconv : (∑ r ∈ (Finset.range (2^k)).filter (fun r => Odd r),
      (if (N+2*2^k-r) % (2*2^k) < 2^k then (1 : ℝ) else -1) *
        (A (2*2^k) r - A (2*2^k) (r+2^k)) *
        (A (2*2^k) ((N+2^k-r) % 2^k) - A (2*2^k) ((N+2^k-r) % 2^k + 2^k))) =
        2 * (∑ χ ∈ s, ∑ ψ ∈ s, star (v χ) * H χ ψ * v ψ).re := by
      rw [← hpf]
      refine Finset.sum_congr rfl (fun r hr => ?_)
      have hrq : r < 2^k := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
      have hmod : (N+2^k-r) % 2^k < 2^k := Nat.mod_lt _ hq0
      rw [hfr r (by omega), hfr (r + 2^k) (by omega), hfr ((N+2^k-r) % 2^k) (by omega),
        hfr ((N+2^k-r) % 2^k + 2^k) (by omega)]
    rw [hconv, abs_mul]
    have : |(2 : ℝ)| = 2 := abs_of_pos two_pos
    rw [this]
    linarith [hfb, hsum]
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range (2^k)) (fun r => Odd r)
    (fun r => (if (N+2*2^k-r) % (2*2^k) < 2^k then (1 : ℝ) else -1) *
        (A (2*2^k) r - A (2*2^k) (r+2^k)) *
        (A (2*2^k) ((N+2^k-r) % 2^k) - A (2*2^k) ((N+2^k-r) % 2^k + 2^k)))
  simp only [Nat.not_odd_iff_even] at hsplit
  rw [← hsplit]
  have heven := ep2wrapRF N k h4 hN hk A hA
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ 2 * (C^2 * N * (Real.log (2*N : ℝ))^4) + (Real.log 2)^2 := add_le_add hodd heven
    _ = _ := by ring

private theorem geoRF (n : ℕ) : ∑ k ∈ Finset.range n, (2 : ℝ)^k = 2^n - 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

private theorem geoSetRF (S : Finset ℕ) (Q : ℝ) (hQ : 0 ≤ Q) (h : ∀ k ∈ S, (2 : ℝ)^k ≤ Q) :
    ∑ k ∈ S, (2 : ℝ)^k ≤ 2 * Q := by
  rcases S.eq_empty_or_nonempty with he | hne
  · rw [he]; simp; linarith
  · set j := S.max' hne with hj
    have hsub : S ⊆ Finset.range (j+1) := by
      intro k hk
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_max' S k hk))
    have h1 : ∑ k ∈ S, (2 : ℝ)^k ≤ ∑ k ∈ Finset.range (j+1), (2 : ℝ)^k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    rw [geoRF, pow_succ] at h1
    have h2 := h j (Finset.max'_mem S hne)
    linarith

set_option maxHeartbeats 1000000 in
theorem Conjectures.Goldbach.DyadicCoarseReflectionBudget :
    ∀ (N K : ℕ) (Q C : ℝ), 4 ≤ N → Even N → N < 2^K → 0 ≤ Q → 2*Q ≤ N → 0 ≤ C →
  (∀ k : ℕ, 1 ≤ k → k < K → (2^k : ℝ) ≤ Q →
    ∀ χ : DirichletCharacter ℂ (2^(k+1)), χ.IsPrimitive →
      ‖∑ n ∈ (Finset.range (N+1)).filter Nat.Prime,
        (Real.log (n : ℝ) : ℂ) * star (χ (n : ZMod (2^(k+1))))‖ ≤
          C * Real.sqrt (N : ℝ) * (Real.log (2*N : ℝ))^2) →
  let w := fun n : ℕ => if n.Prime then Real.log (n : ℝ) else 0
  let A := fun (d r : ℕ) => ∑ n ∈ (Finset.range (N+1)).filter (fun n => n % d = r), w n
  let S := (Finset.range K).filter (fun k => 1 ≤ k ∧ (2^k : ℝ) ≤ Q)
  (∑ k ∈ S,
    let q : ℕ := 2^k
    let D := fun r : ℕ => A (2*q) r - A (2*q) (r+q)
    |(q : ℝ) / ((2^K : ℕ) : ℝ) * ∑ r ∈ Finset.range q,
      (if (N+2*q-r) % (2*q) < q then (1 : ℝ) else -1) * D r * D ((N+q-r) % q)|) ≤
    4 * C^2 * Q * (Real.log (2*N : ℝ))^4 + (Real.log 2)^2 := by
  intro N K Q C h4 hN hNK hQ h2Q hC htw w A S
  have hA : ∀ d r, A d r = ∑ n ∈ (Finset.range (N+1)).filter (fun n => n % d = r),
      (if n.Prime then Real.log (n : ℝ) else 0) := fun _ _ => rfl
  have hNpos : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hNK' : (N : ℝ) ≤ 2^K := by exact_mod_cast hNK.le
  have h2K : (0 : ℝ) < 2^K := by positivity
  have hB1 : 0 ≤ 2 * C^2 * N * (Real.log (2*N : ℝ))^4 := by positivity
  have hB2 : 0 ≤ (Real.log 2)^2 := sq_nonneg _
  have hS1 : ∑ k ∈ S, (2 : ℝ)^k ≤ 2 * Q :=
    geoSetRF S Q hQ (fun k hk => (Finset.mem_filter.mp hk).2.2)
  have hS2 : ∑ k ∈ S, (2 : ℝ)^k ≤ 2^K := by
    have hsub : S ⊆ Finset.range K := Finset.filter_subset _ _
    have h1 : ∑ k ∈ S, (2 : ℝ)^k ≤ ∑ k ∈ Finset.range K, (2 : ℝ)^k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    rw [geoRF] at h1
    linarith
  calc (∑ k ∈ S,
      let q : ℕ := 2^k
      let D := fun r : ℕ => A (2*q) r - A (2*q) (r+q)
      |(q : ℝ) / ((2^K : ℕ) : ℝ) * ∑ r ∈ Finset.range q,
        (if (N+2*q-r) % (2*q) < q then (1 : ℝ) else -1) * D r * D ((N+q-r) % q)|)
      ≤ ∑ k ∈ S, (2 : ℝ)^k / 2^K *
          (2 * C^2 * N * (Real.log (2*N : ℝ))^4 + (Real.log 2)^2) := by
        apply Finset.sum_le_sum
        intro k hk
        obtain ⟨hkK, hk1, hkQ⟩ := Finset.mem_filter.mp hk
        have hkK' : k < K := Finset.mem_range.mp hkK
        have hl := layerRF N k C h4 hN hk1 hC (htw k hk1 hkK' hkQ) A hA
        dsimp only
        rw [abs_mul, abs_of_nonneg (by positivity)]
        push_cast
        exact mul_le_mul_of_nonneg_left hl (by positivity)
    _ = (∑ k ∈ S, (2 : ℝ)^k) / 2^K *
          (2 * C^2 * N * (Real.log (2*N : ℝ))^4 + (Real.log 2)^2) := by
        rw [Finset.sum_div, Finset.sum_mul]
    _ ≤ 4 * C^2 * Q * (Real.log (2*N : ℝ))^4 + (Real.log 2)^2 := by
        have hσ1 : (∑ k ∈ S, (2 : ℝ)^k) / 2^K ≤ 2 * Q / 2^K :=
          div_le_div_of_nonneg_right hS1 h2K.le
        have hσ2 : (∑ k ∈ S, (2 : ℝ)^k) / 2^K ≤ 1 := (div_le_one h2K).mpr hS2
        have hX : 0 ≤ 4 * C^2 * Q * (Real.log (2*N : ℝ))^4 := by positivity
        have h3 : 2 * Q / 2^K * (2 * C^2 * N * (Real.log (2*N : ℝ))^4) =
            4 * C^2 * Q * (Real.log (2*N : ℝ))^4 * (N / 2^K) := by
          field_simp
          ring
        have h4' : 4 * C^2 * Q * (Real.log (2*N : ℝ))^4 * (N / 2^K) ≤
            4 * C^2 * Q * (Real.log (2*N : ℝ))^4 :=
          mul_le_of_le_one_right hX ((div_le_one h2K).mpr hNK')
        rw [mul_add]
        have h5 := mul_le_mul_of_nonneg_right hσ1 hB1
        have h6 := mul_le_mul_of_nonneg_right hσ2 hB2
        linarith

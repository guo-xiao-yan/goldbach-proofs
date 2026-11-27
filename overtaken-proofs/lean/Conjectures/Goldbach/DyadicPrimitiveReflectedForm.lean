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
theorem Conjectures.Goldbach.DyadicPrimitiveReflectedForm :
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

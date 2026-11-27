import Mathlib




private def fe_fiber (m : ℕ) (N : ℕ) (r : ZMod m) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun n => (n : ZMod m) = r)

private def fe_wsum (m : ℕ) (N : ℕ) (w : ℕ → ℂ) (r : ZMod m) : ℂ :=
  ∑ n ∈ fe_fiber m N r, w n

private theorem fe_mem_fiber (m : ℕ) [NeZero m] {N : ℕ} {r : ZMod m} {n : ℕ} (hn : n ∈ fe_fiber m N r) :
    n < N + 1 ∧ (n : ZMod m) = r := by
  simp only [fe_fiber, Finset.mem_filter, Finset.mem_range] at hn
  exact hn

private theorem fe_fiber_card (m : ℕ) [NeZero m] (N : ℕ) (r : ZMod m) : (fe_fiber m N r).card ≤ 1 + N / m := by
  have hinj : Set.InjOn (fun n : ℕ => n / m) (fe_fiber m N r : Set ℕ) := by
    intro a ha b hb hab
    replace hab : a / m = b / m := hab
    have ha' := fe_mem_fiber m ha
    have hb' := fe_mem_fiber m hb
    have hmod : a % m = b % m :=
      (ZMod.natCast_eq_natCast_iff' a b m).mp (by rw [ha'.2, hb'.2])
    calc a = m * (a / m) + a % m := (Nat.div_add_mod a m).symm
      _ = m * (b / m) + b % m := by rw [hab, hmod]
      _ = b := Nat.div_add_mod b m
  have himg : (fe_fiber m N r).image (fun n : ℕ => n / m) ⊆ Finset.range (1 + N / m) := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    have h1 := (fe_mem_fiber m hn).1
    have h2 : n / m ≤ N / m := Nat.div_le_div_right (Nat.le_of_lt_succ h1)
    exact Finset.mem_range.mpr (by omega)
  calc (fe_fiber m N r).card = ((fe_fiber m N r).image (fun n : ℕ => n / m)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (1 + N / m)).card := Finset.card_le_card himg
    _ = 1 + N / m := Finset.card_range _

private theorem fe_fiber_sum (m : ℕ) [NeZero m] (N : ℕ) {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    (∑ n ∈ Finset.range (N + 1), f n) = ∑ r : ZMod m, ∑ n ∈ fe_fiber m N r, f n := by
  have h1 : ∀ n ∈ Finset.range (N + 1), f n = ∑ r : ZMod m, if (n : ZMod m) = r then f n else 0 := by
    intro n _
    simp
  calc (∑ n ∈ Finset.range (N + 1), f n)
      = ∑ n ∈ Finset.range (N + 1), ∑ r : ZMod m, if (n : ZMod m) = r then f n else 0 :=
        Finset.sum_congr rfl h1
    _ = ∑ r : ZMod m, ∑ n ∈ Finset.range (N + 1), if (n : ZMod m) = r then f n else 0 :=
        Finset.sum_comm
    _ = ∑ r : ZMod m, ∑ n ∈ fe_fiber m N r, f n := by
        apply Finset.sum_congr rfl
        intro r _
        rw [fe_fiber, Finset.sum_filter]

private theorem fe_cs_sum (t : Finset ℕ) (z : ℕ → ℂ) :
    ‖∑ i ∈ t, z i‖ ^ 2 ≤ (t.card : ℝ) * ∑ i ∈ t, ‖z i‖ ^ 2 := by
  have hnorm : ∀ x : ℂ, ‖x‖ ^ 2 = x.re ^ 2 + x.im ^ 2 := by
    intro x
    have := Complex.sq_norm_sub_sq_re x
    linarith
  have h1 : ‖∑ i ∈ t, z i‖ ^ 2 = (∑ i ∈ t, (z i).re) ^ 2 + (∑ i ∈ t, (z i).im) ^ 2 := by
    rw [hnorm]
    simp only [Complex.re_sum, Complex.im_sum]
  have h2 : (∑ i ∈ t, (z i).re) ^ 2 ≤ (t.card : ℝ) * ∑ i ∈ t, (z i).re ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h3 : (∑ i ∈ t, (z i).im) ^ 2 ≤ (t.card : ℝ) * ∑ i ∈ t, (z i).im ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h4 : (∑ i ∈ t, ‖z i‖ ^ 2) = (∑ i ∈ t, (z i).re ^ 2) + ∑ i ∈ t, (z i).im ^ 2 := by
    simp_rw [hnorm]
    rw [Finset.sum_add_distrib]
  have h5 : (t.card : ℝ) * ((∑ i ∈ t, (z i).re ^ 2) + ∑ i ∈ t, (z i).im ^ 2)
      = (t.card : ℝ) * ∑ i ∈ t, (z i).re ^ 2 + (t.card : ℝ) * ∑ i ∈ t, (z i).im ^ 2 := by ring
  rw [h1, h4, h5]
  linarith [h2, h3]

private theorem fe_units_sum (m : ℕ) [NeZero m] {M : Type*} [AddCommMonoid M] (g : ZMod m → M) :
    (∑ a : (ZMod m)ˣ, g (a : ZMod m))
      = ∑ r ∈ (Finset.univ : Finset (ZMod m)).filter IsUnit, g r := by
  refine Finset.sum_bij (fun (a : (ZMod m)ˣ) _ => (a : ZMod m)) ?_ ?_ ?_ ?_
  · intro a _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.isUnit⟩
  · intro a₁ _ a₂ _ h
    exact Units.val_injective h
  · intro r hr
    have hu : IsUnit r := (Finset.mem_filter.mp hr).2
    exact ⟨hu.unit, Finset.mem_univ _, hu.unit_spec⟩
  · intro a _
    rfl

private theorem fe_sum_units_eq (m : ℕ) [NeZero m] (g : ZMod m → ℂ) (h0 : ∀ r, ¬ IsUnit r → g r = 0) :
    (∑ a : (ZMod m)ˣ, g (a : ZMod m)) = ∑ r : ZMod m, g r := by
  rw [fe_units_sum m g, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : IsUnit r
  · simp [h]
  · simp [h, h0 r h]

private theorem fe_sum_units_le (m : ℕ) [NeZero m] (g : ZMod m → ℝ) (h0 : ∀ r, 0 ≤ g r) :
    (∑ a : (ZMod m)ˣ, g (a : ZMod m)) ≤ ∑ r : ZMod m, g r := by
  rw [fe_units_sum m g]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => h0 i)

private theorem fe_orth2 (m : ℕ) [NeZero m] (a b : (ZMod m)ˣ) :
    (∑ χ : DirichletCharacter ℂ m, χ (a : ZMod m) * star (χ (b : ZMod m))) =
      if a = b then (m.totient : ℂ) else 0 := by
  have hcb (χ : DirichletCharacter ℂ m) : star (χ (b : ZMod m)) = χ ((b : ZMod m)⁻¹) := by
    rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]
  have h1 : (∑ χ : DirichletCharacter ℂ m, χ (a : ZMod m) * star (χ (b : ZMod m))) =
      ∑ χ : DirichletCharacter ℂ m, χ ((b : ZMod m)⁻¹) * χ (a : ZMod m) := by
    apply Finset.sum_congr rfl
    intro χ _
    rw [hcb χ, mul_comm]
  rw [h1, DirichletCharacter.sum_char_inv_mul_char_eq ℂ b.isUnit (a : ZMod m)]
  by_cases h : (b : ZMod m) = (a : ZMod m)
  · rw [if_pos h, if_pos (Units.val_inj.mp h).symm]
  · rw [if_neg h, if_neg (fun hab => h (by rw [hab]))]

private theorem fe_parseval_star (m : ℕ) [NeZero m] (G : (ZMod m)ˣ → ℂ) :
    (∑ χ : DirichletCharacter ℂ m, ‖∑ a : (ZMod m)ˣ, G a * star (χ (a : ZMod m))‖ ^ 2) =
      (m.totient : ℝ) * ∑ a : (ZMod m)ˣ, ‖G a‖ ^ 2 := by
  have hv (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
  have hex (χ : DirichletCharacter ℂ m) :
      star (∑ a : (ZMod m)ˣ, G a * star (χ (a : ZMod m))) *
          (∑ a : (ZMod m)ˣ, G a * star (χ (a : ZMod m))) =
        ∑ a : (ZMod m)ˣ, ∑ b : (ZMod m)ˣ,
          (star (G a) * G b) * (χ (a : ZMod m) * star (χ (b : ZMod m))) := by
    rw [star_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [star_mul, star_star]
    ring
  have hswap : ∀ (F : (ZMod m)ˣ → (ZMod m)ˣ → DirichletCharacter ℂ m → ℂ),
      (∑ χ : DirichletCharacter ℂ m, ∑ a : (ZMod m)ˣ, ∑ b : (ZMod m)ˣ, F a b χ) =
        ∑ a : (ZMod m)ˣ, ∑ b : (ZMod m)ˣ, ∑ χ : DirichletCharacter ℂ m, F a b χ := by
    intro F
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
  have hmain : (∑ χ : DirichletCharacter ℂ m,
        star (∑ a : (ZMod m)ˣ, G a * star (χ (a : ZMod m))) *
          (∑ a : (ZMod m)ˣ, G a * star (χ (a : ZMod m)))) =
      (m.totient : ℂ) * ∑ a : (ZMod m)ˣ, ((‖G a‖ ^ 2 : ℝ) : ℂ) := by
    simp_rw [hex]
    rw [hswap]
    simp_rw [← Finset.mul_sum, fe_orth2 m]
    have hcol : ∀ a b : (ZMod m)ˣ,
        (star (G a) * G b) * (if a = b then (m.totient : ℂ) else 0) =
          if a = b then ((‖G a‖ ^ 2 : ℝ) : ℂ) * (m.totient : ℂ) else 0 := by
      intro a b
      by_cases h : a = b
      · subst h
        rw [if_pos rfl, if_pos rfl, hv]
      · rw [if_neg h, if_neg h, mul_zero]
    simp_rw [hcol]
    simp
    rw [← Finset.sum_mul, mul_comm]
  have hfinal : (∑ χ : DirichletCharacter ℂ m,
        ((‖∑ a : (ZMod m)ˣ, G a * star (χ (a : ZMod m))‖ ^ 2 : ℝ) : ℂ)) =
      (m.totient : ℂ) * ∑ a : (ZMod m)ˣ, ((‖G a‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hmain]
    apply Finset.sum_congr rfl
    intro χ _
    exact (hv _).symm
  simp only [← Complex.ofReal_sum] at hfinal
  exact_mod_cast hfinal



private theorem fe_CharacterWindowFiberEnergy :
    ∀ (m : ℕ) [NeZero m] (N : ℕ) (w : ℕ → ℂ) (s : Finset (DirichletCharacter ℂ m)),
      (∑ χ ∈ s, ‖(∑ n ∈ Finset.range (N+1), w n * star (χ (n : ZMod m))) /
          (Real.sqrt (m.totient : ℝ) : ℂ)‖^2) ≤
        (1 + (N/m : ℕ) : ℝ) * ∑ n ∈ Finset.range (N+1), ‖w n‖^2 := by
  intro m _ N w s
  classical
  have hm : 0 < m := NeZero.pos m
  have hφ : (0 : ℝ) < (m.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hm
  have hsqrt : ‖((Real.sqrt (m.totient : ℝ) : ℂ))‖ ^ 2 = (m.totient : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sq_sqrt (Nat.cast_nonneg m.totient)
  have hA : ∀ χ : DirichletCharacter ℂ m,
      (∑ n ∈ Finset.range (N+1), w n * star (χ (n : ZMod m))) =
        ∑ a : (ZMod m)ˣ, fe_wsum m N w (a : ZMod m) * star (χ (a : ZMod m)) := by
    intro χ
    rw [fe_fiber_sum m N (fun n => w n * star (χ (n : ZMod m)))]
    have h2 : ∀ r : ZMod m, (∑ n ∈ fe_fiber m N r, w n * star (χ (n : ZMod m))) =
        fe_wsum m N w r * star (χ r) := by
      intro r
      have h3 : ∀ n ∈ fe_fiber m N r, w n * star (χ (n : ZMod m)) = w n * star (χ r) := by
        intro n hn
        rw [(fe_mem_fiber m hn).2]
      calc (∑ n ∈ fe_fiber m N r, w n * star (χ (n : ZMod m)))
          = ∑ n ∈ fe_fiber m N r, w n * star (χ r) := Finset.sum_congr rfl h3
        _ = fe_wsum m N w r * star (χ r) := by
            show ∑ n ∈ fe_fiber m N r, w n * star (χ r) = (∑ n ∈ fe_fiber m N r, w n) * star (χ r)
            rw [Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun r _ => h2 r)]
    have h4 : ∀ r : ZMod m, ¬ IsUnit r → fe_wsum m N w r * star (χ r) = 0 := by
      intro r hr
      rw [MulChar.map_nonunit χ hr, star_zero, mul_zero]
    exact (fe_sum_units_eq m _ h4).symm
  have hP : (∑ χ : DirichletCharacter ℂ m,
      ‖∑ a : (ZMod m)ˣ, fe_wsum m N w (a : ZMod m) * star (χ (a : ZMod m))‖ ^ 2) =
      (m.totient : ℝ) * ∑ a : (ZMod m)ˣ, ‖fe_wsum m N w (a : ZMod m)‖ ^ 2 := fe_parseval_star m _
  have hbound : (∑ χ ∈ s, ‖(∑ n ∈ Finset.range (N+1), w n * star (χ (n : ZMod m))) /
      (Real.sqrt (m.totient : ℝ) : ℂ)‖ ^ 2) ≤
      ∑ a : (ZMod m)ˣ, ‖fe_wsum m N w (a : ZMod m)‖ ^ 2 := by
    have hdiv : ∀ χ : DirichletCharacter ℂ m,
        ‖(∑ n ∈ Finset.range (N+1), w n * star (χ (n : ZMod m))) /
            (Real.sqrt (m.totient : ℝ) : ℂ)‖ ^ 2 =
          ‖∑ n ∈ Finset.range (N+1), w n * star (χ (n : ZMod m))‖ ^ 2 / (m.totient : ℝ) := by
      intro χ
      rw [norm_div, div_pow, hsqrt]
    have hsd : (∑ χ ∈ s, ‖∑ a : (ZMod m)ˣ, fe_wsum m N w (a : ZMod m) *
        star (χ (a : ZMod m))‖ ^ 2 / (m.totient : ℝ)) =
        (∑ χ ∈ s, ‖∑ a : (ZMod m)ˣ, fe_wsum m N w (a : ZMod m) *
          star (χ (a : ZMod m))‖ ^ 2) / (m.totient : ℝ) := by
      simp_rw [div_eq_mul_inv, Finset.sum_mul]
    have hsub : (∑ χ ∈ s, ‖∑ a : (ZMod m)ˣ, fe_wsum m N w (a : ZMod m) *
        star (χ (a : ZMod m))‖ ^ 2) ≤
        ∑ χ : DirichletCharacter ℂ m, ‖∑ a : (ZMod m)ˣ, fe_wsum m N w (a : ZMod m) *
          star (χ (a : ZMod m))‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun i _ _ => sq_nonneg _)
    simp_rw [hdiv, hA]
    rw [hsd, div_le_iff₀ hφ]
    calc (∑ χ ∈ s, ‖∑ a : (ZMod m)ˣ, fe_wsum m N w (a : ZMod m) * star (χ (a : ZMod m))‖ ^ 2)
        ≤ ∑ χ : DirichletCharacter ℂ m, ‖∑ a : (ZMod m)ˣ, fe_wsum m N w (a : ZMod m) *
            star (χ (a : ZMod m))‖ ^ 2 := hsub
      _ = (m.totient : ℝ) * ∑ a : (ZMod m)ˣ, ‖fe_wsum m N w (a : ZMod m)‖ ^ 2 := hP
      _ = (∑ a : (ZMod m)ˣ, ‖fe_wsum m N w (a : ZMod m)‖ ^ 2) * (m.totient : ℝ) := by ring
  have hfin : (∑ r : ZMod m, ‖fe_wsum m N w r‖ ^ 2) ≤
      (1 + (N / m : ℕ) : ℝ) * ∑ n ∈ Finset.range (N+1), ‖w n‖ ^ 2 := by
    have hcs : ∀ r : ZMod m, ‖fe_wsum m N w r‖ ^ 2 ≤
        ((fe_fiber m N r).card : ℝ) * ∑ n ∈ fe_fiber m N r, ‖w n‖ ^ 2 := by
      intro r
      exact fe_cs_sum (fe_fiber m N r) w
    calc (∑ r : ZMod m, ‖fe_wsum m N w r‖ ^ 2)
        ≤ ∑ r : ZMod m, ((fe_fiber m N r).card : ℝ) * ∑ n ∈ fe_fiber m N r, ‖w n‖ ^ 2 :=
          Finset.sum_le_sum (fun r _ => hcs r)
      _ ≤ ∑ r : ZMod m, (1 + (N / m : ℕ) : ℝ) * ∑ n ∈ fe_fiber m N r, ‖w n‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro r _
          apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun n _ => sq_nonneg _))
          calc ((fe_fiber m N r).card : ℝ) ≤ ((1 + N / m : ℕ) : ℝ) := by exact_mod_cast fe_fiber_card m N r
            _ = (1 + (N / m : ℕ) : ℝ) := by simp
      _ = (1 + (N / m : ℕ) : ℝ) * ∑ r : ZMod m, ∑ n ∈ fe_fiber m N r, ‖w n‖ ^ 2 := by
          rw [Finset.mul_sum]
      _ = (1 + (N / m : ℕ) : ℝ) * ∑ n ∈ Finset.range (N+1), ‖w n‖ ^ 2 := by
          rw [fe_fiber_sum m N]
  calc (∑ χ ∈ s, ‖(∑ n ∈ Finset.range (N+1), w n * star (χ (n : ZMod m))) /
      (Real.sqrt (m.totient : ℝ) : ℂ)‖ ^ 2)
      ≤ ∑ a : (ZMod m)ˣ, ‖fe_wsum m N w (a : ZMod m)‖ ^ 2 := hbound
    _ ≤ ∑ r : ZMod m, ‖fe_wsum m N w r‖ ^ 2 := fe_sum_units_le m _ (fun r => sq_nonneg _)
    _ ≤ (1 + (N / m : ℕ) : ℝ) * ∑ n ∈ Finset.range (N+1), ‖w n‖ ^ 2 := hfin

section



variable {m : ℕ} [NeZero m]

private lemma rc_totient_pos_real : (0 : ℝ) < (m.totient : ℝ) := by
  exact_mod_cast Nat.totient_pos.mpr (NeZero.pos m)

private lemma rc_totient_cast : ((m.totient : ℕ) : ℂ) = ((m.totient : ℝ) : ℂ) := by
  simp

private lemma rc_star_mul_self (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]

private lemma rc_sum_interchange {α β : Type*} [Fintype α] [Fintype β] {M : Type*} [AddCommMonoid M]
    (f : α → β → M) : (∑ a : α, ∑ b : β, f a b) = ∑ b : β, ∑ a : α, f a b := by
  conv_lhs => rw [Finset.sum_comm]

private lemma rc_sum_units_eq_sum {M : Type*} [AddCommMonoid M] (f : ZMod m → M)
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

private lemma rc_sum_char_units (θ : DirichletCharacter ℂ m) :
    ∑ x : (ZMod m)ˣ, θ (x : ZMod m) = if θ = 1 then ((m.totient : ℝ) : ℂ) else 0 := by
  have hz : ∀ a : ZMod m, ¬IsUnit a → θ a = 0 := fun a ha => MulChar.map_nonunit θ ha
  rw [rc_sum_units_eq_sum (fun a => θ a) hz]
  by_cases h : θ = 1
  · rw [if_pos h, h, MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient, rc_totient_cast]
  · rw [if_neg h, MulChar.sum_eq_zero_of_ne_one h]

private lemma rc_star_char (χ : DirichletCharacter ℂ m) (x : (ZMod m)ˣ) :
    star (χ (x : ZMod m)) = χ ((x : ZMod m)⁻¹) := by
  rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]

private lemma rc_orth1 (x y : (ZMod m)ˣ) :
    ∑ χ : DirichletCharacter ℂ m, star (χ (x : ZMod m)) * χ (y : ZMod m)
      = if x = y then ((m.totient : ℝ) : ℂ) else 0 := by
  simp_rw [rc_star_char]
  rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ x.isUnit (y : ZMod m)]
  by_cases hxy : (x : ZMod m) = (y : ZMod m)
  · rw [if_pos hxy, if_pos (Units.val_inj.mp hxy), rc_totient_cast]
  · rw [if_neg hxy, if_neg (fun h => hxy (Units.val_inj.mpr h))]

private lemma rc_orth2 (χ ψ : DirichletCharacter ℂ m) :
    ∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (x : ZMod m)
      = if χ = ψ then ((m.totient : ℝ) : ℂ) else 0 := by
  have h1 (x : (ZMod m)ˣ) :
      star (χ (x : ZMod m)) * ψ (x : ZMod m) = (χ⁻¹ * ψ) (x : ZMod m) := by
    rw [MulChar.mul_apply, MulChar.star_apply']
  have h2 : ∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (x : ZMod m)
      = ∑ x : (ZMod m)ˣ, (χ⁻¹ * ψ) (x : ZMod m) := Finset.sum_congr rfl (fun x _ => h1 x)
  rw [h2, rc_sum_char_units]
  by_cases h : χ = ψ
  · subst h
    simp
  · rw [if_neg h, if_neg (fun h2 => h (inv_mul_eq_one.mp h2))]

private lemma rc_parseval_complex (g : (ZMod m)ˣ → ℂ) :
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
    simp_rw [rc_orth1]
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

private lemma rc_parseval (g : (ZMod m)ˣ → ℂ) :
    ∑ χ : DirichletCharacter ℂ m, ‖∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * g x‖ ^ 2
      = (m.totient : ℝ) * ∑ x : (ZMod m)ˣ, ‖g x‖ ^ 2 := by
  have h := rc_parseval_complex g
  simp_rw [rc_star_mul_self] at h
  have h2 : ((∑ χ : DirichletCharacter ℂ m,
        ‖∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * g x‖ ^ 2 : ℝ) : ℂ)
      = (((m.totient : ℝ) * ∑ x : (ZMod m)ˣ, ‖g x‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_sum]
    exact h
  exact Complex.ofReal_injective h2

private lemma rc_sum_swap (N : ZMod m) (A B : ZMod m → ℂ)
    (hA : ∀ a, ¬IsUnit a → A a = 0) (hB : ∀ a, ¬IsUnit a → B a = 0) :
    ∑ x : (ZMod m)ˣ, A (x : ZMod m) * B (N - (x : ZMod m))
      = ∑ x : (ZMod m)ˣ, B (x : ZMod m) * A (N - (x : ZMod m)) := by
  have h1 : ∀ a : ZMod m, ¬IsUnit a → A a * B (N - a) = 0 := by
    intro a ha
    rw [hA a ha, zero_mul]
  have h2 : ∀ a : ZMod m, ¬IsUnit a → B a * A (N - a) = 0 := by
    intro a ha
    rw [hB a ha, zero_mul]
  rw [rc_sum_units_eq_sum (fun a => A a * B (N - a)) h1,
    rc_sum_units_eq_sum (fun a => B a * A (N - a)) h2]
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

private lemma rc_sum_reflect_le (N : ZMod m) (F : ZMod m → ℂ) (hF : ∀ a, ¬IsUnit a → F a = 0) :
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
        (rc_sum_units_eq_sum (fun a : ZMod m => ‖F a‖ ^ 2) hf0).symm

private lemma rc_synth_norm (w : DirichletCharacter ℂ m → ℂ) :
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
            star (χ (x : ZMod m)) * (w ψ * ψ (x : ZMod m)) := rc_sum_interchange _
      _ = ∑ ψ : DirichletCharacter ℂ m, w ψ
            * ∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (x : ZMod m) := by
          refine Finset.sum_congr rfl (fun ψ _ => ?_)
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun x _ => by ring)
      _ = ∑ ψ : DirichletCharacter ℂ m,
            w ψ * (if χ = ψ then ((m.totient : ℝ) : ℂ) else 0) := by
          simp_rw [rc_orth2]
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
  have hp := rc_parseval (fun x : (ZMod m)ˣ => ∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (x : ZMod m))
  have hkey1 : ∀ χ : DirichletCharacter ℂ m,
      ‖∑ x : (ZMod m)ˣ, star (χ (x : ZMod m))
        * ∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (x : ZMod m)‖ ^ 2
      = (m.totient : ℝ) ^ 2 * ‖w χ‖ ^ 2 := by
    intro χ
    rw [hB χ, norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt rc_totient_pos_real), mul_pow]
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
  exact (mul_left_cancel₀ (ne_of_gt rc_totient_pos_real) h3).symm

private lemma rc_main_bound (N : ZMod m) (w : DirichletCharacter ℂ m → ℂ) :
    ∑ χ : DirichletCharacter ℂ m,
        ‖∑ ψ : DirichletCharacter ℂ m,
            ((∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (N - (x : ZMod m)))
              / (m.totient : ℂ)) * w ψ‖ ^ 2
      ≤ ∑ ψ : DirichletCharacter ℂ m, ‖w ψ‖ ^ 2 := by
  have hφ : (m.totient : ℝ) ≠ 0 := ne_of_gt rc_totient_pos_real
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
              (star (χ (x : ZMod m)) * ψ (N - (x : ZMod m))) * w ψ := rc_sum_interchange _
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
          rc_parseval (fun x : (ZMod m)ˣ => ∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (N - (x : ZMod m)))]
    _ ≤ ((m.totient : ℝ) * ∑ x : (ZMod m)ˣ,
          ‖∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (x : ZMod m)‖ ^ 2) / (m.totient : ℝ) ^ 2 := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt rc_totient_pos_real)
        exact rc_sum_reflect_le N (fun a : ZMod m => ∑ ψ : DirichletCharacter ℂ m, w ψ * ψ a) hFz
    _ = ∑ ψ : DirichletCharacter ℂ m, ‖w ψ‖ ^ 2 := by
        rw [rc_synth_norm w]
        field_simp


private theorem rc_ReflectionCharacterContraction :
    ∀ (m : ℕ) [NeZero m] (N : ZMod m),
      let H : Matrix (DirichletCharacter ℂ m) (DirichletCharacter ℂ m) ℂ := fun χ ψ =>
        (∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (N - (x : ZMod m))) / (m.totient : ℂ)
      H.IsHermitian ∧ ∀ (s : Finset (DirichletCharacter ℂ m)) (v : DirichletCharacter ℂ m → ℂ),
        (∑ χ ∈ s, ‖∑ ψ ∈ s, H χ ψ * v ψ‖^2) ≤ ∑ χ ∈ s, ‖v χ‖^2 := by
  intro m _ N
  dsimp only
  refine ⟨?_, ?_⟩
  · refine Matrix.IsHermitian.ext (fun χ ψ => ?_)
    show star ((∑ x : (ZMod m)ˣ, star (ψ (x : ZMod m)) * χ (N - (x : ZMod m))) / (m.totient : ℂ))
        = (∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (N - (x : ZMod m))) / (m.totient : ℂ)
    have hstar : star ((m.totient : ℕ) : ℂ) = ((m.totient : ℕ) : ℂ) := star_natCast _
    rw [star_div₀, hstar, star_sum]
    have h1 : ∑ x : (ZMod m)ˣ, star (star (ψ (x : ZMod m)) * χ (N - (x : ZMod m)))
        = ∑ x : (ZMod m)ˣ, ψ (x : ZMod m) * star (χ (N - (x : ZMod m))) := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [star_mul, star_star]
      ring
    rw [h1]
    have hsw : ∑ x : (ZMod m)ˣ, ψ (x : ZMod m) * star (χ (N - (x : ZMod m)))
        = ∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (N - (x : ZMod m)) :=
      rc_sum_swap N
        (fun a : ZMod m => ψ a) (fun a : ZMod m => star (χ a))
        (fun a ha => MulChar.map_nonunit ψ ha)
        (fun a ha => by rw [MulChar.map_nonunit χ ha, star_zero])
    rw [hsw]
  · intro s v
    classical
    show (∑ χ ∈ s, ‖∑ ψ ∈ s, ((∑ x : (ZMod m)ˣ, star (χ (x : ZMod m))
        * ψ (N - (x : ZMod m))) / (m.totient : ℂ)) * v ψ‖ ^ 2) ≤ ∑ χ ∈ s, ‖v χ‖ ^ 2
    have hfilt : (Finset.univ : Finset (DirichletCharacter ℂ m)).filter (· ∈ s) = s := by
      ext ψ
      simp
    have hsub (f : DirichletCharacter ℂ m → ℂ) :
        ∑ ψ : DirichletCharacter ℂ m, f ψ * (if ψ ∈ s then v ψ else 0) = ∑ ψ ∈ s, f ψ * v ψ := by
      have h1 : ∀ ψ : DirichletCharacter ℂ m, f ψ * (if ψ ∈ s then v ψ else 0)
          = if ψ ∈ s then f ψ * v ψ else 0 := by
        intro ψ
        by_cases h : ψ ∈ s <;> simp [h]
      simp_rw [h1]
      rw [← Finset.sum_filter, hfilt]
    have hnorm : ∑ ψ : DirichletCharacter ℂ m, ‖(if ψ ∈ s then v ψ else 0)‖ ^ 2
        = ∑ ψ ∈ s, ‖v ψ‖ ^ 2 := by
      have h1 : ∀ ψ : DirichletCharacter ℂ m, ‖(if ψ ∈ s then v ψ else 0)‖ ^ 2
          = if ψ ∈ s then ‖v ψ‖ ^ 2 else 0 := by
        intro ψ
        by_cases h : ψ ∈ s <;> simp [h]
      simp_rw [h1]
      rw [← Finset.sum_filter, hfilt]
    have hmain := rc_main_bound N
      (fun ψ => if ψ ∈ s then v ψ else 0)
    calc ∑ χ ∈ s, ‖∑ ψ ∈ s, ((∑ x : (ZMod m)ˣ, star (χ (x : ZMod m))
          * ψ (N - (x : ZMod m))) / (m.totient : ℂ)) * v ψ‖ ^ 2
        ≤ ∑ χ : DirichletCharacter ℂ m, ‖∑ ψ ∈ s, ((∑ x : (ZMod m)ˣ, star (χ (x : ZMod m))
            * ψ (N - (x : ZMod m))) / (m.totient : ℂ)) * v ψ‖ ^ 2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
          intro i _ _
          exact sq_nonneg _
      _ = ∑ χ : DirichletCharacter ℂ m, ‖∑ ψ : DirichletCharacter ℂ m,
            ((∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (N - (x : ZMod m)))
              / (m.totient : ℂ)) * (if ψ ∈ s then v ψ else 0)‖ ^ 2 := by
          refine Finset.sum_congr rfl (fun χ _ => ?_)
          rw [hsub]
      _ ≤ ∑ ψ : DirichletCharacter ℂ m, ‖(if ψ ∈ s then v ψ else 0)‖ ^ 2 := hmain
      _ = ∑ χ ∈ s, ‖v χ‖ ^ 2 := hnorm
end

private theorem qf_abs {ι : Type*} (s : Finset ι) (H : ι → ι → ℂ)
    (hH : ∀ v : ι → ℂ, ∑ χ ∈ s, ‖∑ ψ ∈ s, H χ ψ * v ψ‖ ^ 2 ≤ ∑ χ ∈ s, ‖v χ‖ ^ 2)
    (x y : ι → ℂ) :
    ‖∑ χ ∈ s, ∑ ψ ∈ s, star (x χ) * H χ ψ * y ψ‖ ≤
      Real.sqrt (∑ χ ∈ s, ‖x χ‖ ^ 2) * Real.sqrt (∑ χ ∈ s, ‖y χ‖ ^ 2) := by
  have h1 : ∑ χ ∈ s, ∑ ψ ∈ s, star (x χ) * H χ ψ * y ψ =
      ∑ χ ∈ s, star (x χ) * ∑ ψ ∈ s, H χ ψ * y ψ := by
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun ψ _ => by ring)
  rw [h1]
  calc ‖∑ χ ∈ s, star (x χ) * ∑ ψ ∈ s, H χ ψ * y ψ‖
      ≤ ∑ χ ∈ s, ‖star (x χ) * ∑ ψ ∈ s, H χ ψ * y ψ‖ := norm_sum_le _ _
    _ = ∑ χ ∈ s, ‖x χ‖ * ‖∑ ψ ∈ s, H χ ψ * y ψ‖ := by
        refine Finset.sum_congr rfl (fun χ _ => ?_)
        rw [norm_mul, norm_star]
    _ ≤ Real.sqrt (∑ χ ∈ s, ‖x χ‖ ^ 2) * Real.sqrt (∑ χ ∈ s, ‖∑ ψ ∈ s, H χ ψ * y ψ‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt s _ _
    _ ≤ Real.sqrt (∑ χ ∈ s, ‖x χ‖ ^ 2) * Real.sqrt (∑ χ ∈ s, ‖y χ‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hH y)) (Real.sqrt_nonneg _)

private theorem qf_diff {ι : Type*} (s : Finset ι) (H : ι → ι → ℂ)
    (hH : ∀ v : ι → ℂ, ∑ χ ∈ s, ‖∑ ψ ∈ s, H χ ψ * v ψ‖ ^ 2 ≤ ∑ χ ∈ s, ‖v χ‖ ^ 2)
    (a b : ι → ℂ) :
    |(∑ χ ∈ s, ∑ ψ ∈ s, star (a χ) * H χ ψ * a ψ).re - (∑ χ ∈ s, ∑ ψ ∈ s, star (b χ) * H χ ψ * b ψ).re| ≤
      Real.sqrt (∑ χ ∈ s, ‖a χ - b χ‖ ^ 2) *
        (Real.sqrt (∑ χ ∈ s, ‖a χ‖ ^ 2) + Real.sqrt (∑ χ ∈ s, ‖b χ‖ ^ 2)) := by
  have hid : (∑ χ ∈ s, ∑ ψ ∈ s, star (a χ) * H χ ψ * a ψ) -
      (∑ χ ∈ s, ∑ ψ ∈ s, star (b χ) * H χ ψ * b ψ) =
      (∑ χ ∈ s, ∑ ψ ∈ s, star ((a - b) χ) * H χ ψ * a ψ) +
      (∑ χ ∈ s, ∑ ψ ∈ s, star (b χ) * H χ ψ * (a - b) ψ) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun χ _ => Finset.sum_congr rfl (fun ψ _ => ?_))
    simp only [Pi.sub_apply, star_sub]
    ring
  rw [← Complex.sub_re, hid, Complex.add_re]
  have e1 := qf_abs s H hH (a - b) a
  have e2 := qf_abs s H hH b (a - b)
  have n1 : ∀ z : ℂ, |z.re| ≤ ‖z‖ := fun z => Complex.abs_re_le_norm z
  have hr : (fun χ => (a - b) χ) = fun χ => a χ - b χ := rfl
  simp only [Pi.sub_apply] at e1 e2
  calc |(∑ χ ∈ s, ∑ ψ ∈ s, star ((a - b) χ) * H χ ψ * a ψ).re +
        (∑ χ ∈ s, ∑ ψ ∈ s, star (b χ) * H χ ψ * (a - b) ψ).re|
      ≤ |(∑ χ ∈ s, ∑ ψ ∈ s, star ((a - b) χ) * H χ ψ * a ψ).re| +
        |(∑ χ ∈ s, ∑ ψ ∈ s, star (b χ) * H χ ψ * (a - b) ψ).re| := abs_add_le _ _
    _ ≤ _ := by
        have := n1 (∑ χ ∈ s, ∑ ψ ∈ s, star ((a - b) χ) * H χ ψ * a ψ)
        have := n1 (∑ χ ∈ s, ∑ ψ ∈ s, star (b χ) * H χ ψ * (a - b) ψ)
        simp only [Pi.sub_apply] at *
        nlinarith [e1, e2]

private lemma pm_energy (m : ℕ) [NeZero m] (N : ℕ) (s : Finset (DirichletCharacter ℂ m)) (u : ℕ → ℝ) :
    ∑ χ ∈ s, ‖(∑ n ∈ Finset.range (N+1), (u n : ℂ) * star (χ (n : ZMod m))) /
        (Real.sqrt (m.totient : ℝ) : ℂ)‖ ^ 2 ≤
      (1 + (N/m : ℕ) : ℝ) * ∑ n ∈ Finset.range (N+1), (u n) ^ 2 := by
  have h := fe_CharacterWindowFiberEnergy m N (fun n => (u n : ℂ)) s
  simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using h


private theorem qf_diff2 {ι : Type*} (s : Finset ι) (H : ι → ι → ℂ)
    (hH : ∀ v : ι → ℂ, ∑ χ ∈ s, ‖∑ ψ ∈ s, H χ ψ * v ψ‖ ^ 2 ≤ ∑ χ ∈ s, ‖v χ‖ ^ 2)
    (a b : ι → ℂ) :
    |(∑ χ ∈ s, ∑ ψ ∈ s, star (a χ) * H χ ψ * a ψ).re - (∑ χ ∈ s, ∑ ψ ∈ s, star (b χ) * H χ ψ * b ψ).re| ≤
      2 * Real.sqrt (∑ χ ∈ s, ‖a χ - b χ‖ ^ 2) * Real.sqrt (∑ χ ∈ s, ‖a χ‖ ^ 2) +
        Real.sqrt (∑ χ ∈ s, ‖a χ - b χ‖ ^ 2) ^ 2 := by
  have hid : (∑ χ ∈ s, ∑ ψ ∈ s, star (a χ) * H χ ψ * a ψ) -
      (∑ χ ∈ s, ∑ ψ ∈ s, star (b χ) * H χ ψ * b ψ) =
      (∑ χ ∈ s, ∑ ψ ∈ s, star ((a - b) χ) * H χ ψ * a ψ) +
      (∑ χ ∈ s, ∑ ψ ∈ s, star (a χ) * H χ ψ * (a - b) ψ) -
      (∑ χ ∈ s, ∑ ψ ∈ s, star ((a - b) χ) * H χ ψ * (a - b) ψ) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun χ _ => Finset.sum_congr rfl (fun ψ _ => ?_))
    simp only [Pi.sub_apply, star_sub]
    ring
  rw [← Complex.sub_re, hid, Complex.sub_re, Complex.add_re]
  have e1 := qf_abs s H hH (a - b) a
  have e2 := qf_abs s H hH a (a - b)
  have e3 := qf_abs s H hH (a - b) (a - b)
  simp only [Pi.sub_apply] at e1 e2 e3
  have n1 : ∀ z : ℂ, |z.re| ≤ ‖z‖ := fun z => Complex.abs_re_le_norm z
  have h1 := n1 (∑ χ ∈ s, ∑ ψ ∈ s, star ((a - b) χ) * H χ ψ * a ψ)
  have h2 := n1 (∑ χ ∈ s, ∑ ψ ∈ s, star (a χ) * H χ ψ * (a - b) ψ)
  have h3 := n1 (∑ χ ∈ s, ∑ ψ ∈ s, star ((a - b) χ) * H χ ψ * (a - b) ψ)
  simp only [Pi.sub_apply] at h1 h2 h3
  have hsq : Real.sqrt (∑ χ ∈ s, ‖a χ - b χ‖ ^ 2) ^ 2 = Real.sqrt (∑ χ ∈ s, ‖a χ - b χ‖ ^ 2) *
      Real.sqrt (∑ χ ∈ s, ‖a χ - b χ‖ ^ 2) := sq _
  simp only [Pi.sub_apply]
  rw [abs_le]
  constructor <;> nlinarith [abs_le.mp h1, abs_le.mp h2, abs_le.mp h3]

private theorem layer_bound (m : ℕ) [NeZero m] (N : ℕ) (s : Finset (DirichletCharacter ℂ m))
    (a b : DirichletCharacter ℂ m → ℂ) (E A : ℝ) (hE : 0 ≤ E) (hA : 0 ≤ A)
    (hab : ∑ χ ∈ s, ‖a χ - b χ‖ ^ 2 ≤ E ^ 2) (ha : ∑ χ ∈ s, ‖a χ‖ ^ 2 ≤ A ^ 2) :
    |(∑ χ ∈ s, ∑ ψ ∈ s, star (a χ) *
      ((∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ ((N : ZMod m) - (x : ZMod m))) / (m.totient : ℂ)) * a ψ).re -
     (∑ χ ∈ s, ∑ ψ ∈ s, star (b χ) *
      ((∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ ((N : ZMod m) - (x : ZMod m))) / (m.totient : ℂ)) * b ψ).re|
      ≤ 2 * E * A + E ^ 2 := by
  have hH := (rc_ReflectionCharacterContraction m (N : ZMod m)).2 s
  have hq := qf_diff2 s (fun χ ψ : DirichletCharacter ℂ m =>
    (∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ ((N : ZMod m) - (x : ZMod m))) / (m.totient : ℂ)) hH a b
  refine hq.trans ?_
  have hD : Real.sqrt (∑ χ ∈ s, ‖a χ - b χ‖ ^ 2) ≤ E := by
    rw [Real.sqrt_le_iff]; exact ⟨hE, hab⟩
  have hD0 := Real.sqrt_nonneg (∑ χ ∈ s, ‖a χ - b χ‖ ^ 2)
  have hA' : Real.sqrt (∑ χ ∈ s, ‖a χ‖ ^ 2) ≤ A := by
    rw [Real.sqrt_le_iff]; exact ⟨hA, ha⟩
  have hA0 := Real.sqrt_nonneg (∑ χ ∈ s, ‖a χ‖ ^ 2)
  nlinarith [mul_le_mul hD hA' hA0 hE, pow_le_pow_left₀ hD0 hD 2]

private lemma geo_aux (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (K : ℕ) :
    ∑ k ∈ Finset.Ico 1 K, x ^ (K - 1 - k) ≤ 1 / (1 - x) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have h : ∀ i ∈ Finset.range (K - 1), x ^ (K - 1 - (1 + i)) = x ^ (K - 1 - 1 - i) := by
    intro i _
    congr 1
    omega
  rw [Finset.sum_congr rfl h, Finset.sum_range_reflect (fun i => x ^ i) (K - 1)]
  have := geom_sum_Ico_le_of_lt_one hx0 hx1 (m := 0) (n := K - 1)
  rw [Finset.sum_Ico_eq_sum_range] at this
  simpa using this

private lemma layer_t (k j N : ℕ) (hN : N < 2 ^ (k + 1 + j)) :
    ((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ (k + 1 + j) : ℕ) : ℝ) *
      Real.sqrt (1 + ((N / 2 ^ (k + 1) : ℕ) : ℝ)) ≤ Real.sqrt (2 * (1 / 2) ^ j) := by
  have hm : 0 < 2 ^ (k + 1) := by positivity
  have hdiv : N / 2 ^ (k + 1) < 2 ^ j := by
    rw [Nat.div_lt_iff_lt_mul hm]
    calc N < 2 ^ (k + 1 + j) := hN
      _ = 2 ^ j * 2 ^ (k + 1) := by ring
  have hdiv' : ((N / 2 ^ (k + 1) : ℕ) : ℝ) ≤ (2 : ℝ) ^ j := by exact_mod_cast hdiv.le
  have ht : ((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ (k + 1 + j) : ℕ) : ℝ) = (1 / 2) ^ j := by
    push_cast
    rw [pow_add (2 : ℝ) (k + 1) j, one_div, inv_pow]
    field_simp
  rw [ht]
  set t : ℝ := (1 / 2) ^ j with htdef
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have htj : t * (2 : ℝ) ^ j = 1 := by
    rw [htdef, one_div, inv_pow]; field_simp
  have hnn : 0 ≤ 1 + ((N / 2 ^ (k + 1) : ℕ) : ℝ) := by positivity
  have hc : t * Real.sqrt (1 + ((N / 2 ^ (k + 1) : ℕ) : ℝ)) =
      Real.sqrt (t ^ 2 * (1 + ((N / 2 ^ (k + 1) : ℕ) : ℝ))) := by
    rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht0.le]
  rw [hc]
  refine Real.sqrt_le_sqrt ?_
  have : t ^ 2 * (1 + ((N / 2 ^ (k + 1) : ℕ) : ℝ)) ≤ t ^ 2 * (1 + 2 ^ j) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left ht1 ht0.le]

private lemma sqrt_geo (j : ℕ) :
    Real.sqrt (2 * (1 / 2 : ℝ) ^ j) = Real.sqrt 2 * (Real.sqrt 2 / 2) ^ j := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hx : (1 / 2 : ℝ) ^ j = ((Real.sqrt 2 / 2) ^ j) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    congr 1
    nlinarith
  rw [hx, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]

theorem Conjectures.Goldbach.DyadicTruncationFormBudget :
    ∀ (N K : ℕ) (S : Finset ℕ) (w : ℕ → ℝ)
    (z : (k : ℕ) → DirichletCharacter ℂ (2^(k+1)) → ℂ) (E : ℝ),
  N < 2^K → 0 ≤ E → (∀ k ∈ S, 1 ≤ k ∧ k < K) →
  let s := fun k : ℕ => (Finset.univ : Finset (DirichletCharacter ℂ (2^(k+1)))).filter (fun χ => χ.conductor = 2^(k+1))
  let v := fun (k : ℕ) (χ : DirichletCharacter ℂ (2^(k+1))) =>
    (∑ n ∈ Finset.range (N+1), (w n : ℂ) * star (χ (n : ZMod (2^(k+1))))) /
      (Real.sqrt (((2^(k+1) : ℕ).totient) : ℝ) : ℂ)
  let R := fun (k : ℕ) (a : DirichletCharacter ℂ (2^(k+1)) → ℂ) =>
    (∑ χ ∈ s k, ∑ ψ ∈ s k, star (a χ) *
      ((∑ x : (ZMod (2^(k+1)))ˣ, star (χ (x : ZMod (2^(k+1)))) * ψ ((N : ZMod (2^(k+1))) - (x : ZMod (2^(k+1))))) /
        (((2^(k+1) : ℕ).totient) : ℂ)) * a ψ).re
  (∀ k ∈ S, (∑ χ ∈ s k, ‖v k χ-z k χ‖^2) ≤ E^2) →
    |∑ k ∈ S, ((2^(k+1) : ℕ) : ℝ) / ((2^K : ℕ) : ℝ) * (R k (v k) - R k (z k))| ≤
      10 * E * Real.sqrt (∑ n ∈ Finset.range (N+1), (w n)^2) + 2*E^2 := by
  intro N K S w z E hN hE hS s v R hE2
  have hW0 : 0 ≤ ∑ n ∈ Finset.range (N+1), (w n) ^ 2 := Finset.sum_nonneg (fun n _ => sq_nonneg _)
  set W := Real.sqrt (∑ n ∈ Finset.range (N+1), (w n) ^ 2) with hWdef
  have hWnn : 0 ≤ W := Real.sqrt_nonneg _
  have hWsq : W ^ 2 = ∑ n ∈ Finset.range (N+1), (w n) ^ 2 := Real.sq_sqrt hW0
  set x : ℝ := Real.sqrt 2 / 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hr : Real.sqrt 2 < 10 / 7 := by nlinarith
  have hx1 : x < 1 := by rw [hx]; linarith
  have key : ∀ k ∈ S, |((2^(k+1) : ℕ) : ℝ) / ((2^K : ℕ) : ℝ) * (R k (v k) - R k (z k))| ≤
      2 * E * W * (Real.sqrt 2 * x ^ (K - 1 - k)) + E ^ 2 * (1 / 2 : ℝ) ^ (K - 1 - k) := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := hS k hk
    obtain ⟨j, hj⟩ : ∃ j, K = k + 1 + j := ⟨K - 1 - k, by omega⟩
    have hjj : K - 1 - k = j := by omega
    rw [hjj]
    have hN' : N < 2 ^ (k + 1 + j) := hj ▸ hN
    have ht : ((2^(k+1) : ℕ) : ℝ) / ((2^K : ℕ) : ℝ) = (1 / 2 : ℝ) ^ j := by
      rw [hj]
      push_cast
      rw [pow_add (2 : ℝ) (k + 1) j, one_div, inv_pow]
      field_simp
    have ht0 : 0 ≤ (1 / 2 : ℝ) ^ j := by positivity
    set Cm : ℝ := 1 + ((N / 2 ^ (k + 1) : ℕ) : ℝ) with hCm
    have hCm0 : 0 ≤ Cm := by positivity
    have hen := pm_energy (2 ^ (k + 1)) N (s k) w
    have hA : 0 ≤ Real.sqrt Cm * W := by positivity
    have ha : ∑ χ ∈ s k, ‖v k χ‖ ^ 2 ≤ (Real.sqrt Cm * W) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hCm0, hWsq]
      exact hen
    have hl := layer_bound (2 ^ (k + 1)) N (s k) (v k) (z k) E (Real.sqrt Cm * W) hE hA (hE2 k hk) ha
    have hl' : |R k (v k) - R k (z k)| ≤ 2 * E * (Real.sqrt Cm * W) + E ^ 2 := hl
    have hkt := layer_t k j N hN'
    rw [← hj, ht] at hkt
    rw [ht]
    rw [abs_mul, abs_of_nonneg ht0]
    have e1 : (1 / 2 : ℝ) ^ j * |R k (v k) - R k (z k)| ≤
        (1 / 2 : ℝ) ^ j * (2 * E * (Real.sqrt Cm * W) + E ^ 2) :=
      mul_le_mul_of_nonneg_left hl' ht0
    have e2 : (1 / 2 : ℝ) ^ j * Real.sqrt Cm ≤ Real.sqrt 2 * x ^ j := by
      rw [← sqrt_geo j]; exact hkt
    have e3 : 2 * E * W * ((1 / 2 : ℝ) ^ j * Real.sqrt Cm) ≤ 2 * E * W * (Real.sqrt 2 * x ^ j) :=
      mul_le_mul_of_nonneg_left e2 (by positivity)
    nlinarith
  have hterm0 : ∀ k : ℕ, 0 ≤ 2 * E * W * (Real.sqrt 2 * x ^ (K - 1 - k)) + E ^ 2 * (1 / 2 : ℝ) ^ (K - 1 - k) :=
    fun k => by positivity
  have hS' : S ⊆ Finset.Ico 1 K := fun k hk => Finset.mem_Ico.mpr (hS k hk)
  calc |∑ k ∈ S, ((2^(k+1) : ℕ) : ℝ) / ((2^K : ℕ) : ℝ) * (R k (v k) - R k (z k))|
      ≤ ∑ k ∈ S, |((2^(k+1) : ℕ) : ℝ) / ((2^K : ℕ) : ℝ) * (R k (v k) - R k (z k))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ S, (2 * E * W * (Real.sqrt 2 * x ^ (K - 1 - k)) + E ^ 2 * (1 / 2 : ℝ) ^ (K - 1 - k)) :=
        Finset.sum_le_sum key
    _ ≤ ∑ k ∈ Finset.Ico 1 K, (2 * E * W * (Real.sqrt 2 * x ^ (K - 1 - k)) +
          E ^ 2 * (1 / 2 : ℝ) ^ (K - 1 - k)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hS' (fun k _ _ => hterm0 k)
    _ = 2 * E * W * Real.sqrt 2 * ∑ k ∈ Finset.Ico 1 K, x ^ (K - 1 - k) +
          E ^ 2 * ∑ k ∈ Finset.Ico 1 K, (1 / 2 : ℝ) ^ (K - 1 - k) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl (fun k _ => by ring)
    _ ≤ 2 * E * W * Real.sqrt 2 * (1 / (1 - x)) + E ^ 2 * (1 / (1 - 1 / 2)) := by
        have g1 := geo_aux x hx0 hx1 K
        have g2 := geo_aux (1 / 2) (by norm_num) (by norm_num) K
        have c1 : 0 ≤ 2 * E * W * Real.sqrt 2 := by positivity
        exact add_le_add (mul_le_mul_of_nonneg_left g1 c1)
          (mul_le_mul_of_nonneg_left g2 (sq_nonneg E))
    _ ≤ 10 * E * W + 2 * E ^ 2 := by
        have hd : 0 < 1 - x := by linarith
        have hb : Real.sqrt 2 * (1 / (1 - x)) ≤ 5 := by
          rw [mul_one_div, div_le_iff₀ hd, hx]
          nlinarith
        have c1 : 0 ≤ 2 * E * W := by positivity
        have e : 2 * E * W * Real.sqrt 2 * (1 / (1 - x)) ≤ 2 * E * W * 5 := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hb c1
        have e' : (1 / (1 - 1 / 2 : ℝ)) = 2 := by norm_num
        rw [e']
        nlinarith

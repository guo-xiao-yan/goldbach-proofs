import Mathlib

private lemma rcb_mult_sum (q A : ℕ) (hq : 1 ≤ q) :
    (∑ u ∈ Finset.Icc 1 A, if q ∣ u then ((u:ℝ)⁻¹) else 0)
      ≤ (q:ℝ)⁻¹ * ∑ u ∈ Finset.Icc 1 A, (u:ℝ)⁻¹ := by
  rw [← Finset.sum_filter]
  have hinj : Set.InjOn (fun u : ℕ => u / q) ((Finset.Icc 1 A).filter (fun u => q ∣ u) : Finset ℕ) := by
    intro x hx y hy hxy
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_setOf_eq] at hx hy
    obtain ⟨_, ⟨c, rfl⟩⟩ := hx
    obtain ⟨_, ⟨d, rfl⟩⟩ := hy
    simp only at hxy
    rw [Nat.mul_div_cancel_left _ (by omega), Nat.mul_div_cancel_left _ (by omega)] at hxy
    rw [hxy]
  have h1 : ∑ u ∈ (Finset.Icc 1 A).filter (fun u => q ∣ u), (u:ℝ)⁻¹
      = ∑ u ∈ (Finset.Icc 1 A).filter (fun u => q ∣ u), (q:ℝ)⁻¹ * (((u / q : ℕ) : ℝ))⁻¹ := by
    apply Finset.sum_congr rfl
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_Icc] at hu
    obtain ⟨_, ⟨c, rfl⟩⟩ := hu
    rw [Nat.mul_div_cancel_left _ (by omega)]
    have : (q:ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
    push_cast
    rw [mul_inv]
  rw [h1, ← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← Finset.sum_image (f := fun k : ℕ => ((k:ℝ))⁻¹) hinj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc] at hk ⊢
    obtain ⟨u, ⟨⟨h1, h2⟩, ⟨c, rfl⟩⟩, rfl⟩ := hk
    rw [Nat.mul_div_cancel_left _ (by omega)]
    have : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h; omega
      · exact h
    have : c ≤ q * c := Nat.le_mul_of_pos_left c (by omega)
    omega
  · intros; positivity

private theorem rcb_main :
    ∀ (A D : ℕ) (T : ℕ→ℝ), (∀ q,0≤T q) → (∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D, ((∑ q ∈ (u.gcd v).divisors,T q)*(u:ℝ)⁻¹*(v:ℝ)⁻¹)) ≤ (∑ q ∈ Finset.Icc 1 (min A D),T q*(q:ℝ)⁻¹^2)* (∑ u ∈ Finset.Icc 1 A,(u:ℝ)⁻¹)*(∑ v ∈ Finset.Icc 1 D,(v:ℝ)⁻¹) := by
  intro A D T hT
  have step1 : ∀ u ∈ Finset.Icc 1 A, ∀ v ∈ Finset.Icc 1 D,
      (∑ q ∈ (u.gcd v).divisors, T q)
        = ∑ q ∈ Finset.Icc 1 (min A D), if q ∣ u ∧ q ∣ v then T q else 0 := by
    intro u hu v hv
    simp only [Finset.mem_Icc] at hu hv
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext q
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc, Nat.dvd_gcd_iff]
    have hg : 0 < u.gcd v := Nat.gcd_pos_of_pos_left _ (by omega)
    have h2 : u.gcd v ≤ u := Nat.gcd_le_left _ (by omega)
    have h3 : u.gcd v ≤ v := Nat.gcd_le_right _ (by omega)
    constructor
    · rintro ⟨hd, hne⟩
      have h1 : q ≤ u.gcd v := Nat.le_of_dvd hg (Nat.dvd_gcd_iff.mpr hd)
      have hq : 0 < q := Nat.pos_of_dvd_of_pos hd.1 (by omega)
      exact ⟨⟨by omega, by omega⟩, hd⟩
    · rintro ⟨_, h⟩
      exact ⟨h, by omega⟩
  have e1 : (∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D, ((∑ q ∈ (u.gcd v).divisors,T q)*(u:ℝ)⁻¹*(v:ℝ)⁻¹))
      = ∑ q ∈ Finset.Icc 1 (min A D), T q *
          ((∑ u ∈ Finset.Icc 1 A, if q ∣ u then ((u:ℝ)⁻¹) else 0) *
           (∑ v ∈ Finset.Icc 1 D, if q ∣ v then ((v:ℝ)⁻¹) else 0)) := by
    have : ∀ u ∈ Finset.Icc 1 A, (∑ v ∈ Finset.Icc 1 D, ((∑ q ∈ (u.gcd v).divisors,T q)*(u:ℝ)⁻¹*(v:ℝ)⁻¹))
        = ∑ v ∈ Finset.Icc 1 D, ∑ q ∈ Finset.Icc 1 (min A D),
            T q * ((if q ∣ u then ((u:ℝ)⁻¹) else 0) * (if q ∣ v then ((v:ℝ)⁻¹) else 0)) := by
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      rw [step1 u hu v hv, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q _
      by_cases h1 : q ∣ u <;> by_cases h2 : q ∣ v <;> simp [h1, h2] <;> ring
    rw [Finset.sum_congr rfl this]
    have hc : ∀ u ∈ Finset.Icc 1 A, (∑ v ∈ Finset.Icc 1 D, ∑ q ∈ Finset.Icc 1 (min A D),
            T q * ((if q ∣ u then ((u:ℝ)⁻¹) else 0) * (if q ∣ v then ((v:ℝ)⁻¹) else 0)))
        = ∑ q ∈ Finset.Icc 1 (min A D), ∑ v ∈ Finset.Icc 1 D,
            T q * ((if q ∣ u then ((u:ℝ)⁻¹) else 0) * (if q ∣ v then ((v:ℝ)⁻¹) else 0)) :=
      fun _ _ => Finset.sum_comm
    rw [Finset.sum_congr rfl hc, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.mul_sum]
  rw [e1, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro q hq
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
  have hqA := rcb_mult_sum q A hq1
  have hqD := rcb_mult_sum q D hq1
  have hS1 : 0 ≤ ∑ u ∈ Finset.Icc 1 A, if q ∣ u then ((u:ℝ)⁻¹) else 0 :=
    Finset.sum_nonneg (fun u _ => by split_ifs <;> positivity)
  have hS2 : 0 ≤ ∑ u ∈ Finset.Icc 1 D, if q ∣ u then ((u:ℝ)⁻¹) else 0 :=
    Finset.sum_nonneg (fun u _ => by split_ifs <;> positivity)
  have hprod := mul_le_mul hqA hqD hS2 (by positivity)
  have : T q * ((∑ u ∈ Finset.Icc 1 A, if q ∣ u then ((u:ℝ)⁻¹) else 0) *
           (∑ v ∈ Finset.Icc 1 D, if q ∣ v then ((v:ℝ)⁻¹) else 0))
      ≤ T q * ((q:ℝ)⁻¹ * (∑ u ∈ Finset.Icc 1 A, (u:ℝ)⁻¹) * ((q:ℝ)⁻¹ * ∑ u ∈ Finset.Icc 1 D, (u:ℝ)⁻¹)) :=
    mul_le_mul_of_nonneg_left hprod (hT q)
  calc _ ≤ _ := this
    _ = _ := by ring

private lemma rcb_gcd_bound (n B H m : ℕ) (hn : 0 < n) (hB : 0 < B) (hBH : B ≤ H) :
    (∑ q ∈ Finset.Icc 1 m, ((n:ℝ) * (if q ≤ B then ((q.gcd n:ℝ)*q/H) else (q.gcd n:ℝ))) * ((q:ℝ)⁻¹)^2)
      ≤ ((n:ℝ)/B) * n.divisors.card * ∑ q ∈ Finset.Icc 1 m, (q:ℝ)⁻¹ := by
  have hBr : (0:ℝ) < B := by exact_mod_cast hB
  have hHr : (B:ℝ) ≤ H := by exact_mod_cast hBH
  have hterm : ∀ q ∈ Finset.Icc 1 m,
      ((n:ℝ) * (if q ≤ B then ((q.gcd n:ℝ)*q/H) else (q.gcd n:ℝ))) * ((q:ℝ)⁻¹)^2
        ≤ ((n:ℝ)/B) * ∑ e ∈ n.divisors, (if e ∣ q then (e:ℝ) * (q:ℝ)⁻¹ else 0) := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hqr : (0:ℝ) < q := by exact_mod_cast hq1
    have hg : (q.gcd n) ∈ n.divisors := by
      exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hn.ne'⟩
    have hsum : (q.gcd n : ℝ) * (q:ℝ)⁻¹ ≤ ∑ e ∈ n.divisors, (if e ∣ q then (e:ℝ) * (q:ℝ)⁻¹ else 0) := by
      have := Finset.single_le_sum (f := fun e : ℕ => (if e ∣ q then (e:ℝ) * (q:ℝ)⁻¹ else 0))
        (s := n.divisors) (fun e _ => by split_ifs <;> positivity) hg
      simpa [Nat.gcd_dvd_left] using this
    have hkey : ((n:ℝ) * (if q ≤ B then ((q.gcd n:ℝ)*q/H) else (q.gcd n:ℝ))) * ((q:ℝ)⁻¹)^2
        ≤ ((n:ℝ)/B) * ((q.gcd n : ℝ) * (q:ℝ)⁻¹) := by
      have hgn : (0:ℝ) ≤ (q.gcd n : ℝ) := by positivity
      have hnn : (0:ℝ) ≤ n := by positivity
      split_ifs with h
      · have hHp : (0:ℝ) < H := lt_of_lt_of_le hBr hHr
        calc (n:ℝ) * ((q.gcd n:ℝ) * q / H) * ((q:ℝ)⁻¹)^2 = ((q.gcd n:ℝ) * (q:ℝ)⁻¹ / H) * n := by
              field_simp
          _ ≤ ((q.gcd n:ℝ) * (q:ℝ)⁻¹ / B) * n := by
              apply mul_le_mul_of_nonneg_right _ hnn
              apply div_le_div_of_nonneg_left (by positivity) hBr hHr
          _ = _ := by field_simp
      · have hlt : (B:ℝ) < q := by exact_mod_cast (not_le.mp h)
        have h1 : (q:ℝ)⁻¹ ≤ (B:ℝ)⁻¹ := inv_anti₀ hBr hlt.le
        have : (n:ℝ) * (q.gcd n:ℝ) * ((q:ℝ)⁻¹)^2 ≤ (n:ℝ) * (q.gcd n:ℝ) * ((q:ℝ)⁻¹ * (B:ℝ)⁻¹) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [sq]
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
        calc _ ≤ _ := this
          _ = _ := by field_simp
    calc _ ≤ _ := hkey
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
  calc _ ≤ ∑ q ∈ Finset.Icc 1 m, ((n:ℝ)/B) * ∑ e ∈ n.divisors, (if e ∣ q then (e:ℝ) * (q:ℝ)⁻¹ else 0) :=
        Finset.sum_le_sum hterm
    _ = ((n:ℝ)/B) * ∑ e ∈ n.divisors, ∑ q ∈ Finset.Icc 1 m, (if e ∣ q then (e:ℝ) * (q:ℝ)⁻¹ else 0) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ ((n:ℝ)/B) * ∑ e ∈ n.divisors, ∑ q ∈ Finset.Icc 1 m, (q:ℝ)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro e he
        have he1 : 1 ≤ e := Nat.pos_of_mem_divisors he
        have her : (0:ℝ) < e := by exact_mod_cast he1
        have := rcb_mult_sum e m he1
        have h2 : (∑ q ∈ Finset.Icc 1 m, (if e ∣ q then (e:ℝ) * (q:ℝ)⁻¹ else 0))
            = (e:ℝ) * ∑ q ∈ Finset.Icc 1 m, (if e ∣ q then (q:ℝ)⁻¹ else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q _
          split_ifs <;> simp
        rw [h2]
        calc (e:ℝ) * _ ≤ (e:ℝ) * ((e:ℝ)⁻¹ * ∑ q ∈ Finset.Icc 1 m, (q:ℝ)⁻¹) :=
              mul_le_mul_of_nonneg_left this her.le
          _ = _ := by field_simp
    _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

theorem Conjectures.Goldbach.RectangularCornerBudget :
    ∀ (n A D B H : ℕ), 0<n → 0<B → B≤H → let L := fun N : ℕ => ∑ q ∈ Finset.Icc 1 N,(q:ℝ)⁻¹; let C := fun u v : ℕ => (1+Real.log ((n:ℝ)+2))^2 + ((max A D:ℕ):ℝ)*(u.gcd v:ℝ)^2/((u:ℝ)*v) + (n:ℝ)/((u:ℝ)*v) * ((∑ q ∈ (u.gcd v).divisors.filter (·≤B),(q.gcd n:ℝ)*q/H) + ∑ q ∈ (u.gcd v).divisors.filter (B<·),(q.gcd n:ℝ)); (∑ u ∈ Finset.Icc 1 A,∑ v ∈ Finset.Icc 1 D,C u v) ≤ (A:ℝ)*D*(1+Real.log ((n:ℝ)+2))^2 + (A:ℝ)*D*L A*L D + ((n:ℝ)/B)*n.divisors.card*L (min A D)*L A*L D := by
  intro n A D B H hn hB hBH L C
  have hm : ((max A D : ℕ):ℝ) * ((min A D : ℕ):ℝ) = (A:ℝ) * D := by
    rcases le_total A D with h | h
    · simp [max_eq_right h, min_eq_left h, mul_comm]
    · simp [max_eq_left h, min_eq_right h]
  have h2 := rcb_main A D (fun q => (q:ℝ)^2) (fun q => by positivity)
  have h3 := rcb_main A D (fun q => (n:ℝ) * (if q ≤ B then ((q.gcd n:ℝ)*q/H) else (q.gcd n:ℝ)))
    (fun q => by
      have : (0:ℝ) ≤ (q.gcd n:ℝ) := by positivity
      split_ifs <;> positivity)
  have e1 : ∀ u v : ℕ, C u v = (1+Real.log ((n:ℝ)+2))^2
      + ((max A D:ℕ):ℝ) * ((u.gcd v:ℝ)^2/((u:ℝ)*v))
      + ((∑ q ∈ (u.gcd v).divisors, (n:ℝ) * (if q ≤ B then ((q.gcd n:ℝ)*q/H) else (q.gcd n:ℝ))) * (u:ℝ)⁻¹ * (v:ℝ)⁻¹) := by
    intro u v
    simp only [C]
    rw [← Finset.mul_sum, Finset.sum_ite]
    simp only [not_le]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hsum2 : (∑ q ∈ Finset.Icc 1 (min A D), (q:ℝ)^2 * ((q:ℝ)⁻¹)^2) = ((min A D : ℕ):ℝ) := by
    rw [Finset.sum_congr rfl (g := fun _ => (1:ℝ))]
    · simp
    · intro q hq
      have : (q:ℝ) ≠ 0 := by
        have := (Finset.mem_Icc.mp hq).1
        exact_mod_cast (by omega : q ≠ 0)
      field_simp
  have hX : (∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D, ((u.gcd v:ℝ)^2/((u:ℝ)*v)))
      ≤ ((min A D : ℕ):ℝ) * L A * L D := by
    calc _ ≤ ∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D, (∑ q ∈ (u.gcd v).divisors, (q:ℝ)^2) * (u:ℝ)⁻¹ * (v:ℝ)⁻¹ := by
          apply Finset.sum_le_sum; intro u hu
          apply Finset.sum_le_sum; intro v hv
          have hu1 := (Finset.mem_Icc.mp hu).1
          have hv1 := (Finset.mem_Icc.mp hv).1
          have hgd : u.gcd v ∈ (u.gcd v).divisors :=
            Nat.mem_divisors.mpr ⟨dvd_rfl, (Nat.gcd_pos_of_pos_left _ (by omega)).ne'⟩
          have := Finset.single_le_sum (f := fun q : ℕ => (q:ℝ)^2) (s := (u.gcd v).divisors)
            (fun q _ => by positivity) hgd
          rw [div_eq_mul_inv, mul_inv]
          have h0 : (0:ℝ) ≤ (u:ℝ)⁻¹ * (v:ℝ)⁻¹ := by positivity
          calc (u.gcd v:ℝ)^2 * ((u:ℝ)⁻¹ * (v:ℝ)⁻¹) ≤ (∑ q ∈ (u.gcd v).divisors, (q:ℝ)^2) * ((u:ℝ)⁻¹ * (v:ℝ)⁻¹) :=
                mul_le_mul_of_nonneg_right this h0
            _ = _ := by ring
      _ ≤ _ := h2
      _ = _ := by rw [hsum2]
  have hR := le_trans h3 (by
    have := rcb_gcd_bound n B H (min A D) hn hB hBH
    have hLA : (0:ℝ) ≤ ∑ u ∈ Finset.Icc 1 A, (u:ℝ)⁻¹ := Finset.sum_nonneg (fun _ _ => by positivity)
    have hLD : (0:ℝ) ≤ ∑ u ∈ Finset.Icc 1 D, (u:ℝ)⁻¹ := Finset.sum_nonneg (fun _ _ => by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hLA) hLD)
  have hsplit : (∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D, C u v)
      = (A:ℝ) * D * (1+Real.log ((n:ℝ)+2))^2
        + ((max A D:ℕ):ℝ) * (∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D, ((u.gcd v:ℝ)^2/((u:ℝ)*v)))
        + ∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D,
            ((∑ q ∈ (u.gcd v).divisors, (n:ℝ) * (if q ≤ B then ((q.gcd n:ℝ)*q/H) else (q.gcd n:ℝ))) * (u:ℝ)⁻¹ * (v:ℝ)⁻¹) := by
    simp only [e1, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, ← Finset.mul_sum]
    push_cast
    ring
  rw [hsplit]
  have hmax : (0:ℝ) ≤ ((max A D:ℕ):ℝ) := by positivity
  have h4 := mul_le_mul_of_nonneg_left hX hmax
  have h5 : ((max A D:ℕ):ℝ) * (((min A D : ℕ):ℝ) * L A * L D) = (A:ℝ) * D * L A * L D := by
    rw [← hm]; ring
  simp only [L] at h5 ⊢
  linarith

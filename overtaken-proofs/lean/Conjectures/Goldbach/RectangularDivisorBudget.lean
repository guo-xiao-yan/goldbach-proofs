import Mathlib

private lemma rdb_mult_sum (q A : ℕ) (hq : 1 ≤ q) :
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

theorem Conjectures.Goldbach.RectangularDivisorBudget :
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
  have hqA := rdb_mult_sum q A hq1
  have hqD := rdb_mult_sum q D hq1
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

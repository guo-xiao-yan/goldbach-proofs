import Mathlib

private lemma chen_D_iff (n p : ℕ) :
    ((Finset.Icc 2 n).filter (fun r => r.Prime ∧
      ((Finset.Ioc r n).filter (fun v => v.Prime ∧ p + r * v = n)).Nonempty)).Nonempty ↔
    ∃ r v, r.Prime ∧ v.Prime ∧ r < v ∧ p + r * v = n := by
  constructor
  · rintro ⟨r, hr⟩
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hr
    obtain ⟨_, hrp, v, hv⟩ := hr
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hv
    exact ⟨r, v, hrp, hv.2.1, hv.1.1, hv.2.2⟩
  · rintro ⟨r, v, hr, hv, hrv, h⟩
    have h1 : r ≤ r * v := Nat.le_mul_of_pos_right r hv.pos
    have h2 : v ≤ r * v := Nat.le_mul_of_pos_left v hr.pos
    refine ⟨r, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨hr.two_le, by omega⟩, hr, v, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hrv, by omega⟩, hv, h⟩

private lemma chen_len2 (m : ℕ) (hm : 0 < m) :
    m.primeFactorsList.length = 2 ↔ ∃ a b, a.Prime ∧ b.Prime ∧ a ≤ b ∧ a * b = m := by
  constructor
  · intro h
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp h
    have ha : a.Prime := Nat.prime_of_mem_primeFactorsList (by rw [hab]; simp)
    have hb : b.Prime := Nat.prime_of_mem_primeFactorsList (by rw [hab]; simp)
    have hp := Nat.prod_primeFactorsList hm.ne'
    rw [hab] at hp
    simp only [List.prod_cons, List.prod_nil, mul_one] at hp
    rcases le_total a b with h | h
    · exact ⟨a, b, ha, hb, h, hp⟩
    · exact ⟨b, a, hb, ha, h, by rw [mul_comm]; exact hp⟩
  · rintro ⟨a, b, ha, hb, _, rfl⟩
    have := Nat.perm_primeFactorsList_mul ha.ne_zero hb.ne_zero
    rw [this.length_eq, List.length_append, Nat.primeFactorsList_prime ha,
      Nat.primeFactorsList_prime hb]
    rfl

theorem Conjectures.Goldbach.FiniteChenUnweightedCountPartition :
    ∀ n : ℕ, let P := (Finset.range (n+1)).filter Nat.Prime; let C := P.filter (fun p => 0<n-p ∧ (n-p).primeFactorsList.length≤2); let G := P.filter (fun p => (n-p).Prime); let S := P.filter (fun p => (Nat.sqrt (n-p)).Prime ∧ (Nat.sqrt (n-p))^2=n-p); let D := P.filter (fun p => ((Finset.Icc 2 n).filter (fun r => r.Prime ∧ ((Finset.Ioc r n).filter (fun v => v.Prime ∧ p+r*v=n)).Nonempty)).Nonempty); C.card = G.card + S.card + D.card + (if (n-1).Prime then 1 else 0) := by
  intro n P C G S D
  have hS : ∀ p, ((Nat.sqrt (n-p)).Prime ∧ (Nat.sqrt (n-p))^2=n-p) ↔
      ∃ r, r.Prime ∧ r * r = n - p := by
    intro p
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨_, h1, by rw [← pow_two]; exact h2⟩
    · rintro ⟨r, hr, h⟩
      have : Nat.sqrt (n - p) = r := by rw [← h]; exact Nat.sqrt_eq r
      rw [this]
      exact ⟨hr, by rw [← h]; ring⟩
  let C1 := P.filter (fun p => n - p = 1)
  have hmemP : ∀ p, p ∈ P ↔ p ≤ n ∧ p.Prime := by
    intro p
    simp only [P, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h, h2⟩; exact ⟨by omega, h2⟩
    · rintro ⟨h, h2⟩; exact ⟨by omega, h2⟩
  have hDm : ∀ p, p ∈ D ↔ p ∈ P ∧ ∃ r v, r.Prime ∧ v.Prime ∧ r < v ∧ p + r * v = n := by
    intro p
    simp only [D, Finset.mem_filter]
    rw [chen_D_iff]
  have hSm : ∀ p, p ∈ S ↔ p ∈ P ∧ ∃ r, r.Prime ∧ r * r = n - p := by
    intro p
    simp only [S, Finset.mem_filter]
    rw [hS]
  have hGm : ∀ p, p ∈ G ↔ p ∈ P ∧ (n - p).Prime := by
    intro p
    simp only [G, Finset.mem_filter]
  have hC1m : ∀ p, p ∈ C1 ↔ p ∈ P ∧ n - p = 1 := by
    intro p
    simp only [C1, Finset.mem_filter]
  have hCm : ∀ p, p ∈ C ↔ p ∈ P ∧ 0 < n - p ∧ (n - p).primeFactorsList.length ≤ 2 := by
    intro p
    simp only [C, Finset.mem_filter]
  have hC : C = ((G ∪ S) ∪ D) ∪ C1 := by
    ext p
    simp only [hCm, hGm, hSm, hDm, hC1m, Finset.mem_union]
    constructor
    · rintro ⟨hp, hpos, hle⟩
      have hlen : (n-p).primeFactorsList.length = 0 ∨ (n-p).primeFactorsList.length = 1 ∨
          (n-p).primeFactorsList.length = 2 := by omega
      rcases hlen with h | h | h
      · right
        refine ⟨hp, ?_⟩
        rw [List.length_eq_zero_iff, Nat.primeFactorsList_eq_nil] at h
        omega
      · left; left; left
        refine ⟨hp, ?_⟩
        rw [List.length_eq_one_iff] at h
        obtain ⟨a, ha⟩ := h
        have hap : a.Prime := Nat.prime_of_mem_primeFactorsList (by rw [ha]; simp)
        have hpr := Nat.prod_primeFactorsList (show n - p ≠ 0 by omega)
        rw [ha] at hpr
        simp only [List.prod_cons, List.prod_nil, mul_one] at hpr
        rw [← hpr]; exact hap
      · obtain ⟨a, b, ha, hb, hab, hm⟩ := (chen_len2 _ hpos).mp h
        rcases hab.lt_or_eq with h | h
        · left; right
          exact ⟨hp, a, b, ha, hb, h, by omega⟩
        · left; left; right
          subst h
          exact ⟨hp, a, ha, by omega⟩
    · rintro (((⟨hp, h⟩ | ⟨hp, r, hr, h⟩) | ⟨hp, r, v, hr, hv, hrv, h⟩) | ⟨hp, h⟩)
      · refine ⟨hp, by have := h.pos; omega, ?_⟩
        rw [Nat.primeFactorsList_prime h]; simp
      · refine ⟨hp, by have := Nat.mul_pos hr.pos hr.pos; omega, ?_⟩
        rw [← h]
        have := Nat.perm_primeFactorsList_mul hr.ne_zero hr.ne_zero
        rw [this.length_eq, List.length_append, Nat.primeFactorsList_prime hr]
        simp
      · have := Nat.mul_pos hr.pos hv.pos
        refine ⟨hp, by omega, ?_⟩
        have h3 : n - p = r * v := by omega
        rw [h3]
        exact ((chen_len2 _ this).mpr ⟨r, v, hr, hv, hrv.le, rfl⟩).le
      · refine ⟨hp, by omega, ?_⟩
        rw [h]; simp
  have hC1 : C1.card = if (n-1).Prime then 1 else 0 := by
    split_ifs with h
    · rw [Finset.card_eq_one]
      refine ⟨n-1, ?_⟩
      ext p
      simp only [hC1m, hmemP, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; omega
      · rintro rfl
        have := h.pos
        exact ⟨⟨by omega, h⟩, by omega⟩
    · rw [Finset.card_eq_zero]
      ext p
      simp only [hC1m, hmemP, Finset.notMem_empty, iff_false]
      rintro ⟨⟨h1, h2⟩, h3⟩
      have : p = n - 1 := by omega
      exact h (this ▸ h2)
  have dGS : Disjoint G S := by
    rw [Finset.disjoint_left]
    intro p hG hS'
    rw [hGm] at hG
    rw [hSm] at hS'
    obtain ⟨_, r, hr, h⟩ := hS'
    have hpr := hG.2
    rw [← h] at hpr
    exact Nat.not_prime_mul hr.one_lt.ne' hr.one_lt.ne' hpr
  have dGD : Disjoint (G ∪ S) D := by
    rw [Finset.disjoint_left]
    intro p hG hD'
    rw [hDm] at hD'
    obtain ⟨_, r, v, hr, hv, hrv, h⟩ := hD'
    have h3 : n - p = r * v := by omega
    rcases Finset.mem_union.mp hG with hG | hS'
    · rw [hGm] at hG
      have hpr := hG.2
      rw [h3] at hpr
      exact Nat.not_prime_mul hr.one_lt.ne' hv.one_lt.ne' hpr
    · rw [hSm] at hS'
      obtain ⟨_, r', hr', h'⟩ := hS'
      rw [h3] at h'
      have h4 : r ∣ r' * r' := ⟨v, h'⟩
      have h5 : r = r' := (Nat.prime_dvd_prime_iff_eq hr hr').mp (hr.dvd_mul.mp h4 |>.elim id id)
      subst h5
      have : r = v := Nat.eq_of_mul_eq_mul_left hr.pos h'
      omega
  have dD : Disjoint ((G ∪ S) ∪ D) C1 := by
    rw [Finset.disjoint_left]
    intro p hl hC1'
    rw [hC1m] at hC1'
    have h1 := hC1'.2
    rcases Finset.mem_union.mp hl with hl | hD'
    · rcases Finset.mem_union.mp hl with hG | hS'
      · rw [hGm] at hG
        have := hG.2.one_lt; omega
      · rw [hSm] at hS'
        obtain ⟨_, r, hr, h⟩ := hS'
        have := Nat.mul_pos hr.pos hr.pos
        have := hr.two_le
        have : 4 ≤ r * r := by nlinarith
        omega
    · rw [hDm] at hD'
      obtain ⟨_, r, v, hr, hv, hrv, h⟩ := hD'
      have := hr.two_le
      have := hv.two_le
      have : 4 ≤ r * v := by nlinarith
      omega
  rw [hC, Finset.card_union_of_disjoint dD, Finset.card_union_of_disjoint dGD,
    Finset.card_union_of_disjoint dGS, hC1]

import Mathlib

private lemma chen_cube_uniq {r v r' v' : ℕ} (hr : r.Prime) (hr' : r'.Prime) (hv : v.Prime)
    (hv' : v'.Prime) (h1 : r < v) (h2 : r' < v') (h : r * v = r' * v') : r = r' := by
  have hd : r ∣ r' * v' := ⟨v, h.symm⟩
  rcases (Nat.Prime.dvd_mul hr).mp hd with h3 | h3
  · exact (Nat.prime_dvd_prime_iff_eq hr hr').mp h3
  · have h4 : r = v' := (Nat.prime_dvd_prime_iff_eq hr hv').mp h3
    subst h4
    have h5 : v = r' := by
      have : r * v = r * r' := by rw [h]; ring
      exact Nat.eq_of_mul_eq_mul_left hr.pos this
    omega

theorem Conjectures.Goldbach.FiniteChenDistinctFactorCubeSplit :
    ∀ n : ℕ, let R := (Finset.Icc 2 n).filter Nat.Prime; let D := (Finset.range (n+1)).filter (fun p => p.Prime ∧ (R.filter (fun r => ((Finset.Ioc r (n/r)).filter (fun v => v.Prime ∧ p+r*v=n)).Nonempty)).Nonempty); let B := D.filter (fun p => (R.filter (fun r => r ∣ n ∧ ((Finset.Ioc r (n/r)).filter (fun v => v.Prime ∧ p+r*v=n)).Nonempty)).Nonempty); let L := R.filter (fun r => ¬ r∣n ∧ r^3≤n); let H := R.filter (fun r => ¬ r∣n ∧ n<r^3); let F := fun r : ℕ => ((Finset.Ioc r (n/r)).filter (fun v => v.Prime ∧ (n-r*v).Prime)).card; D.card = B.card + (∑ r ∈ L, F r) + (∑ r ∈ H, F r) ∧ B.card≤n.primeFactors.card := by
  intro n R D B L H F
  have hRm : ∀ r, r ∈ R ↔ (2 ≤ r ∧ r ≤ n) ∧ r.Prime := by
    intro r
    simp only [R, Finset.mem_filter, Finset.mem_Icc]
  have hDm : ∀ p, p ∈ D ↔ p < n + 1 ∧ p.Prime ∧ ∃ r, r ∈ R ∧ ∃ v, (r < v ∧ v ≤ n / r) ∧
      v.Prime ∧ p + r * v = n := by
    intro p
    simp only [D, Finset.mem_filter, Finset.mem_range, Finset.filter_nonempty_iff, Finset.mem_Ioc]
  have hBm : ∀ p, p ∈ B ↔ p ∈ D ∧ ∃ r, r ∈ R ∧ r ∣ n ∧ ∃ v, (r < v ∧ v ≤ n / r) ∧
      v.Prime ∧ p + r * v = n := by
    intro p
    simp only [B, Finset.mem_filter, Finset.filter_nonempty_iff, Finset.mem_Ioc]
  have hLm : ∀ r, r ∈ L ↔ r ∈ R ∧ ¬ r ∣ n ∧ r ^ 3 ≤ n := by
    intro r
    simp only [L, Finset.mem_filter]
  have hHm : ∀ r, r ∈ H ↔ r ∈ R ∧ ¬ r ∣ n ∧ n < r ^ 3 := by
    intro r
    simp only [H, Finset.mem_filter]
  have hFm : ∀ r v, v ∈ (Finset.Ioc r (n/r)).filter (fun v => v.Prime ∧ (n-r*v).Prime) ↔
      (r < v ∧ v ≤ n / r) ∧ v.Prime ∧ (n - r * v).Prime := by
    intro r v
    simp only [Finset.mem_filter, Finset.mem_Ioc]
  have hBsub : B ⊆ n.primeFactors := by
    intro p hp
    obtain ⟨hpD, r, hr, hrn, v, hv, hvp, h⟩ := (hBm p).mp hp
    obtain ⟨_, hpp, _⟩ := (hDm p).mp hpD
    have hr' := (hRm r).mp hr
    have hrp : r ∣ p := (Nat.dvd_add_left (dvd_mul_right r v)).mp (h ▸ hrn)
    have : r = p := (Nat.prime_dvd_prime_iff_eq hr'.2 hpp).mp hrp
    subst this
    rw [Nat.mem_primeFactors]
    exact ⟨hpp, hrn, by have := hr'.1.1; omega⟩
  have hBD : B ⊆ D := fun p hp => ((hBm p).mp hp).1
  let R' := R.filter (fun r => ¬ r ∣ n)
  let T := fun r : ℕ => ((Finset.Ioc r (n/r)).filter (fun v => v.Prime ∧ (n-r*v).Prime)).image
    (fun v => n - r * v)
  have hDB : D \ B = R'.biUnion T := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_biUnion, R', T, Finset.mem_filter, Finset.mem_image,
      hFm]
    constructor
    · rintro ⟨hpD, hpB⟩
      obtain ⟨hp1, hpp, r, hr, v, hv, hvp, h⟩ := (hDm p).mp hpD
      have hrn : ¬ r ∣ n := by
        intro hrn
        exact hpB ((hBm p).mpr ⟨hpD, r, hr, hrn, v, hv, hvp, h⟩)
      refine ⟨r, ⟨hr, hrn⟩, v, ⟨hv, hvp, ?_⟩, by omega⟩
      have : n - r * v = p := by omega
      rw [this]; exact hpp
    · rintro ⟨r, ⟨hr, hrn⟩, v, ⟨hv, hvp, hpr⟩, hpe⟩
      have hle : r * v ≤ n := by
        have := (Nat.le_div_iff_mul_le (by have := ((hRm r).mp hr).1.1; omega)).mp hv.2
        linarith
      have hpD : p ∈ D := by
        refine (hDm p).mpr ⟨by omega, by rw [← hpe]; exact hpr, r, hr, v, hv, hvp, by omega⟩
      refine ⟨hpD, fun hpB => ?_⟩
      obtain ⟨_, r', hr', hr'n, v', hv', hv'p, h'⟩ := (hBm p).mp hpB
      have hr1 := (hRm r).mp hr
      have hr2 := (hRm r').mp hr'
      have heq : r * v = r' * v' := by omega
      have := chen_cube_uniq hr1.2 hr2.2 hvp hv'p hv.1 hv'.1 heq
      subst this
      exact hrn hr'n
  have hle : ∀ r v, (r < v ∧ v ≤ n / r) → r * v ≤ n := by
    intro r v hv
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · subst h0; simp
    · have := (Nat.le_div_iff_mul_le h0).mp hv.2
      linarith
  have hrpos : ∀ r v, (r < v ∧ v ≤ n / r) → 0 < r := by
    intro r v hv
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · subst h0; have := hv.2; simp at this; omega
    · exact h0
  have hcardT : ∀ r, (T r).card = F r := by
    intro r
    apply Finset.card_image_of_injOn
    intro v hv v' hv' hvv
    rw [Finset.mem_coe, hFm] at hv hv'
    simp only at hvv
    have h1 := hle r v hv.1
    have h2 := hle r v' hv'.1
    have h3 : r * v = r * v' := by omega
    exact Nat.eq_of_mul_eq_mul_left (hrpos r v hv.1) h3
  have hdisj : ∀ r ∈ R', ∀ r' ∈ R', r ≠ r' → Disjoint (T r) (T r') := by
    intro r hr r' hr' hne
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [T, Finset.mem_image, hFm] at hp hp'
    obtain ⟨v, ⟨hv, hvp, _⟩, hpe⟩ := hp
    obtain ⟨v', ⟨hv', hvp', _⟩, hpe'⟩ := hp'
    have h1 := hle r v hv
    have h2 := hle r' v' hv'
    have hr1 := (hRm r).mp (Finset.mem_filter.mp hr).1
    have hr2 := (hRm r').mp (Finset.mem_filter.mp hr').1
    have := chen_cube_uniq hr1.2 hr2.2 hvp hvp' hv.1 hv'.1 (by omega)
    exact hne this
  have hRL : R' = L ∪ H := by
    ext r
    simp only [R', L, H, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      rcases le_or_gt (r ^ 3) n with h | h
      · exact Or.inl ⟨h1, h2, h⟩
      · exact Or.inr ⟨h1, h2, h⟩
    · rintro (⟨h1, h2, _⟩ | ⟨h1, h2, _⟩) <;> exact ⟨h1, h2⟩
  have hLH : Disjoint L H := by
    rw [Finset.disjoint_left]
    intro r h1 h2
    have := ((hLm r).mp h1).2.2
    have := ((hHm r).mp h2).2.2
    omega
  have hsum : ∑ r ∈ R', F r = (∑ r ∈ L, F r) + ∑ r ∈ H, F r := by
    rw [hRL, Finset.sum_union hLH]
  have hcardDB : (D \ B).card = ∑ r ∈ R', F r := by
    rw [hDB, Finset.card_biUnion hdisj]
    exact Finset.sum_congr rfl (fun r _ => hcardT r)
  have hsplit := Finset.card_sdiff_add_card_eq_card hBD
  refine ⟨?_, Finset.card_le_card hBsub⟩
  rw [add_assoc, ← hsum, ← hcardDB]
  omega

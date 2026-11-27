import Mathlib

private lemma fcq_cop0 (x y z w : ℕ) (h : x*y = z*w+1) : Nat.Coprime x z := by
  have h1 : Nat.gcd x z ∣ x*y := Dvd.dvd.mul_right (Nat.gcd_dvd_left x z) y
  have h2 : Nat.gcd x z ∣ z*w := Dvd.dvd.mul_right (Nat.gcd_dvd_right x z) w
  rw [h] at h1
  have := (Nat.dvd_add_right h2).mp h1
  exact Nat.dvd_one.mp this

private lemma fcq_bez (p1 p2 : ℕ) (h : 1 ≤ p1) (hc : Nat.Coprime p2 p1) :
    ∃ a b : ℕ, a < p1 ∧ b * p1 = a * p2 + 1 := by
  have hI : IsCoprime (p2:ℤ) (p1:ℤ) := Nat.isCoprime_iff_coprime.mpr hc
  obtain ⟨u, v, huv⟩ := hI
  have hp : (0:ℤ) < p1 := by exact_mod_cast h
  have hr0 : 0 ≤ (-u) % (p1:ℤ) := Int.emod_nonneg _ hp.ne'
  have hr1 : (-u) % (p1:ℤ) < p1 := Int.emod_lt_of_pos _ hp
  have hdef : (-u) % (p1:ℤ) + (p1:ℤ) * ((-u) / (p1:ℤ)) = -u := Int.emod_add_mul_ediv _ _
  generalize (-u) % (p1:ℤ) = r at *
  generalize (-u) / (p1:ℤ) = t at *
  have hb : (v - t*p2) * p1 = r*p2 + 1 := by
    linear_combination huv - (p2:ℤ) * hdef
  have hp2 : (0:ℤ) ≤ p2 := by positivity
  have hbpos : 0 ≤ v - t*p2 := by
    by_contra hneg
    push_neg at hneg
    nlinarith [mul_nonneg hr0 hp2]
  refine ⟨r.toNat, (v - t*p2).toNat, by omega, ?_⟩
  have e1 : ((r.toNat : ℕ):ℤ) = r := Int.toNat_of_nonneg hr0
  have e2 : (((v - t*p2).toNat : ℕ):ℤ) = v - t*p2 := Int.toNat_of_nonneg hbpos
  have : (((v - t*p2).toNat : ℕ):ℤ) * p1 = (r.toNat:ℤ) * p2 + 1 := by rw [e1, e2]; exact hb
  exact_mod_cast this

private lemma fcq_nbr (a q Q : ℕ) (hc : Nat.Coprime a q) (hq : 1 ≤ q) (hqQ : q ≤ Q) :
    ∃ s b : ℕ, Q < q + s ∧ s ≤ Q ∧ b * q = a * s + 1 := by
  obtain ⟨s0, b0, hs0, hb0⟩ := fcq_bez q a hq hc
  have hd := Nat.div_add_mod (Q - s0) q
  have hm := Nat.mod_lt (Q - s0) (show 0 < q by omega)
  refine ⟨s0 + q * ((Q - s0) / q), b0 + ((Q - s0) / q) * a, ?_, ?_, ?_⟩
  · generalize q * ((Q - s0) / q) = w at *
    generalize (Q - s0) % q = r at *
    omega
  · generalize q * ((Q - s0) / q) = w at *
    generalize (Q - s0) % q = r at *
    omega
  · have : b0 * q = s0 * a + 1 := hb0
    nlinarith [this]

private lemma fcq_uniq (p1 p2 a b a' b' : ℕ) (h1 : 1 ≤ p1) (hc : Nat.Coprime p1 p2)
    (ha : a ≤ p1) (hb : b ≤ p2) (ha' : a' ≤ p1) (hb' : b' ≤ p2)
    (e : b*p1 = a*p2+1) (e' : b'*p1 = a'*p2+1) : a = a' ∧ b = b' := by
  have hI : IsCoprime (p1:ℤ) (p2:ℤ) := Nat.isCoprime_iff_coprime.mpr hc
  have ez : (b:ℤ)*p1 = a*p2+1 := by exact_mod_cast e
  have ez' : (b':ℤ)*p1 = a'*p2+1 := by exact_mod_cast e'
  have hdvd : (p1:ℤ) ∣ ((a:ℤ) - a') * p2 := ⟨(b:ℤ) - b', by linear_combination ez' - ez⟩
  obtain ⟨k, hk⟩ := hI.dvd_of_dvd_mul_right hdvd
  have hp1 : (1:ℤ) ≤ p1 := by exact_mod_cast h1
  have haz : (a:ℤ) ≤ p1 := by exact_mod_cast ha
  have haz' : (a':ℤ) ≤ p1 := by exact_mod_cast ha'
  have hbz : (b:ℤ) ≤ p2 := by exact_mod_cast hb
  have hbz' : (b':ℤ) ≤ p2 := by exact_mod_cast hb'
  have ha0 : (0:ℤ) ≤ a := by positivity
  have ha0' : (0:ℤ) ≤ a' := by positivity
  have hp2 : (0:ℤ) ≤ p2 := by positivity
  have hk1 : k ≤ 1 := by
    by_contra hh
    push_neg at hh
    nlinarith
  have hk2 : -1 ≤ k := by
    by_contra hh
    push_neg at hh
    nlinarith
  interval_cases k
  · exfalso
    have : (a':ℤ) = p1 := by linarith
    have : (b':ℤ) * p1 ≤ p2 * p1 := mul_le_mul_of_nonneg_right hbz' (by linarith)
    nlinarith
  · have haa : (a:ℤ) = a' := by linarith
    have : ((b:ℤ) - b') * p1 = 0 := by linear_combination ez - ez' + (p2:ℤ) * haa
    rcases mul_eq_zero.mp this with h | h
    · refine ⟨by exact_mod_cast haa, by exact_mod_cast (by linarith : (b:ℤ) = b')⟩
    · exfalso; linarith
  · exfalso
    have : (a:ℤ) = p1 := by linarith
    have : (b:ℤ) * p1 ≤ p2 * p1 := mul_le_mul_of_nonneg_right hbz (by linarith)
    nlinarith

private lemma fcq_exist (p1 p2 : ℕ) (h1 : 1 ≤ p1) (h2 : 1 ≤ p2) (hc : Nat.Coprime p1 p2) :
    ∃ a b : ℕ, a ≤ p1 ∧ b ≤ p2 ∧ b * p1 = a * p2 + 1 := by
  obtain ⟨a, b, ha, hb⟩ := fcq_bez p1 p2 h1 hc.symm
  refine ⟨a, b, ha.le, ?_, hb⟩
  by_contra hh
  push_neg at hh
  nlinarith

private lemma fcq_K (a b p1 p2 c d Q : ℕ) (hd : d ≤ Q) (hs : Q < p1 + p2)
    (e : b*p1 = a*p2+1) : ¬ (a*d < c*p1 ∧ c*p2 < b*d) := by
  rintro ⟨h1, h2⟩
  have h1' : a*d + 1 ≤ c*p1 := h1
  have h2' : c*p2 + 1 ≤ b*d := h2
  have m1 := Nat.mul_le_mul_left p1 h2'
  have m2 := Nat.mul_le_mul_left p2 h1'
  have e2 : d * (b*p1) = d * (a*p2+1) := by rw [e]
  have : p1 + p2 ≤ d := by nlinarith
  omega

private lemma fcq_eqfrac (a p a' p' : ℕ) (h : Nat.Coprime a p) (h' : Nat.Coprime a' p')
    (e : a * p' = a' * p) : p = p' := by
  have d1 : p ∣ p' := by
    have : p ∣ a * p' := ⟨a', by rw [e]; ring⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_left h.symm this)
  have d2 : p' ∣ p := by
    have : p' ∣ a' * p := ⟨a, by rw [← e]; ring⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_left h'.symm this)
  exact Nat.dvd_antisymm d1 d2

private lemma fcq_F1 (Q : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (A : Set ℝ)
    (hA : ∀ x, x ∈ A ↔ ∃ d c : ℕ, 1 ≤ d ∧ d ≤ Q ∧ c ≤ d ∧ c.Coprime d ∧ |x-(c:ℝ)/d| ≤ δ/d)
    (a b p1 p2 : ℕ) (hp1 : 1 ≤ p1) (hp2 : 1 ≤ p2) (hs : Q < p1 + p2)
    (e : b*p1 = a*p2+1) (hb : b ≤ p2) (x : ℝ)
    (hx : x ∈ Set.Ioo (((a:ℝ)+δ)/p1) (((b:ℝ)-δ)/p2)) :
    x ∈ Set.Icc (0:ℝ) 1 ∧ x ∉ A := by
  obtain ⟨hx1, hx2⟩ := hx
  have p1r : (0:ℝ) < p1 := by exact_mod_cast hp1
  have p2r : (0:ℝ) < p2 := by exact_mod_cast hp2
  have er : (b:ℝ)*p1 = a*p2+1 := by exact_mod_cast e
  have ar : (0:ℝ) ≤ a := by positivity
  have br : (b:ℝ) ≤ p2 := by exact_mod_cast hb
  have hsmall : δ * ((p1:ℝ)+p2) < 1 := by
    have h' : (((a:ℝ)+δ)/p1) < (((b:ℝ)-δ)/p2) := lt_trans hx1 hx2
    rw [div_lt_div_iff₀ p1r p2r] at h'
    nlinarith
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have : 0 ≤ ((a:ℝ)+δ)/p1 := by positivity
    linarith
  · have h1 : ((b:ℝ)-δ)/p2 ≤ (b:ℝ)/p2 := by
      apply div_le_div_of_nonneg_right _ p2r.le; linarith
    have h2 : (b:ℝ)/p2 ≤ 1 := (div_le_one p2r).mpr br
    linarith
  · intro hxA
    obtain ⟨d, c, hd1, hdQ, hcd, hcop, habs⟩ := (hA x).mp hxA
    have dr : (0:ℝ) < d := by exact_mod_cast hd1
    rw [abs_le] at habs
    obtain ⟨hl, hr⟩ := habs
    have ca : Nat.Coprime a p1 := (fcq_cop0 p1 b a p2 (by rw [mul_comm]; exact e)).symm
    have cb : Nat.Coprime b p2 := fcq_cop0 b p1 p2 a (by rw [e]; ring) |>.symm |>.symm
    by_cases hc1 : c*p1 ≤ a*d
    · have key : (p1:ℝ)*(c+δ) ≤ d*(a+δ) := by
        rcases Nat.lt_or_eq_of_le hc1 with h | h
        · have h' : (c:ℝ)*p1 + 1 ≤ a*d := by exact_mod_cast h
          have : δ * (p1:ℝ) ≤ δ * (p1+p2) := by nlinarith
          nlinarith [mul_nonneg hδ dr.le]
        · have hdv : p1 ∣ d := by
            have : p1 ∣ a * d := ⟨c, by rw [← h]; ring⟩
            exact Nat.Coprime.dvd_of_dvd_mul_left ca.symm this
          have hle : (p1:ℝ) ≤ d := by exact_mod_cast Nat.le_of_dvd hd1 hdv
          have h' : (c:ℝ)*p1 = a*d := by exact_mod_cast h
          nlinarith [mul_le_mul_of_nonneg_left hle hδ]
      have : ((c:ℝ)+δ)/d ≤ ((a:ℝ)+δ)/p1 := by
        rw [div_le_div_iff₀ dr p1r]; linarith
      have h3 : x - (c:ℝ)/d ≤ δ/d := hr
      have : (c:ℝ)/d + δ/d = ((c:ℝ)+δ)/d := by ring
      linarith
    · push_neg at hc1
      by_cases hc2 : b*d ≤ c*p2
      · have key : (d:ℝ)*(b-δ) ≤ p2*(c-δ) := by
          rcases Nat.lt_or_eq_of_le hc2 with h | h
          · have h' : (b:ℝ)*d + 1 ≤ c*p2 := by exact_mod_cast h
            have : δ * (p2:ℝ) ≤ δ * (p1+p2) := by nlinarith
            nlinarith [mul_nonneg hδ dr.le]
          · have hdv : p2 ∣ d := by
              have : p2 ∣ b * d := ⟨c, by rw [h]; ring⟩
              exact Nat.Coprime.dvd_of_dvd_mul_left cb.symm this
            have hle : (p2:ℝ) ≤ d := by exact_mod_cast Nat.le_of_dvd hd1 hdv
            have h' : (b:ℝ)*d = c*p2 := by exact_mod_cast h
            nlinarith [mul_le_mul_of_nonneg_left hle hδ]
        have : ((b:ℝ)-δ)/p2 ≤ ((c:ℝ)-δ)/d := by
          rw [div_le_div_iff₀ p2r dr]; linarith
        have h3 : -(δ/d) ≤ x - (c:ℝ)/d := hl
        have : (c:ℝ)/d - δ/d = ((c:ℝ)-δ)/d := by ring
        linarith
      · push_neg at hc2
        exact fcq_K a b p1 p2 c d Q hdQ hs e ⟨hc1, hc2⟩

private lemma fcq_disj_aux (Q : ℕ) (a b p1 p2 a' b' p1' p2' : ℕ)
    (hp1 : 1 ≤ p1) (hp2 : 1 ≤ p2) (hp1' : 1 ≤ p1') (hp2' : 1 ≤ p2')
    (hp1'Q : p1' ≤ Q) (hp2'Q : p2' ≤ Q) (hs : Q < p1 + p2)
    (e : b*p1 = a*p2+1) (x : ℝ)
    (hx1 : (a:ℝ)/p1 < x) (hx2 : x < (b:ℝ)/p2) (hx3 : (a':ℝ)/p1' < x) (hx4 : x < (b':ℝ)/p2') :
    a'*p1 ≤ a*p1' ∧ b*p2' ≤ b'*p2 := by
  have p1r : (0:ℝ) < p1 := by exact_mod_cast hp1
  have p2r : (0:ℝ) < p2 := by exact_mod_cast hp2
  have p1'r : (0:ℝ) < p1' := by exact_mod_cast hp1'
  have p2'r : (0:ℝ) < p2' := by exact_mod_cast hp2'
  constructor
  · by_contra h
    push_neg at h
    have h2 : (a':ℝ)/p1' < (b:ℝ)/p2 := lt_trans hx3 hx2
    rw [div_lt_div_iff₀ p1'r p2r] at h2
    have h2' : a'*p2 < b*p1' := by exact_mod_cast h2
    exact fcq_K a b p1 p2 a' p1' Q hp1'Q hs e ⟨h, h2'⟩
  · by_contra h
    push_neg at h
    have h2 : (a:ℝ)/p1 < (b':ℝ)/p2' := lt_trans hx1 hx4
    rw [div_lt_div_iff₀ p1r p2'r] at h2
    have h2' : a*p2' < b'*p1 := by exact_mod_cast h2
    exact fcq_K a b p1 p2 b' p2' Q hp2'Q hs e ⟨h2', h⟩

private lemma fcq_F3 (Q : ℕ) (hQ : 0 < Q) (δ : ℝ) (hδ : 0 ≤ δ) (A : Set ℝ)
    (hA : ∀ x, x ∈ A ↔ ∃ d c : ℕ, 1 ≤ d ∧ d ≤ Q ∧ c ≤ d ∧ c.Coprime d ∧ |x-(c:ℝ)/d| ≤ δ/d)
    (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) (hxA : x ∉ A) :
    ∃ q s a b : ℕ, 1 ≤ q ∧ q ≤ Q ∧ 1 ≤ s ∧ s ≤ Q ∧ Q < q + s ∧ Nat.Coprime q s ∧
      a ≤ q ∧ b ≤ s ∧ b*q = a*s+1 ∧
      x ∈ Set.Ioo (((a:ℝ)+δ)/q) (((b:ℝ)-δ)/s) := by
  classical
  obtain ⟨hx0, hx1⟩ := hx
  let S : Finset (ℕ × ℕ) := ((Finset.Icc 0 Q) ×ˢ (Finset.Icc 1 Q)).filter
    (fun e => e.1 ≤ e.2 ∧ Nat.Coprime e.1 e.2 ∧ (e.1:ℝ)/e.2 ≤ x)
  have hmemS : ∀ e : ℕ × ℕ, e ∈ S ↔ (e.1 ≤ Q ∧ 1 ≤ e.2 ∧ e.2 ≤ Q) ∧
      (e.1 ≤ e.2 ∧ Nat.Coprime e.1 e.2 ∧ (e.1:ℝ)/e.2 ≤ x) := by
    intro e
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Nat.zero_le, true_and]
  have hne : S.Nonempty := ⟨(0,1), by
    rw [hmemS]
    exact ⟨⟨Nat.zero_le _, le_refl _, hQ⟩, Nat.zero_le _, by simp, by simpa using hx0⟩⟩
  obtain ⟨⟨a, q⟩, hmem, hmax⟩ := Finset.exists_max_image S (fun e : ℕ × ℕ => (e.1:ℝ)/e.2) hne
  rw [hmemS] at hmem
  obtain ⟨⟨haQ, hq1, hqQ⟩, haq, hcop, hle⟩ := hmem
  simp only at haq hcop hle hq1 hqQ haQ
  have qr : (0:ℝ) < q := by exact_mod_cast hq1
  have hlt : (a:ℝ)/q < x := by
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      apply hxA
      rw [hA]
      refine ⟨q, a, hq1, hqQ, haq, hcop, ?_⟩
      rw [h, sub_self, abs_zero]
      positivity
  have haq' : a < q := by
    have : (a:ℝ)/q < 1 := lt_of_lt_of_le hlt hx1
    rw [div_lt_one qr] at this
    exact_mod_cast this
  obtain ⟨s, b, hsum, hsQ, hb⟩ := fcq_nbr a q Q hcop hq1 hqQ
  have hs1 : 1 ≤ s := by omega
  have hbs : b ≤ s := by
    by_contra hh
    push_neg at hh
    nlinarith
  have cbs : Nat.Coprime b s := fcq_cop0 b q s a (by rw [hb]; ring)
  have cqs : Nat.Coprime q s := fcq_cop0 q b s a (by rw [mul_comm, hb]; ring)
  have sr : (0:ℝ) < s := by exact_mod_cast hs1
  have hbr : (b:ℝ)*q = a*s+1 := by exact_mod_cast hb
  have hxb : x < (b:ℝ)/s := by
    by_contra hh
    push_neg at hh
    have hmS : (b, s) ∈ S := by
      rw [hmemS]
      exact ⟨⟨by omega, hs1, hsQ⟩, hbs, cbs, hh⟩
    have := hmax (b, s) hmS
    simp only at this
    rw [div_le_div_iff₀ sr qr] at this
    nlinarith
  have h1 : ¬ |x - (a:ℝ)/q| ≤ δ/q := fun h => hxA ((hA x).mpr ⟨q, a, hq1, hqQ, haq, hcop, h⟩)
  have h2 : ¬ |x - (b:ℝ)/s| ≤ δ/s := fun h => hxA ((hA x).mpr ⟨s, b, hs1, hsQ, hbs, cbs, h⟩)
  rw [abs_of_pos (by linarith)] at h1
  rw [abs_of_neg (by linarith)] at h2
  push_neg at h1 h2
  refine ⟨q, s, a, b, hq1, hqQ, hs1, hsQ, hsum, cqs, haq'.le, hbs, hb, ?_, ?_⟩
  · have : ((a:ℝ)+δ)/q = (a:ℝ)/q + δ/q := by ring
    linarith
  · have : ((b:ℝ)-δ)/s = (b:ℝ)/s - δ/s := by ring
    linarith

private lemma fcq_main (Q : ℕ) (δ : ℝ) (hQ : 0 < Q) (hδ : 0 ≤ δ) (A : Set ℝ) (D : Finset (ℕ × ℕ))
    (hA : ∀ x, x ∈ A ↔ ∃ d c : ℕ, 1 ≤ d ∧ d ≤ Q ∧ c ≤ d ∧ c.Coprime d ∧ |x-(c:ℝ)/d| ≤ δ/d)
    (hD : ∀ p, p ∈ D ↔ (1 ≤ p.1 ∧ p.1 ≤ Q) ∧ (1 ≤ p.2 ∧ p.2 ≤ Q) ∧ Q < p.1 + p.2 ∧ p.1.Coprime p.2) :
    (Set.Icc (0:ℝ) 1 ⊆ A ↔ 1 ≤ δ*((Q:ℝ)+1)) ∧
      MeasureTheory.volume (Aᶜ ∩ Set.Icc (0:ℝ) 1) =
        ∑ p ∈ D, ENNReal.ofReal ((1-δ*((p.1:ℝ)+p.2))/((p.1:ℝ)*p.2)) ∧
      ∃ ab : ℕ × ℕ → ℕ × ℕ,
        (∀ p ∈ D, (ab p).1 ≤ p.1 ∧ (ab p).2 ≤ p.2 ∧ (ab p).2*p.1 = (ab p).1*p.2+1) ∧
        ∀ f : ℝ → ℂ, MeasureTheory.IntegrableOn f (Set.Icc 0 1) →
          (∫ x in Aᶜ ∩ Set.Icc (0:ℝ) 1, f x) =
            ∑ p ∈ D, ∫ x in Set.Ioo ((((ab p).1:ℝ)+δ)/p.1) ((((ab p).2:ℝ)-δ)/p.2), f x := by
  classical
  have hex : ∀ p : ℕ × ℕ, p ∈ D → ∃ e : ℕ × ℕ, e.1 ≤ p.1 ∧ e.2 ≤ p.2 ∧ e.2*p.1 = e.1*p.2+1 := by
    intro p hp
    obtain ⟨⟨h1, _⟩, ⟨h2, _⟩, _, hc⟩ := (hD p).mp hp
    obtain ⟨a, b, ha, hb, hab⟩ := fcq_exist p.1 p.2 h1 h2 hc
    exact ⟨(a, b), ha, hb, hab⟩
  choose! ab hab using hex
  have hF1 : ∀ p ∈ D, ∀ x ∈ Set.Ioo ((((ab p).1:ℝ)+δ)/p.1) ((((ab p).2:ℝ)-δ)/p.2),
      x ∈ Set.Icc (0:ℝ) 1 ∧ x ∉ A := by
    intro p hp x hx
    obtain ⟨⟨h1, _⟩, ⟨h2, _⟩, hs, _⟩ := (hD p).mp hp
    obtain ⟨_, hb, e⟩ := hab p hp
    exact fcq_F1 Q δ hδ A hA (ab p).1 (ab p).2 p.1 p.2 h1 h2 hs e hb x hx
  have hdiff : ∀ p ∈ D, (((ab p).2:ℝ)-δ)/p.2 - (((ab p).1:ℝ)+δ)/p.1
      = (1-δ*((p.1:ℝ)+p.2))/((p.1:ℝ)*p.2) := by
    intro p hp
    obtain ⟨⟨h1, _⟩, ⟨h2, _⟩, hs, _⟩ := (hD p).mp hp
    obtain ⟨_, hb, e⟩ := hab p hp
    have p1r : (p.1:ℝ) ≠ 0 := by exact_mod_cast (by omega : p.1 ≠ 0)
    have p2r : (p.2:ℝ) ≠ 0 := by exact_mod_cast (by omega : p.2 ≠ 0)
    have er : ((ab p).2:ℝ) * p.1 = (ab p).1 * p.2 + 1 := by exact_mod_cast e
    field_simp
    linear_combination er
  have hE : Aᶜ ∩ Set.Icc (0:ℝ) 1 = ⋃ p ∈ D, Set.Ioo ((((ab p).1:ℝ)+δ)/p.1) ((((ab p).2:ℝ)-δ)/p.2) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨hxA, hx⟩
      obtain ⟨q, s, a, b, hq1, hqQ, hs1, hsQ, hsum, cqs, haq, hbs, hb, hxI⟩ :=
        fcq_F3 Q hQ δ hδ A hA x hx hxA
      have hpD : (q, s) ∈ D := (hD _).mpr ⟨⟨hq1, hqQ⟩, ⟨hs1, hsQ⟩, hsum, cqs⟩
      obtain ⟨h1, h2, h3⟩ := hab (q, s) hpD
      obtain ⟨rfl, rfl⟩ := fcq_uniq q s a b (ab (q, s)).1 (ab (q, s)).2 hq1 cqs haq hbs h1 h2 hb h3
      exact ⟨(q, s), hpD, hxI⟩
    · rintro ⟨p, hp, hx⟩
      have := hF1 p hp x hx
      exact ⟨this.2, this.1⟩
  have hdisj : Set.PairwiseDisjoint (↑D : Set (ℕ × ℕ))
      (fun p => Set.Ioo ((((ab p).1:ℝ)+δ)/p.1) ((((ab p).2:ℝ)-δ)/p.2)) := by
    intro p hp p' hp' hne
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    apply hne
    have hp := Finset.mem_coe.mp hp
    have hp' := Finset.mem_coe.mp hp'
    obtain ⟨⟨h1, h1Q⟩, ⟨h2, h2Q⟩, hs, hc⟩ := (hD p).mp hp
    obtain ⟨⟨h1', h1Q'⟩, ⟨h2', h2Q'⟩, hs', hc'⟩ := (hD p').mp hp'
    obtain ⟨_, _, e⟩ := hab p hp
    obtain ⟨_, _, e'⟩ := hab p' hp'
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hx3, hx4⟩ := hx'
    have p1r : (0:ℝ) < p.1 := by exact_mod_cast h1
    have p2r : (0:ℝ) < p.2 := by exact_mod_cast h2
    have p1r' : (0:ℝ) < p'.1 := by exact_mod_cast h1'
    have p2r' : (0:ℝ) < p'.2 := by exact_mod_cast h2'
    have ar : (0:ℝ) ≤ (ab p).1 := by positivity
    have ar' : (0:ℝ) ≤ (ab p').1 := by positivity
    have l1 : ((ab p).1:ℝ)/p.1 ≤ (((ab p).1:ℝ)+δ)/p.1 :=
      div_le_div_of_nonneg_right (by linarith) p1r.le
    have l2 : (((ab p).2:ℝ)-δ)/p.2 ≤ ((ab p).2:ℝ)/p.2 :=
      div_le_div_of_nonneg_right (by linarith) p2r.le
    have l3 : ((ab p').1:ℝ)/p'.1 ≤ (((ab p').1:ℝ)+δ)/p'.1 :=
      div_le_div_of_nonneg_right (by linarith) p1r'.le
    have l4 : (((ab p').2:ℝ)-δ)/p'.2 ≤ ((ab p').2:ℝ)/p'.2 :=
      div_le_div_of_nonneg_right (by linarith) p2r'.le
    have A1 := fcq_disj_aux Q (ab p).1 (ab p).2 p.1 p.2 (ab p').1 (ab p').2 p'.1 p'.2
      h1 h2 h1' h2' h1Q' h2Q' hs e x (by linarith) (by linarith) (by linarith) (by linarith)
    have A2 := fcq_disj_aux Q (ab p').1 (ab p').2 p'.1 p'.2 (ab p).1 (ab p).2 p.1 p.2
      h1' h2' h1 h2 h1Q h2Q hs' e' x (by linarith) (by linarith) (by linarith) (by linarith)
    have ca : Nat.Coprime (ab p).1 p.1 := (fcq_cop0 p.1 (ab p).2 (ab p).1 p.2 (by rw [mul_comm]; exact e)).symm
    have ca' : Nat.Coprime (ab p').1 p'.1 := (fcq_cop0 p'.1 (ab p').2 (ab p').1 p'.2 (by rw [mul_comm]; exact e')).symm
    have cb : Nat.Coprime (ab p).2 p.2 := fcq_cop0 _ p.1 p.2 (ab p).1 (by rw [e]; ring)
    have cb' : Nat.Coprime (ab p').2 p'.2 := fcq_cop0 _ p'.1 p'.2 (ab p').1 (by rw [e']; ring)
    have q1 : p.1 = p'.1 := fcq_eqfrac _ _ _ _ ca ca' (le_antisymm A2.1 A1.1)
    have q2 : p.2 = p'.2 := fcq_eqfrac _ _ _ _ cb cb' (le_antisymm A1.2 A2.2)
    exact Prod.ext q1 q2
  refine ⟨?_, ?_, ab, hab, ?_⟩
  · constructor
    · intro hsub
      by_contra hlt
      push_neg at hlt
      have hp0 : ((1, Q) : ℕ × ℕ) ∈ D := (hD _).mpr ⟨⟨le_refl _, hQ⟩, ⟨hQ, le_refl _⟩, by simp, by simp⟩
      have hd := hdiff _ hp0
      have hpos : 0 < (1 - δ * (((((1, Q) : ℕ × ℕ)).1:ℝ) + ((((1, Q) : ℕ × ℕ)).2:ℝ))) /
          ((((((1, Q) : ℕ × ℕ)).1:ℝ)) * ((((1, Q) : ℕ × ℕ)).2:ℝ)) := by
        apply div_pos
        · simp only [Nat.cast_one]; linarith
        · have : (0:ℝ) < Q := by exact_mod_cast hQ
          simp only [Nat.cast_one]; positivity
      have hne : (Set.Ioo ((((ab (1,Q)).1:ℝ)+δ)/((1,Q):ℕ×ℕ).1) ((((ab (1,Q)).2:ℝ)-δ)/((1,Q):ℕ×ℕ).2)).Nonempty :=
        Set.nonempty_Ioo.mpr (by linarith)
      obtain ⟨x, hx⟩ := hne
      have := hF1 _ hp0 x hx
      exact this.2 (hsub this.1)
    · intro h x hx
      by_contra hxA
      have hmem : x ∈ Aᶜ ∩ Set.Icc (0:ℝ) 1 := ⟨hxA, hx⟩
      rw [hE] at hmem
      simp only [Set.mem_iUnion, exists_prop] at hmem
      obtain ⟨p, hp, hxp⟩ := hmem
      obtain ⟨_, _, hs, _⟩ := (hD p).mp hp
      have hd := hdiff p hp
      have hlt : (((ab p).1:ℝ)+δ)/p.1 < (((ab p).2:ℝ)-δ)/p.2 := lt_trans hxp.1 hxp.2
      have h1 : (0:ℝ) < p.1 := by
        have := ((hD p).mp hp).1.1; exact_mod_cast this
      have h2 : (0:ℝ) < p.2 := by
        have := ((hD p).mp hp).2.1.1; exact_mod_cast this
      have hq : (Q:ℝ) + 1 ≤ p.1 + p.2 := by exact_mod_cast hs
      have : 0 < (1 - δ * ((p.1:ℝ) + p.2)) / ((p.1:ℝ) * p.2) := by linarith
      have h3 : 0 < 1 - δ * ((p.1:ℝ) + p.2) := by
        by_contra hh; push_neg at hh
        have := div_nonpos_of_nonpos_of_nonneg hh (by positivity : (0:ℝ) ≤ (p.1:ℝ) * p.2)
        linarith
      nlinarith [mul_le_mul_of_nonneg_left hq hδ]
  · rw [hE, MeasureTheory.measure_biUnion_finset hdisj (fun p _ => measurableSet_Ioo)]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Real.volume_Ioo, hdiff p hp]
  · intro f hf
    rw [hE]
    apply MeasureTheory.integral_biUnion_finset D (fun p _ => measurableSet_Ioo) hdisj
    intro p hp
    apply hf.mono_set
    intro x hx
    exact (hF1 p hp x hx).1

theorem Conjectures.Goldbach.FareyComplementQuadrature :
    ∀ (Q : ℕ) (δ : ℝ), 0 < Q → 0 ≤ δ →
      let A := {x : ℝ | ∃ d c : ℕ, 1 ≤ d ∧ d ≤ Q ∧ c ≤ d ∧ c.Coprime d ∧ |x-(c:ℝ)/d| ≤ δ/d}
      let D := ((Finset.Icc 1 Q) ×ˢ (Finset.Icc 1 Q)).filter (fun p => Q < p.1+p.2 ∧ p.1.Coprime p.2)
      (Set.Icc (0:ℝ) 1 ⊆ A ↔ 1 ≤ δ*((Q:ℝ)+1)) ∧
      MeasureTheory.volume (Aᶜ ∩ Set.Icc (0:ℝ) 1) =
        ∑ p ∈ D, ENNReal.ofReal ((1-δ*((p.1:ℝ)+p.2))/((p.1:ℝ)*p.2)) ∧
      ∃ ab : ℕ × ℕ → ℕ × ℕ,
        (∀ p ∈ D, (ab p).1 ≤ p.1 ∧ (ab p).2 ≤ p.2 ∧ (ab p).2*p.1 = (ab p).1*p.2+1) ∧
        ∀ f : ℝ → ℂ, MeasureTheory.IntegrableOn f (Set.Icc 0 1) →
          (∫ x in Aᶜ ∩ Set.Icc (0:ℝ) 1, f x) =
            ∑ p ∈ D, ∫ x in Set.Ioo ((((ab p).1:ℝ)+δ)/p.1) ((((ab p).2:ℝ)-δ)/p.2), f x := by
  intro Q δ hQ hδ A D
  refine fcq_main Q δ hQ hδ A D (fun x => Iff.rfl) ?_
  intro p
  simp only [D, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  tauto

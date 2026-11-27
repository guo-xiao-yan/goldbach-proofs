import Mathlib

private lemma hs_modeq (n d c b s q j : ℕ) (hds : d * s ≡ b [MOD n]) (hdc : d * c ≡ 1 [MOD n]) :
    (b + d * q) * j ≡ 1 [MOD n] ↔ (q + s) * j ≡ c [MOD n] := by
  have h1 : (b + d * q) * j ≡ d * ((q + s) * j) [MOD n] := by
    have : b + d * q ≡ d * s + d * q [MOD n] := Nat.ModEq.add_right _ hds.symm
    have h2 := Nat.ModEq.mul_right j this
    have e : (d * s + d * q) * j = d * ((q + s) * j) := by ring
    rwa [e] at h2
  constructor
  · intro h
    have h3 : d * ((q + s) * j) ≡ 1 [MOD n] := h1.symm.trans h
    have h4 := Nat.ModEq.mul_left c h3
    have e : c * (d * ((q + s) * j)) = (d * c) * ((q + s) * j) := by ring
    rw [e, mul_one] at h4
    have h5 := Nat.ModEq.mul_right ((q + s) * j) hdc
    rw [one_mul] at h5
    exact h5.symm.trans h4
  · intro h
    have h3 := Nat.ModEq.mul_left d h
    exact h1.trans (h3.trans hdc)

private lemma hs_div (d x : ℕ) (hd : 0 < d) : d * (x / d) ≤ x ∧ x < d * (x / d) + d := by
  have h1 := Nat.div_add_mod x d
  have h2 := Nat.mod_lt x hd
  omega

theorem Conjectures.Goldbach.FareyHyperbolaShift :
    ∀ (n d b l h s c : ℕ) (J : Finset ℕ), 1 < n → 0 < d → b < d → b ≤ h → l ≤ h → h < n → s < n → (d*s) % n = b % n → (d*c) % n = 1 → let lo := (l+d-1-b)/d; let hi := (h-b)/d; let I := Finset.Icc (lo+s) (hi+s); let count := fun (I : Finset ℕ) (k : ℕ) => ((I.product J).filter (fun (x : ℕ × ℕ) => (x.1*x.2) % n = k % n)).card; hi+s < n ∧ count ((Finset.Icc l h).filter (fun u => u % d = b)) 1 = count I c ∧ |(I.card:ℝ) - ((h-l+1 : ℕ):ℝ)/d| ≤ 1 := by
  intro n d b l h s c J hn hd hbd hbh hlh hhn hsn hds hdc lo hi I count
  have hlo : lo = (l+d-1-b)/d := rfl
  have hhi : hi = (h-b)/d := rfl
  clear_value lo hi
  have hb : b % n = b := Nat.mod_eq_of_lt (by omega)
  have hds' : d * s % n = b := by rw [hds, hb]
  have hdsM : d * s ≡ b [MOD n] := by
    show d * s % n = b % n
    rw [hds']; exact hb.symm
  have hdcM : d * c ≡ 1 [MOD n] := by
    show (d * c) % n = 1 % n
    rw [hdc, Nat.mod_eq_of_lt hn]
  obtain ⟨hhi1, hhi2⟩ := hs_div d (h - b) hd
  obtain ⟨hlo1, hlo2⟩ := hs_div d (l + d - 1 - b) hd
  rw [← hhi] at hhi1 hhi2
  rw [← hlo] at hlo1 hlo2
  have hk := Nat.mod_add_div (d * s) n
  rw [hds'] at hk
  have hkd : d * s / n < d := by
    by_contra hcon
    have hc : d ≤ d * s / n := not_lt.mp hcon
    have : n * d ≤ n * (d * s / n) := Nat.mul_le_mul_left n hc
    have : d * s < d * n := Nat.mul_lt_mul_of_pos_left hsn hd
    have : n * d = d * n := Nat.mul_comm n d
    omega
  have hfirst : hi + s < n := by
    have hlt : d * (hi + s) < d * n := by
      have e : d * (hi + s) = d * hi + d * s := by ring
      have h1 : n * (d * s / n + 1) ≤ n * d := Nat.mul_le_mul_left n hkd
      have h2 : n * (d * s / n + 1) = n * (d * s / n) + n := by ring
      have : n * d = d * n := Nat.mul_comm n d
      omega
    exact lt_of_mul_lt_mul_left hlt (Nat.zero_le _)
  refine ⟨hfirst, ?_, ?_⟩
  · have hrange : ∀ q : ℕ, (l ≤ b + d * q ∧ b + d * q ≤ h) ↔ (lo ≤ q ∧ q ≤ hi) := by
      intro q
      have e1 : lo ≤ q ↔ (l + d - 1 - b) < (q + 1) * d := by
        rw [hlo, ← Nat.div_lt_iff_lt_mul hd]; exact Nat.lt_succ_iff.symm
      have e2 : q ≤ hi ↔ q * d ≤ h - b := by
        rw [hhi]; exact Nat.le_div_iff_mul_le hd
      rw [e1, e2]
      have e3 : (q + 1) * d = d * q + d := by ring
      have e4 : q * d = d * q := by ring
      rw [e3, e4]
      omega
    have hmod : ∀ q : ℕ, (b + d * q) % d = b ∧ (b + d * q) / d = q := by
      intro q
      refine ⟨?_, ?_⟩
      · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hbd]
      · rw [Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hbd, zero_add]
    have hrec : ∀ u : ℕ, u % d = b → u = b + d * (u / d) := by
      intro u hu
      have := Nat.mod_add_div u d
      omega
    show ((((Finset.Icc l h).filter (fun u => u % d = b)).product J).filter
        (fun (x : ℕ × ℕ) => (x.1*x.2) % n = 1 % n)).card =
      ((I.product J).filter (fun (x : ℕ × ℕ) => (x.1*x.2) % n = c % n)).card
    refine Finset.card_nbij' (fun x => (x.1 / d + s, x.2)) (fun x => (b + d * (x.1 - s), x.2)) ?_ ?_ ?_ ?_
    · intro x hx
      obtain ⟨u, j⟩ := x
      simp only [Finset.product_eq_sprod, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, I] at hx ⊢
      obtain ⟨⟨⟨⟨hu1, hu2⟩, hu3⟩, hj⟩, hm⟩ := hx
      have hu := hrec u hu3
      have hr := (hrange (u / d)).1 (by rw [← hu]; exact ⟨hu1, hu2⟩)
      refine ⟨⟨⟨by omega, by omega⟩, hj⟩, ?_⟩
      have := (hs_modeq n d c b s (u / d) j hdsM hdcM).1
      rw [← hu] at this
      exact this hm
    · intro x hx
      obtain ⟨t, j⟩ := x
      simp only [Finset.product_eq_sprod, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, I] at hx ⊢
      obtain ⟨⟨⟨ht1, ht2⟩, hj⟩, hm⟩ := hx
      have hr := (hrange (t - s)).2 ⟨by omega, by omega⟩
      refine ⟨⟨⟨hr, (hmod (t - s)).1⟩, hj⟩, ?_⟩
      have h2 := (hs_modeq n d c b s (t - s) j hdsM hdcM).2
      have e : t - s + s = t := by omega
      rw [e] at h2
      exact h2 hm
    · intro x hx
      obtain ⟨u, j⟩ := x
      simp only [Finset.product_eq_sprod, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hx
      have hu := hrec u hx.1.1.2
      simp only [Nat.add_sub_cancel]
      rw [← hu]
    · intro x hx
      obtain ⟨t, j⟩ := x
      simp only [Finset.product_eq_sprod, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, I] at hx
      simp only [(hmod _).2]
      have : t - s + s = t := by omega
      rw [this]
  · have hcard : I.card = hi + 1 - lo := by
      show (Finset.Icc (lo + s) (hi + s)).card = _
      rw [Nat.card_Icc]; omega
    have hle : lo ≤ hi + 1 := by
      by_contra hcon
      have hcon := not_le.mp hcon
      have : d * (hi + 2) ≤ d * lo := Nat.mul_le_mul_left d (by omega)
      have e : d * (hi + 2) = d * hi + d + d := by ring
      omega
    obtain ⟨k, hk⟩ : ∃ k, k = I.card := ⟨_, rfl⟩
    have hk2 : k + lo = hi + 1 := by omega
    have hk3 : d * k + d * lo = d * hi + d := by
      have : d * (k + lo) = d * (hi + 1) := by rw [hk2]
      linarith [mul_add d k lo, mul_add d hi 1]
    have F1 : d * k ≤ (h - l + 1) + d := by omega
    have F2 : (h - l + 1) ≤ d * k + d := by omega
    rw [← hk]
    have hdR : (0:ℝ) < d := by exact_mod_cast hd
    have F1R : (d:ℝ) * k ≤ ((h - l + 1 : ℕ):ℝ) + d := by exact_mod_cast F1
    have F2R : ((h - l + 1 : ℕ):ℝ) ≤ (d:ℝ) * k + d := by exact_mod_cast F2
    rw [show (k:ℝ) - ((h - l + 1 : ℕ):ℝ) / d = ((d:ℝ) * k - ((h - l + 1 : ℕ):ℝ)) / d by field_simp]
    rw [abs_div, abs_of_pos hdR, div_le_one hdR, abs_le]
    constructor <;> linarith

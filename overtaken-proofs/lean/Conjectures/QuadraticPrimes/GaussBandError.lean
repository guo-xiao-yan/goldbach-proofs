import Mathlib

private theorem gbe_recip :
    ∀ a b p r v : ℕ, 0 < a → a ≤ b → p.Prime → p = a ^ 2 + b ^ 2 →
      r < p → v < b → (b * r) % p = a % p → (a * v) % b = 1 % b →
      ∃ j : ℤ, (r : ℝ) / p + (v : ℝ) / b = (j : ℝ) + (a : ℝ) / ((b : ℝ) * p) := by
  intro a b p r v ha hab hp hpab hrp hvb hbr hav
  have hp2 : 2 ≤ p := hp.two_le
  have hp0 : 0 < p := hp.pos
  have ha1 : 1 ≤ a := ha
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have hb_lt_p : b < p := by
    nlinarith [hpab, ha1, hb0]
  have hpb_not : ¬ p ∣ b := by
    intro hdvd
    have : p ≤ b := Nat.le_of_dvd hb0 hdvd
    omega
  have hcop : Nat.Coprime b p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpb_not).symm
  set X : ℤ := (b : ℤ) * (r : ℤ) + (p : ℤ) * (v : ℤ) - (a : ℤ) with hX
  have h1p : ((b : ZMod p) * (r : ZMod p)) = (a : ZMod p) := by
    rw [← Nat.cast_mul, ZMod.natCast_eq_natCast_iff']
    exact hbr
  have hXp : ((X : ℤ) : ZMod p) = 0 := by
    have hrepr : ((X : ℤ) : ZMod p) =
        (b : ZMod p) * (r : ZMod p) + (p : ZMod p) * (v : ZMod p) - (a : ZMod p) := by
      rw [hX]
      push_cast
      ring
    rw [hrepr, h1p, ZMod.natCast_self p]
    ring
  have h1b : ((a : ZMod b) * (v : ZMod b)) = 1 := by
    rw [← Nat.cast_mul, ← Nat.cast_one]
    exact (ZMod.natCast_eq_natCast_iff' (a * v) 1 b).mpr (by simpa using hav)
  have hpb : (p : ZMod b) = (a : ZMod b) ^ 2 := by
    rw [hpab]
    push_cast
    rw [ZMod.natCast_self]
    ring
  have hXb : ((X : ℤ) : ZMod b) = 0 := by
    have hrepr : ((X : ℤ) : ZMod b) =
        (b : ZMod b) * (r : ZMod b) + (p : ZMod b) * (v : ZMod b) - (a : ZMod b) := by
      rw [hX]
      push_cast
      ring
    rw [hrepr, ZMod.natCast_self b, hpb]
    have hstep : (a : ZMod b) ^ 2 * (v : ZMod b) =
        (a : ZMod b) * ((a : ZMod b) * (v : ZMod b)) := by ring
    rw [zero_mul, zero_add, hstep, h1b]
    ring
  have hpdvd : (p : ℤ) ∣ X := (ZMod.intCast_zmod_eq_zero_iff_dvd X p).mp hXp
  have hbdvd : (b : ℤ) ∣ X := (ZMod.intCast_zmod_eq_zero_iff_dvd X b).mp hXb
  have hcopZ : IsCoprime (b : ℤ) (p : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact hcop
  obtain ⟨j, hj⟩ := hcopZ.mul_dvd hbdvd hpdvd
  refine ⟨j, ?_⟩
  have hcast : (b : ℝ) * (r : ℝ) + (p : ℝ) * (v : ℝ) - (a : ℝ) =
      ((b : ℝ) * (p : ℝ)) * (j : ℝ) := by
    have hXR : (X : ℝ) = (b : ℝ) * (r : ℝ) + (p : ℝ) * (v : ℝ) - (a : ℝ) := by
      rw [hX]
      push_cast
      ring
    have hjR : (X : ℝ) = ((b : ℝ) * (p : ℝ)) * (j : ℝ) := by
      have := congrArg (fun t : ℤ => (t : ℝ)) hj
      push_cast at this
      exact this
    rw [← hXR, hjR]
  have hbp0 : ((b : ℝ) * (p : ℝ)) ≠ 0 := by positivity
  have hb0R : (b : ℝ) ≠ 0 := by positivity
  have hp0R : (p : ℝ) ≠ 0 := by positivity
  have hkey : (b : ℝ) * (r : ℝ) + (p : ℝ) * (v : ℝ) =
      (j : ℝ) * ((b : ℝ) * (p : ℝ)) + (a : ℝ) := by
    linarith [hcast]
  field_simp
  linarith [hkey]



private theorem gbe_dirichlet (θ : ℝ) (u w : ℕ) (huw : u ≤ w) :
    2 * Real.sin (θ / 2) * (∑ n ∈ Finset.Ioc u w, Real.cos ((n : ℝ) * θ)) =
      Real.sin (((w : ℝ) + 1 / 2) * θ) - Real.sin (((u : ℝ) + 1 / 2) * θ) := by
  induction w, huw using Nat.le_induction with
  | base => simp
  | succ w hw ih =>
    rw [Finset.sum_Ioc_succ_top hw, mul_add, ih]
    have e1 : (((w + 1 : ℕ) : ℝ)) * θ = ((w : ℝ) + 1 / 2) * θ + θ / 2 := by
      push_cast; ring
    have e2 : ((((w + 1 : ℕ) : ℝ)) + 1 / 2) * θ = ((w : ℝ) + 1 / 2) * θ + 2 * (θ / 2) := by
      push_cast; ring
    have key : Real.sin (((w : ℝ) + 1 / 2) * θ + 2 * (θ / 2)) - Real.sin (((w : ℝ) + 1 / 2) * θ) =
        2 * Real.sin (θ / 2) * Real.cos (((w : ℝ) + 1 / 2) * θ + θ / 2) := by
      rw [Real.sin_sub_sin]
      have a1 : (((w : ℝ) + 1 / 2) * θ + 2 * (θ / 2) - ((w : ℝ) + 1 / 2) * θ) / 2 = θ / 2 := by ring
      have a2 : (((w : ℝ) + 1 / 2) * θ + 2 * (θ / 2) + ((w : ℝ) + 1 / 2) * θ) / 2 =
          ((w : ℝ) + 1 / 2) * θ + θ / 2 := by ring
      rw [a1, a2]
    rw [e1, e2]
    linarith [key]

private theorem gbe_dirichlet_bound (θ : ℝ) (hs : Real.sin (θ / 2) ≠ 0) (u w : ℕ) :
    |∑ n ∈ Finset.Ioc u w, Real.cos ((n : ℝ) * θ)| ≤ 1 / |Real.sin (θ / 2)| := by
  have hpos : 0 < |Real.sin (θ / 2)| := abs_pos.mpr hs
  rw [le_div_iff₀ hpos]
  by_cases huw : u ≤ w
  · have h := gbe_dirichlet θ u w huw
    have h2 : |2 * Real.sin (θ / 2) * (∑ n ∈ Finset.Ioc u w, Real.cos ((n : ℝ) * θ))| ≤ 2 := by
      rw [h]
      have := Real.abs_sin_le_one (((w : ℝ) + 1 / 2) * θ)
      have := Real.abs_sin_le_one (((u : ℝ) + 1 / 2) * θ)
      calc _ ≤ |Real.sin (((w : ℝ) + 1 / 2) * θ)| + |Real.sin (((u : ℝ) + 1 / 2) * θ)| :=
            abs_sub _ _
        _ ≤ 2 := by linarith
    rw [abs_mul, abs_mul] at h2
    have : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
    rw [this] at h2
    nlinarith
  · have : Finset.Ioc u w = ∅ := by
      ext n; simp; omega
    rw [this]; simp

private theorem gbe_filter_shape (P : ℕ → Prop) [DecidablePred P] (hP : Monotone P) (u w : ℕ) :
    ∃ u' : ℕ, (Finset.Ioc u w).filter P = Finset.Ioc u' w := by
  by_cases hex : ((Finset.Ioc u w).filter P).Nonempty
  · set m := ((Finset.Ioc u w).filter P).min' hex with hm
    have hmem := Finset.min'_mem _ hex
    rw [← hm] at hmem
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hmem
    refine ⟨m - 1, ?_⟩
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have : m ≤ n := by
        rw [hm]; exact Finset.min'_le _ _ (by simp only [Finset.mem_filter, Finset.mem_Ioc]; exact ⟨⟨h1, h2⟩, h3⟩)
      omega
    · rintro ⟨h1, h2⟩
      exact ⟨⟨by omega, h2⟩, hP (show m ≤ n by omega) hmem.2⟩
  · refine ⟨w, ?_⟩
    rw [Finset.not_nonempty_iff_eq_empty] at hex
    rw [hex]; simp

private theorem gbe_core (m e x p a b r v k : ℕ) (hp : p.Prime) (h2 : 2 < p) (ha : 0 < a) (hab : a ≤ b)
    (hpab : p = a ^ 2 + b ^ 2) (hrp : r < p) (hvb : v < b) (h3 : (b * r) % p = a % p)
    (h4 : (a * v) % b = 1 % b) (hk : 0 < k) (hks : k ≤ Nat.sqrt p) :
    |(2 * Real.cos (2 * Real.pi * (k : ℝ) * (r : ℝ) / (p : ℝ)) -
        2 * Real.cos (2 * Real.pi * (k : ℝ) * (v : ℝ) / (b : ℝ))) *
      (∑ n ∈ (Finset.Ioc x (2 * x)).filter (fun n => p ^ m ≤ n ^ e),
        Real.cos (2 * Real.pi * (k : ℝ) * (n : ℝ) / (p : ℝ))) / (p : ℝ)| ≤
    2 * Real.pi / p := by
  have hkk : k * k ≤ p := Nat.le_sqrt.mp hks
  have h2k : 2 * k ≤ p := by
    rcases Nat.lt_or_ge k 2 with h | h
    · omega
    · nlinarith
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hb0R : (0 : ℝ) < b := by exact_mod_cast hb0
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h2kR : 2 * (k : ℝ) ≤ p := by exact_mod_cast h2k
  have hpi := Real.pi_pos
  obtain ⟨j, hj⟩ := gbe_recip a b p r v ha hab hp hpab hrp hvb h3 h4
  -- window sum bound
  obtain ⟨u', hu'⟩ := gbe_filter_shape (fun n => p ^ m ≤ n ^ e)
    (fun m n hmn => fun h => le_trans h (Nat.pow_le_pow_left hmn _)) x (2 * x)
  set θ : ℝ := 2 * Real.pi * (k : ℝ) / (p : ℝ) with hθ
  have hsin_arg : θ / 2 = Real.pi * k / p := by rw [hθ]; ring
  have hxle : Real.pi * k / p ≤ Real.pi / 2 := by
    rw [div_le_iff₀ hp0]; nlinarith
  have hxnn : 0 ≤ Real.pi * k / p := by positivity
  have hsinge : 2 / Real.pi * (Real.pi * k / p) ≤ Real.sin (Real.pi * k / p) :=
    Real.mul_le_sin hxnn hxle
  have hval : 2 / Real.pi * (Real.pi * k / p) = 2 * k / p := by field_simp
  rw [hval] at hsinge
  have hsinpos : 0 < Real.sin (θ / 2) := by
    rw [hsin_arg]
    exact lt_of_lt_of_le (by positivity) hsinge
  have hW : |∑ n ∈ (Finset.Ioc x (2 * x)).filter (fun n => p ^ m ≤ n ^ e),
        Real.cos (2 * Real.pi * (k : ℝ) * (n : ℝ) / (p : ℝ))| ≤ p / (2 * k) := by
    rw [hu']
    have := gbe_dirichlet_bound θ hsinpos.ne' u' (2 * x)
    have e : ∀ n : ℕ, Real.cos (2 * Real.pi * (k : ℝ) * (n : ℝ) / (p : ℝ)) =
        Real.cos ((n : ℝ) * θ) := by
      intro n; rw [hθ]; congr 1; ring
    simp only [e]
    refine this.trans ?_
    rw [abs_of_pos hsinpos, hsin_arg]
    have : 2 * (k : ℝ) / p ≤ Real.sin (Real.pi * k / p) := hsinge
    have hs' : 0 < Real.sin (Real.pi * k / p) := by rw [← hsin_arg]; exact hsinpos
    rw [div_le_div_iff₀ hs' (by positivity)]
    rw [div_le_iff₀ hp0] at this
    nlinarith
  -- root difference bound
  have hdiff : |2 * Real.cos (2 * Real.pi * (k : ℝ) * (r : ℝ) / (p : ℝ)) -
        2 * Real.cos (2 * Real.pi * (k : ℝ) * (v : ℝ) / (b : ℝ))| ≤ 4 * Real.pi * k / p := by
    have hr : (r : ℝ) / p = j - (v : ℝ) / b + (a : ℝ) / ((b : ℝ) * p) := by linarith
    have e1 : 2 * Real.pi * (k : ℝ) * (r : ℝ) / (p : ℝ) =
        (-(2 * Real.pi * (k : ℝ) * (v : ℝ) / (b : ℝ)) + 2 * Real.pi * (k : ℝ) * (a : ℝ) / ((b : ℝ) * p))
          + ((k * j : ℤ) : ℝ) * (2 * Real.pi) := by
      have : 2 * Real.pi * (k : ℝ) * (r : ℝ) / (p : ℝ) = 2 * Real.pi * k * ((r : ℝ) / p) := by ring
      rw [this, hr]
      push_cast
      field_simp
      ring
    rw [e1, Real.cos_add_int_mul_two_pi]
    set Z := 2 * Real.pi * (k : ℝ) * (v : ℝ) / (b : ℝ)
    set Wv := 2 * Real.pi * (k : ℝ) * (a : ℝ) / ((b : ℝ) * p)
    have hc : Real.cos (-Z + Wv) = Real.cos (Z - Wv) := by
      rw [← Real.cos_neg]; congr 1; ring
    rw [hc]
    have hl := Real.abs_cos_sub_cos_le (Z - Wv) Z
    have hWv : 0 ≤ Wv := by positivity
    have hWv2 : Wv ≤ 2 * Real.pi * k / p := by
      simp only [Wv]
      rw [div_le_div_iff₀ (by positivity) hp0]
      have : (a : ℝ) ≤ b := by exact_mod_cast hab
      have h5 : 0 ≤ 2 * Real.pi * (k : ℝ) * p := by positivity
      nlinarith
    have : |Z - Wv - Z| = Wv := by
      rw [show Z - Wv - Z = -Wv by ring, abs_neg, abs_of_nonneg hWv]
    rw [this] at hl
    have : 2 * Real.cos (Z - Wv) - 2 * Real.cos Z = 2 * (Real.cos (Z - Wv) - Real.cos Z) := by ring
    rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have : 4 * Real.pi * k / p = 2 * (2 * Real.pi * k / p) := by ring
    rw [this]
    linarith
  rw [abs_div, abs_mul, abs_of_pos hp0]
  apply div_le_div_of_nonneg_right _ hp0.le
  calc _ ≤ (4 * Real.pi * k / p) * (p / (2 * k)) := mul_le_mul hdiff hW (abs_nonneg _) (by positivity)
    _ = 2 * Real.pi := by field_simp; ring


private theorem gbe_inv_sqrt_sum (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, 1 / Real.sqrt (n : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hs : Real.sqrt ((N + 1 : ℕ) : ℝ) * Real.sqrt ((N + 1 : ℕ) : ℝ) = ((N + 1 : ℕ) : ℝ) :=
      Real.mul_self_sqrt (Nat.cast_nonneg _)
    have ht : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := Real.mul_self_sqrt hN
    have hspos : 0 < Real.sqrt ((N + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have htnn : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
    have key : 1 / Real.sqrt ((N + 1 : ℕ) : ℝ) ≤
        2 * Real.sqrt ((N + 1 : ℕ) : ℝ) - 2 * Real.sqrt (N : ℝ) := by
      rw [div_le_iff₀ hspos]
      push_cast at hs ⊢
      nlinarith [sq_nonneg (Real.sqrt ((N : ℝ) + 1) - Real.sqrt (N : ℝ))]
    linarith

private theorem gbe_card_low (p : ℕ) :
    ((Finset.Ico 1 p).filter (fun k => min k (p - k) ≤ Nat.sqrt p)).card ≤ 2 * Nat.sqrt p := by
  set s := Nat.sqrt p
  have hsub : (Finset.Ico 1 p).filter (fun k => min k (p - k) ≤ s) ⊆
      Finset.Icc 1 s ∪ (Finset.Icc 1 s).image (fun j => p - j) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Ico] at hk
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_image]
    obtain ⟨⟨h1, h2⟩, h3⟩ := hk
    rcases le_total k (p - k) with h | h
    · left; rw [min_eq_left h] at h3; exact ⟨h1, h3⟩
    · right; rw [min_eq_right h] at h3
      exact ⟨p - k, ⟨by omega, h3⟩, by omega⟩
  calc _ ≤ (Finset.Icc 1 s ∪ (Finset.Icc 1 s).image (fun j => p - j)).card := Finset.card_le_card hsub
    _ ≤ (Finset.Icc 1 s).card + ((Finset.Icc 1 s).image (fun j => p - j)).card := Finset.card_union_le _ _
    _ ≤ s + s := by
      have := Finset.card_image_le (s := Finset.Icc 1 s) (f := fun j => p - j)
      simp only [Nat.card_Icc] at *
      omega
    _ = 2 * s := by ring

private theorem gbe_pM_gen (x p m n : ℕ) (hm : 0 < m) (h : p ^ m ≤ (2 * x) ^ n) :
    (p : ℝ) ≤ (2 * (x : ℝ)) ^ ((n : ℝ) / m) := by
  by_contra hlt
  push Not at hlt
  have h0 : (0 : ℝ) ≤ 2 * (x : ℝ) := by positivity
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hM : ((2 * (x : ℝ)) ^ ((n : ℝ) / m)) ^ m = (2 * (x : ℝ)) ^ n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h0, ← Real.rpow_natCast]
    congr 1; field_simp
  have hpos : 0 ≤ (2 * (x : ℝ)) ^ ((n : ℝ) / m) := Real.rpow_nonneg h0 _
  have h1 : ((2 * (x : ℝ)) ^ ((n : ℝ) / m)) ^ m < (p : ℝ) ^ m :=
    pow_lt_pow_left₀ hlt hpos hm.ne'
  rw [hM] at h1
  have h2 : ((p ^ m : ℕ) : ℝ) ≤ (((2 * x) ^ n : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h2
  linarith

private theorem gbe_pM (x p : ℕ) (h : p ^ 100000 ≤ (2 * x) ^ 132301) :
    (p : ℝ) ≤ (2 * (x : ℝ)) ^ ((132301 : ℝ) / 100000) := by
  have := gbe_pM_gen x p 100000 132301 (by norm_num) h
  simpa using this

theorem Conjectures.QuadraticPrimes.GaussBandError :
    let block := fun x : ℕ => Finset.Ioc x (2*x); let window := fun x p : ℕ => (block x).filter (fun n => p^100000≤n^132301); let phase := fun p k (t : ℕ) => 2*Real.pi*(k : ℝ)*(t : ℝ)/(p : ℝ); let rootWave := fun q k t : ℕ => 2*Real.cos (phase q k t); let good := fun p a b r v : ℕ => p.Prime ∧ 2<p ∧ 0<a ∧ a≤b ∧ p=a^2+b^2 ∧ r<p ∧ v<b ∧ (b*r) % p=a % p ∧ (a*v) % b=1 % b; let low := fun p : ℕ => (Finset.Ico 1 p).filter (fun k => min k (p-k)≤Nat.sqrt p); let amp := fun x p q t : ℕ => (∑ k ∈ low p, rootWave q (min k (p-k)) t * (∑ n ∈ window x p, Real.cos (phase p (min k (p-k)) n)) / (p : ℝ)) * Real.log p; let split := fun x : ℕ => (Finset.Ioc x ((2*x)^2+1)).filter (fun p => p.Prime ∧ p % 4=1 ∧ p^100000≤(2*x)^132301); ∃ C : ℝ, 0<C ∧ ∀ x : ℕ, 4≤x → ∀ S : Finset ℕ, S⊆split x →
      ∀ a b r v : ℕ → ℕ, (∀ p ∈ S, good p (a p) (b p) (r p) (v p)) →
      |∑ p ∈ S, (amp x p p (r p) - amp x p (b p) (v p))| ≤
        C * (x : ℝ)^(132301/200000 : ℝ) * (Real.log (2*(x : ℝ)))^2 := by
  intro block window phase rootWave good low amp split
  refine ⟨32 * Real.pi, by positivity, ?_⟩
  intro x hx S hS a b r v hg
  have hpi := Real.pi_pos
  have hx0 : (0 : ℝ) < x := by
    have : (0 : ℕ) < x := by omega
    exact_mod_cast this
  have hA : ∀ p ∈ S, |amp x p p (r p) - amp x p (b p) (v p)| ≤
      Real.log p * (2 * Nat.sqrt p) * (2 * Real.pi / p) := by
    intro p hpS
    have hps := hS hpS
    simp only [split, Finset.mem_filter, Finset.mem_Ioc] at hps
    obtain ⟨hp, h2, ha, hab, hpab, hrp, hvb, h3, h4⟩ := hg p hpS
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have heq : amp x p p (r p) - amp x p (b p) (v p) =
        (∑ k ∈ low p, (rootWave p (min k (p - k)) (r p) - rootWave (b p) (min k (p - k)) (v p)) *
          (∑ n ∈ window x p, Real.cos (phase p (min k (p - k)) n)) / (p : ℝ)) * Real.log p := by
      simp only [amp]
      rw [← sub_mul, ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [heq, abs_mul, abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_le))]
    rw [mul_comm]
    have hsum : |∑ k ∈ low p, (rootWave p (min k (p - k)) (r p) - rootWave (b p) (min k (p - k)) (v p)) *
          (∑ n ∈ window x p, Real.cos (phase p (min k (p - k)) n)) / (p : ℝ)| ≤
        (2 * Nat.sqrt p) * (2 * Real.pi / p) := by
      calc _ ≤ ∑ k ∈ low p, |(rootWave p (min k (p - k)) (r p) - rootWave (b p) (min k (p - k)) (v p)) *
          (∑ n ∈ window x p, Real.cos (phase p (min k (p - k)) n)) / (p : ℝ)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ low p, 2 * Real.pi / p := by
          apply Finset.sum_le_sum
          intro k hk
          simp only [low, Finset.mem_filter, Finset.mem_Ico] at hk
          have hc := gbe_core 100000 132301 x p (a p) (b p) (r p) (v p) (min k (p - k)) hp h2 ha hab hpab hrp hvb h3 h4
            (lt_min hk.1.1 (Nat.sub_pos_of_lt hk.1.2)) hk.2
          have hmin : min (k : ℝ) ((p : ℝ) - k) = ((min k (p - k) : ℕ) : ℝ) := by
            rw [Nat.cast_min, Nat.cast_sub hk.1.2.le]
          simp only [rootWave, phase, window, block, hmin]
          exact hc
        _ = (low p).card * (2 * Real.pi / p) := by simp
        _ ≤ (2 * Nat.sqrt p) * (2 * Real.pi / p) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast gbe_card_low p
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
    calc _ ≤ Real.log p * ((2 * Nat.sqrt p) * (2 * Real.pi / p)) := mul_le_mul_of_nonneg_left hsum hl
      _ = _ := by ring
  set M : ℝ := (2 * (x : ℝ)) ^ ((132301 : ℝ) / 100000) with hM
  have h2x0 : (0 : ℝ) < 2 * x := by positivity
  have hL1 : 1 ≤ Real.log (2 * (x : ℝ)) := by
    rw [Real.le_log_iff_exp_le h2x0]
    have := Real.exp_one_lt_d9
    have : (4 : ℝ) ≤ x := by exact_mod_cast hx
    linarith
  have hlogM : Real.log M ≤ 2 * Real.log (2 * (x : ℝ)) := by
    rw [hM, Real.log_rpow h2x0]
    nlinarith
  have hMpos : 0 < M := Real.rpow_pos_of_pos h2x0 _
  have hpM : ∀ p ∈ S, (p : ℝ) ≤ M := by
    intro p hpS
    have hps := hS hpS
    simp only [split, Finset.mem_filter, Finset.mem_Ioc] at hps
    exact gbe_pM x p hps.2.2.2
  have hB : ∀ p ∈ S, |amp x p p (r p) - amp x p (b p) (v p)| ≤
      (Real.log M * (4 * Real.pi)) * (1 / Real.sqrt (p : ℝ)) := by
    intro p hpS
    refine (hA p hpS).trans ?_
    have hps := hS hpS
    simp only [split, Finset.mem_filter, Finset.mem_Ioc] at hps
    have hp1 : 1 ≤ p := hps.2.1.one_le
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hps.2.1.pos
    have hlog : Real.log p ≤ Real.log M := Real.log_le_log hp0 (hpM p hpS)
    have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp1)
    have hq : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp0
    have hqq : Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = p := Real.mul_self_sqrt hp0.le
    have hs : (Nat.sqrt p : ℝ) ≤ Real.sqrt p := Real.nat_sqrt_le_real_sqrt
    have hmid : (2 * (Nat.sqrt p : ℝ)) * (2 * Real.pi / p) ≤ 4 * Real.pi * (1 / Real.sqrt (p : ℝ)) := by
      set q := Real.sqrt (p : ℝ) with hqd
      rw [← hqq]
      have e : (2 * (Nat.sqrt p : ℝ)) * (2 * Real.pi / (q * q)) =
          (4 * Real.pi * (1 / q)) * ((Nat.sqrt p : ℝ) / q) := by
        field_simp; ring
      rw [e]
      apply mul_le_of_le_one_right (by positivity)
      exact (div_le_one hq).mpr hs
    calc Real.log p * (2 * Nat.sqrt p) * (2 * Real.pi / p)
        = Real.log p * ((2 * (Nat.sqrt p : ℝ)) * (2 * Real.pi / p)) := by ring
      _ ≤ Real.log M * (4 * Real.pi * (1 / Real.sqrt (p : ℝ))) :=
          mul_le_mul hlog hmid (by positivity) (hlog0.trans hlog)
      _ = _ := by ring
  have hN : S ⊆ Finset.Icc 1 ⌊M⌋₊ := by
    intro p hpS
    have hps := hS hpS
    simp only [split, Finset.mem_filter, Finset.mem_Ioc] at hps
    rw [Finset.mem_Icc]
    exact ⟨hps.2.1.one_le, Nat.le_floor (hpM p hpS)⟩
  have hsumS : ∑ p ∈ S, 1 / Real.sqrt (p : ℝ) ≤ 2 * Real.sqrt M := by
    calc _ ≤ ∑ p ∈ Finset.Icc 1 ⌊M⌋₊, 1 / Real.sqrt (p : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hN (fun _ _ _ => by positivity)
      _ ≤ 2 * Real.sqrt (⌊M⌋₊ : ℝ) := gbe_inv_sqrt_sum _
      _ ≤ 2 * Real.sqrt M := by
          gcongr
          exact Nat.floor_le hMpos.le
  have hsqM : Real.sqrt M ≤ 2 * (x : ℝ) ^ ((132301 : ℝ) / 200000) := by
    rw [Real.sqrt_eq_rpow, hM, ← Real.rpow_mul h2x0.le]
    have e : (132301 : ℝ) / 100000 * (1 / 2) = 132301 / 200000 := by norm_num
    rw [e, Real.mul_rpow (by norm_num) hx0.le]
    have : (2 : ℝ) ^ ((132301 : ℝ) / 200000) ≤ 2 := by
      calc (2 : ℝ) ^ ((132301 : ℝ) / 200000) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have h0 : 0 ≤ (x : ℝ) ^ ((132301 : ℝ) / 200000) := Real.rpow_nonneg hx0.le _
    nlinarith
  set E : ℝ := (x : ℝ) ^ ((132301 : ℝ) / 200000) with hE
  have hE0 : 0 ≤ E := Real.rpow_nonneg hx0.le _
  set L : ℝ := Real.log (2 * (x : ℝ)) with hL
  have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg (by
    have : (1 : ℝ) ≤ 2 * x := by have : (4 : ℝ) ≤ x := by exact_mod_cast hx
                                 linarith
    exact (Real.one_le_rpow this (by norm_num)))
  calc |∑ p ∈ S, (amp x p p (r p) - amp x p (b p) (v p))|
      ≤ ∑ p ∈ S, |amp x p p (r p) - amp x p (b p) (v p)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ S, (Real.log M * (4 * Real.pi)) * (1 / Real.sqrt (p : ℝ)) := Finset.sum_le_sum hB
    _ = (Real.log M * (4 * Real.pi)) * ∑ p ∈ S, 1 / Real.sqrt (p : ℝ) := by rw [Finset.mul_sum]
    _ ≤ (Real.log M * (4 * Real.pi)) * (2 * Real.sqrt M) :=
        mul_le_mul_of_nonneg_left hsumS (by positivity)
    _ ≤ (2 * L * (4 * Real.pi)) * (2 * (2 * E)) := by
        apply mul_le_mul _ _ (by positivity) (by positivity)
        · exact mul_le_mul_of_nonneg_right hlogM (by positivity)
        · linarith
    _ = 32 * Real.pi * E * L := by ring
    _ ≤ 32 * Real.pi * E * L ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith

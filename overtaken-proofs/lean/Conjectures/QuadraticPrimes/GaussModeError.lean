import Mathlib

private theorem gme_recip :
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



private theorem gme_dirichlet (θ : ℝ) (u w : ℕ) (huw : u ≤ w) :
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

private theorem gme_dirichlet_bound (θ : ℝ) (hs : Real.sin (θ / 2) ≠ 0) (u w : ℕ) :
    |∑ n ∈ Finset.Ioc u w, Real.cos ((n : ℝ) * θ)| ≤ 1 / |Real.sin (θ / 2)| := by
  have hpos : 0 < |Real.sin (θ / 2)| := abs_pos.mpr hs
  rw [le_div_iff₀ hpos]
  by_cases huw : u ≤ w
  · have h := gme_dirichlet θ u w huw
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

private theorem gme_filter_shape (P : ℕ → Prop) [DecidablePred P] (hP : Monotone P) (u w : ℕ) :
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

private theorem gme_core (x p a b r v k : ℕ) (hp : p.Prime) (h2 : 2 < p) (ha : 0 < a) (hab : a ≤ b)
    (hpab : p = a ^ 2 + b ^ 2) (hrp : r < p) (hvb : v < b) (h3 : (b * r) % p = a % p)
    (h4 : (a * v) % b = 1 % b) (hk : 0 < k) (hks : k ≤ Nat.sqrt p) :
    |(2 * Real.cos (2 * Real.pi * (k : ℝ) * (r : ℝ) / (p : ℝ)) -
        2 * Real.cos (2 * Real.pi * (k : ℝ) * (v : ℝ) / (b : ℝ))) *
      (∑ n ∈ (Finset.Ioc x (2 * x)).filter (fun n => p ^ 100000 ≤ n ^ 132301),
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
  obtain ⟨j, hj⟩ := gme_recip a b p r v ha hab hp hpab hrp hvb h3 h4
  -- window sum bound
  obtain ⟨u', hu'⟩ := gme_filter_shape (fun n => p ^ 100000 ≤ n ^ 132301)
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
  have hW : |∑ n ∈ (Finset.Ioc x (2 * x)).filter (fun n => p ^ 100000 ≤ n ^ 132301),
        Real.cos (2 * Real.pi * (k : ℝ) * (n : ℝ) / (p : ℝ))| ≤ p / (2 * k) := by
    rw [hu']
    have := gme_dirichlet_bound θ hsinpos.ne' u' (2 * x)
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

theorem Conjectures.QuadraticPrimes.GaussModeError :
    let block := fun x : ℕ => Finset.Ioc x (2*x); let window := fun x p : ℕ => (block x).filter (fun n => p^100000≤n^132301); let phase := fun p k (t : ℕ) => 2*Real.pi*(k : ℝ)*(t : ℝ)/(p : ℝ); let rootWave := fun q k t : ℕ => 2*Real.cos (phase q k t); let good := fun p a b r v : ℕ => p.Prime ∧ 2<p ∧ 0<a ∧ a≤b ∧ p=a^2+b^2 ∧ r<p ∧ v<b ∧ (b*r) % p=a % p ∧ (a*v) % b=1 % b; ∀ x p a b r v k : ℕ, good p a b r v → 0<k → k≤Nat.sqrt p →
      |(rootWave p k r - rootWave b k v) * (∑ n ∈ window x p, Real.cos (phase p k n)) / (p : ℝ)| ≤
      2*Real.pi/p := by
  intro block window phase rootWave good x p a b r v k hg hk hks
  obtain ⟨hp, h2, ha, hab, hpab, hrp, hvb, h3, h4⟩ := hg
  exact gme_core x p a b r v k hp h2 ha hab hpab hrp hvb h3 h4 hk hks

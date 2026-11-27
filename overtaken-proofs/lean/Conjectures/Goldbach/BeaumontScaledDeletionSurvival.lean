import Mathlib

namespace Conjectures.Goldbach.RobustInputs



/-!
The finite Goldbach Selberg sieve and smooth-number Euler product bounds below are adapted
from OpenAI, openai/math (Apache License 2.0), revision 3344da59991ed94f9ba711217b29c1d760badfa6.
https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/NumberTheory/EgyptianFractions
The modules are combined for verification with the pinned toolchain. The cutoff and denominator estimates are derived here.
-/

-- Upstream module OAI.NumberTheory.EgyptianFractions.SelbergOptimal

namespace OAI
noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius
open Finset ArithmeticFunction

namespace Problem337.SelbergOptimal

/-- Complementation turns a sum over multiples among divisors into a divisor sum. -/
theorem sum_multiples_complement (P l : ℕ) (hP : P ≠ 0) (hl : l ∣ P)
    (f : ℕ → ℝ) :
    (∑ d ∈ P.divisors, if l ∣ d then f (P / d) else 0) =
      ∑ d ∈ (P / l).divisors, f d := by
  calc
    _ = ∑ d ∈ P.divisors, if l ∣ P / d then f d else 0 := by
      rw [← Nat.sum_div_divisors P (fun d => if l ∣ d then f (P / d) else 0)]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hP]
    _ = ∑ d ∈ (P / l).divisors, f d := by
      rw [← Finset.sum_filter]
      congr 1
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hd, _⟩, hld⟩
        refine ⟨?_, Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) hl)
          (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP hl)))⟩
        apply (Nat.dvd_div_iff_mul_dvd hl).2
        rw [Nat.mul_comm]
        exact (Nat.dvd_div_iff_mul_dvd hd).1 hld
      · rintro ⟨hd, _⟩
        have hdP : d ∣ P := hd.trans (Nat.div_dvd_of_dvd hl)
        refine ⟨⟨hdP, hP⟩, ?_⟩
        apply (Nat.dvd_div_iff_mul_dvd hdP).2
        rw [Nat.mul_comm]
        exact (Nat.dvd_div_iff_mul_dvd hl).1 hd

/-- Inverse of the upper divisor-sum transform, expressed through ordinary
Möbius inversion after complementing divisors. -/
def upperInverse (P : ℕ) (y : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ x ∈ (P / d).divisorsAntidiagonal, (μ x.1 : ℝ) * y (P / x.2)

theorem sum_upperInverse (P l : ℕ) (hP : P ≠ 0) (hl : l ∣ P)
    (y : ℕ → ℝ) :
    (∑ d ∈ P.divisors, if l ∣ d then upperInverse P y d else 0) = y l := by
  let f : ℕ → ℝ := fun n =>
    ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℝ) * y (P / x.2)
  have hmob : ∀ n > 0, ∑ d ∈ n.divisors, f d = y (P / n) := by
    apply ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mpr
    intro n hn
    rfl
  change (∑ d ∈ P.divisors, if l ∣ d then f (P / d) else 0) = y l
  rw [sum_multiples_complement P l hP hl f]
  rw [hmob (P / l) (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) hl)
    (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP hl)))]
  rw [Nat.div_div_self hl hP]

theorem upperInverse_one (P : ℕ) (hP : P ≠ 0) (y : ℕ → ℝ) :
    upperInverse P y 1 = ∑ d ∈ P.divisors, (μ d : ℝ) * y d := by
  unfold upperInverse
  rw [Nat.div_one, Nat.sum_divisorsAntidiagonal (f := fun d e => (μ d : ℝ) * y (P / e))]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hP]

/-- The positive finite normalizing sum of the optimal Selberg weights. -/
def normalizer (s : BoundingSieve) (z : ℕ) : ℝ :=
  ∑ d ∈ s.prodPrimes.divisors, if d ≤ z then s.selbergTerms d else 0

theorem normalizer_pos (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    0 < normalizer s z := by
  apply Finset.sum_pos'
  · intro d hd
    split_ifs
    · exact (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hd)).le
    · exact le_rfl
  · refine ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, s.prodPrimes_ne_zero⟩, ?_⟩
    rw [ite_eq_left hz]
    exact s.selbergTerms_pos (one_dvd _)

/-- The diagonal coordinates attaining the constrained minimum. -/
def optimalDiagonal (s : BoundingSieve) (z d : ℕ) : ℝ :=
  if d ≤ z then (μ d : ℝ) * s.selbergTerms d / normalizer s z else 0

/-- Selberg weights obtained by upper Möbius inversion. -/
def optimalWeight (s : BoundingSieve) (z d : ℕ) : ℝ :=
  if d ∣ s.prodPrimes then
    upperInverse s.prodPrimes (optimalDiagonal s z) d / s.nu d else 0

theorem optimalWeight_transform (s : BoundingSieve) (z l : ℕ)
    (hl : l ∣ s.prodPrimes) :
    (∑ d ∈ s.prodPrimes.divisors,
      if l ∣ d then s.nu d * optimalWeight s z d else 0) =
      optimalDiagonal s z l := by
  calc
    _ = ∑ d ∈ s.prodPrimes.divisors,
        if l ∣ d then upperInverse s.prodPrimes (optimalDiagonal s z) d else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdP := Nat.dvd_of_mem_divisors hd
      rw [optimalWeight, ite_eq_left hdP]
      have hnu := s.nu_ne_zero hdP
      congr 1
      field_simp
    _ = _ := sum_upperInverse _ _ s.prodPrimes_ne_zero hl _

theorem optimalWeight_one (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    optimalWeight s z 1 = 1 := by
  rw [optimalWeight, ite_eq_left (one_dvd _), s.nu_mult.map_one, div_one,
    upperInverse_one _ s.prodPrimes_ne_zero]
  have hG : normalizer s z ≠ 0 := (normalizer_pos s hz).ne'
  calc
    _ = (∑ d ∈ s.prodPrimes.divisors,
        if d ≤ z then s.selbergTerms d else 0) / normalizer s z := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d hd
      have hmu : (μ d : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
          (s.squarefree_of_mem_divisors_prodPrimes hd)
      unfold optimalDiagonal
      split_ifs with he
      · rw [mul_div_assoc, ← mul_assoc, ← pow_two, hmu, one_mul]
      · simp
    _ = 1 := div_self hG

/-- The diagonalized main term at the optimal weights is exactly the
reciprocal of the finite Selberg normalizer. -/
theorem mainSum_optimalWeight (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    s.mainSum (BoundingSieve.lambdaSquared (optimalWeight s z)) =
      1 / normalizer s z := by
  rw [s.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  have hG : normalizer s z ≠ 0 := (normalizer_pos s hz).ne'
  calc
    _ = (∑ d ∈ s.prodPrimes.divisors,
        if d ≤ z then s.selbergTerms d else 0) / normalizer s z ^ 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d hd
      have hdP := Nat.dvd_of_mem_divisors hd
      have hg : s.selbergTerms d ≠ 0 := (s.selbergTerms_pos hdP).ne'
      have hmu : (μ d : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
          (s.squarefree_of_mem_divisors_prodPrimes hd)
      rw [optimalWeight_transform s z d hdP]
      unfold optimalDiagonal
      split_ifs with he
      · rw [div_pow, mul_pow, hmu, one_mul]
        field_simp
      · simp
    _ = 1 / normalizer s z := by
      change normalizer s z / normalizer s z ^ 2 = _
      field_simp

/-- The Selberg upper-bound sieve with its main term optimized. -/
theorem siftedSum_le (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    s.siftedSum ≤ s.totalMass / normalizer s z +
      s.errSum (BoundingSieve.lambdaSquared (optimalWeight s z)) := by
  have h := s.siftedSum_le_mainSum_errSum_of_upperMoebius
    (BoundingSieve.lambdaSquared (optimalWeight s z))
    (BoundingSieve.upperMoebius_lambdaSquared _ (optimalWeight_one s hz))
  rw [mainSum_optimalWeight s hz, mul_one_div] at h
  exact h

/-- No optimal weight lies above the chosen truncation. -/
theorem optimalWeight_eq_zero_of_lt (s : BoundingSieve) {z d : ℕ} (hzd : z < d) :
    optimalWeight s z d = 0 := by
  unfold optimalWeight
  split_ifs with hdP
  · suffices upperInverse s.prodPrimes (optimalDiagonal s z) d = 0 by rw [this, zero_div]
    unfold upperInverse
    apply Finset.sum_eq_zero
    intro x hx
    have hx2 : x.2 ∣ s.prodPrimes / d :=
      Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)
    have hxP : x.2 ∣ s.prodPrimes := hx2.trans (Nat.div_dvd_of_dvd hdP)
    have hdx : d ∣ s.prodPrimes / x.2 := by
      apply (Nat.dvd_div_iff_mul_dvd hxP).2
      rw [Nat.mul_comm]
      exact (Nat.dvd_div_iff_mul_dvd hdP).1 hx2
    have hpos : 0 < s.prodPrimes / x.2 :=
      Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero s.prodPrimes_ne_zero) hxP)
        (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hxP))
    have hlong : z < s.prodPrimes / x.2 := hzd.trans_le (Nat.le_of_dvd hpos hdx)
    simp [optimalDiagonal, not_le.mpr hlong]
  · rfl

/-- Upper Möbius inversion does not increase the crude full-divisor
absolute-mass bound. This estimate is independent of squarefreeness. -/
theorem abs_upperInverse_le (P d : ℕ) (hP : P ≠ 0) (hd : d ∣ P)
    (y : ℕ → ℝ) :
    |upperInverse P y d| ≤ ∑ e ∈ P.divisors, |y e| := by
  unfold upperInverse
  rw [Nat.sum_divisorsAntidiagonal' (f := fun a b => (μ a : ℝ) * y (P / b))]
  calc
    _ ≤ ∑ e ∈ (P / d).divisors, |(μ ((P / d) / e) : ℝ) * y (P / e)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ (P / d).divisors, |y (P / e)| := by
      apply Finset.sum_le_sum
      intro e he
      have hmu : |(μ ((P / d) / e) : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := (P / d) / e)
      rw [abs_mul]
      simpa using mul_le_mul_of_nonneg_right hmu (abs_nonneg (y (P / e)))
    _ ≤ ∑ e ∈ P.divisors, |y (P / e)| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he
        exact Nat.mem_divisors.mpr
          ⟨(Nat.dvd_of_mem_divisors he).trans (Nat.div_dvd_of_dvd hd), hP⟩
      · intro e he hnot
        exact abs_nonneg _
    _ = _ := Nat.sum_div_divisors P (fun e => |y e|)

/-- The optimal diagonal coordinates have total absolute mass one. -/
theorem sum_abs_optimalDiagonal (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    (∑ d ∈ s.prodPrimes.divisors, |optimalDiagonal s z d|) = 1 := by
  have hG := normalizer_pos s hz
  calc
    _ = (∑ d ∈ s.prodPrimes.divisors,
        if d ≤ z then s.selbergTerms d else 0) / normalizer s z := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d hd
      have hg := s.selbergTerms_pos (Nat.dvd_of_mem_divisors hd)
      have hmu : |(μ d : ℝ)| = 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree
          (s.squarefree_of_mem_divisors_prodPrimes hd)
      unfold optimalDiagonal
      split_ifs
      · rw [abs_div, abs_mul, hmu, abs_of_pos hg, abs_of_pos hG, one_mul]
      · simp
    _ = 1 := div_self hG.ne'

/-- A coefficient bound adequate for polynomial-error applications of the sieve. -/
theorem abs_optimalWeight_le (s : BoundingSieve) {z d : ℕ} (hz : 1 ≤ z)
    (hd : d ∣ s.prodPrimes) :
    |optimalWeight s z d| ≤ (s.nu d)⁻¹ := by
  rw [optimalWeight, ite_eq_left hd, abs_div, abs_of_pos (s.nu_pos_of_dvd_prodPrimes hd)]
  have h := abs_upperInverse_le s.prodPrimes d s.prodPrimes_ne_zero hd
    (optimalDiagonal s z)
  rw [sum_abs_optimalDiagonal s hz] at h
  simpa only [one_div] using div_le_div_of_nonneg_right h
    (s.nu_pos_of_dvd_prodPrimes hd).le

/-- The upper inverse in the more usual sum-over-multiples form. -/
theorem upperInverse_eq_sum_multiples (P d : ℕ) (hP : P ≠ 0) (hd : d ∣ P)
    (y : ℕ → ℝ) :
    upperInverse P y d =
      ∑ e ∈ P.divisors, if d ∣ e then (μ (e / d) : ℝ) * y e else 0 := by
  unfold upperInverse
  rw [Nat.sum_divisorsAntidiagonal' (f := fun a b => (μ a : ℝ) * y (P / b)),
    ← sum_multiples_complement P d hP hd
      (fun e => (μ ((P / d) / e) : ℝ) * y (P / e))]
  apply Finset.sum_congr rfl
  intro e he
  have heP := Nat.dvd_of_mem_divisors he
  rw [Nat.div_div_self heP hP]
  split_ifs with hde
  · have hPe : 0 < P / e := Nat.div_pos
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) heP)
      (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP heP))
    have hquot : (P / d) / (P / e) = e / d := by
      rw [← Nat.div_mul_div heP hde, Nat.mul_comm, Nat.mul_div_cancel _ hPe]
    rw [hquot]
  · rfl

/-- Divisor multiples are parametrized by the complementary quotient. -/
theorem sum_multiples_eq (P d : ℕ) (hP : P ≠ 0) (hd : d ∣ P)
    (f : ℕ → ℝ) :
    (∑ e ∈ P.divisors, if d ∣ e then f e else 0) =
      ∑ t ∈ (P / d).divisors, f (d * t) := by
  calc
    _ = ∑ e ∈ P.divisors, if d ∣ e then f (P / (P / e)) else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      rw [Nat.div_div_self (Nat.dvd_of_mem_divisors he) hP]
    _ = ∑ t ∈ (P / d).divisors, f (P / t) :=
      sum_multiples_complement P d hP hd (fun t => f (P / t))
    _ = ∑ t ∈ (P / d).divisors, f (d * t) := by
      rw [← Nat.sum_div_divisors (P / d) (fun t => f (P / t))]
      apply Finset.sum_congr rfl
      intro t ht
      have htQ := Nat.dvd_of_mem_divisors ht
      have hQpos : 0 < P / d := Nat.div_pos
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) hd)
        (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP hd))
      have hQt : 0 < (P / d) / t := Nat.div_pos (Nat.le_of_dvd hQpos htQ)
        (Nat.pos_of_mem_divisors ht)
      have hprod : ((P / d) / t) * (d * t) = P := by
        calc
          _ = d * (((P / d) / t) * t) := by ring
          _ = d * (P / d) := by rw [Nat.div_mul_cancel htQ]
          _ = P := Nat.mul_div_cancel' hd
      congr 1
      conv_lhs => arg 1; rw [← hprod]
      exact Nat.mul_div_cancel_left (d * t) hQt

/-- The two Möbius signs from upper inversion collapse on squarefree divisors. -/
theorem moebius_div_mul (e d : ℕ) (he : Squarefree e) (hd : d ∣ e) :
    (μ (e / d) : ℝ) * (μ e : ℝ) = (μ d : ℝ) := by
  have hm : d * (e / d) = e := Nat.mul_div_cancel' hd
  have hcop : d.Coprime (e / d) := Nat.coprime_of_squarefree_mul (hm.symm ▸ he)
  have hmu := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
  rw [hm] at hmu
  have heq : (μ e : ℝ) = (μ d : ℝ) * (μ (e / d) : ℝ) := by exact_mod_cast hmu
  have hsquare : (μ (e / d) : ℝ) ^ 2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
      (he.squarefree_of_dvd (Nat.div_dvd_of_dvd hd))
  rw [heq]
  calc
    _ = (μ d : ℝ) * (μ (e / d) : ℝ) ^ 2 := by ring
    _ = _ := by rw [hsquare, mul_one]

/-- The truncated normalizer on complementary divisors. -/
def complementNormalizer (s : BoundingSieve) (z d : ℕ) : ℝ :=
  ∑ t ∈ (s.prodPrimes / d).divisors, if t ≤ z / d then s.selbergTerms t else 0

/-- Explicit classical formula for the optimal coefficient. In particular,
the sign is the Möbius sign and the remaining factors are nonnegative. -/
theorem optimalWeight_formula (s : BoundingSieve) (z d : ℕ)
    (hd : d ∣ s.prodPrimes) :
    optimalWeight s z d = (μ d : ℝ) * s.selbergTerms d / s.nu d *
      (complementNormalizer s z d / normalizer s z) := by
  rw [optimalWeight, ite_eq_left hd,
    upperInverse_eq_sum_multiples _ _ s.prodPrimes_ne_zero hd]
  have hdpos : 0 < d := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hd)
  have hsum :
      (∑ e ∈ s.prodPrimes.divisors,
        if d ∣ e then (μ (e / d) : ℝ) * optimalDiagonal s z e else 0) =
      (μ d : ℝ) / normalizer s z *
        (s.selbergTerms d * complementNormalizer s z d) := by
    calc
      _ = (μ d : ℝ) / normalizer s z *
          (∑ e ∈ s.prodPrimes.divisors,
            if d ∣ e then (if e ≤ z then s.selbergTerms e else 0) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        by_cases hde : d ∣ e
        · rw [ite_eq_left hde, ite_eq_left hde]
          unfold optimalDiagonal
          split_ifs with hez
          · rw [mul_div_assoc, ← mul_assoc,
              moebius_div_mul e d (s.squarefree_of_mem_divisors_prodPrimes he) hde]
            ring
          · simp
        · simp [hde]
      _ = (μ d : ℝ) / normalizer s z *
          (∑ t ∈ (s.prodPrimes / d).divisors,
            if d * t ≤ z then s.selbergTerms (d * t) else 0) := by
        rw [sum_multiples_eq _ _ s.prodPrimes_ne_zero hd]
      _ = _ := by
        congr 1
        unfold complementNormalizer
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        have htQ := Nat.dvd_of_mem_divisors ht
        have hdt : d * t ∣ s.prodPrimes := by
          simpa [Nat.mul_comm] using (Nat.dvd_div_iff_mul_dvd hd).1 htQ
        have hcop : d.Coprime t := Nat.coprime_of_squarefree_mul
          (s.squarefree_of_dvd_prodPrimes hdt)
        have hiff : d * t ≤ z ↔ t ≤ z / d := by
          rw [Nat.le_div_iff_mul_le hdpos, Nat.mul_comm]
        simp only [hiff]
        split_ifs
        · exact s.selbergTerms_isMultiplicative.map_mul_of_coprime hcop
        · simp
  rw [hsum]
  ring

end Problem337.SelbergOptimal

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.SelbergWeightBound

namespace OAI
noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius
open Finset

namespace Problem337.SelbergOptimal

/-- Summation over the divisors of a coprime product has no multiplicities. -/
theorem sum_coprime_divisors {a b : ℕ} (hab : a.Coprime b) (f : ℕ → ℝ) :
    (∑ d ∈ (a * b).divisors, f d) =
      ∑ e ∈ a.divisors, ∑ t ∈ b.divisors, f (e * t) := by
  rw [hab.divisors_mul]
  simp only [sum_map]
  exact (sum_attach (a.divisors ×ˢ b.divisors)
    (fun p : ℕ × ℕ => f (p.1 * p.2))).trans (sum_product _ _ _)

/-- The complementary divisor of a squarefree integer is coprime to it. -/
theorem coprime_complement (s : BoundingSieve) {d : ℕ} (hd : d ∣ s.prodPrimes) :
    d.Coprime (s.prodPrimes / d) := by
  apply Nat.coprime_of_squarefree_mul
  simpa only [Nat.mul_div_cancel' hd] using s.prodPrimes_squarefree

/-- Split the finite Selberg normalizer at a divisor of the sieving product. -/
theorem normalizer_decompose (s : BoundingSieve) (z : ℕ) {d : ℕ}
    (hd : d ∣ s.prodPrimes) :
    normalizer s z =
      ∑ e ∈ d.divisors, ∑ t ∈ (s.prodPrimes / d).divisors,
        if e * t ≤ z then s.selbergTerms e * s.selbergTerms t else 0 := by
  have hcop := coprime_complement s hd
  unfold normalizer
  conv_lhs => rw [← Nat.mul_div_cancel' hd]
  rw [sum_coprime_divisors hcop]
  apply sum_congr rfl
  intro e he
  apply sum_congr rfl
  intro t ht
  rw [s.selbergTerms_isMultiplicative.map_mul_of_coprime
    (hcop.coprime_dvd_left (Nat.dvd_of_mem_divisors he) |>.coprime_dvd_right
      (Nat.dvd_of_mem_divisors ht))]

theorem sum_selbergTerms_divisors (s : BoundingSieve) {d : ℕ}
    (hd : d ∣ s.prodPrimes) :
    (∑ e ∈ d.divisors, s.selbergTerms e) = s.selbergTerms d / s.nu d := by
  have h := s.sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv hd
  rw [← sum_filter, Nat.divisors_filter_dvd_of_dvd s.prodPrimes_ne_zero hd] at h
  simpa only [div_eq_mul_inv] using h

/-- The positive numerator of an optimal Selberg weight is a subsum of the
normalizer, after splitting into complementary divisor coordinates. -/
theorem truncated_complement_sum_le_normalizer (s : BoundingSieve) (z : ℕ)
    {d : ℕ} (hd : d ∣ s.prodPrimes) :
    (s.selbergTerms d / s.nu d) *
        (∑ t ∈ (s.prodPrimes / d).divisors,
          if d * t ≤ z then s.selbergTerms t else 0) ≤ normalizer s z := by
  rw [← sum_selbergTerms_divisors s hd, sum_mul,
    normalizer_decompose s z hd]
  apply sum_le_sum
  intro e he
  rw [mul_sum]
  apply sum_le_sum
  intro t ht
  have heP := (Nat.dvd_of_mem_divisors he).trans hd
  have htP := (Nat.dvd_of_mem_divisors ht).trans (Nat.div_dvd_of_dvd hd)
  have he0 := (s.selbergTerms_pos heP).le
  have ht0 := (s.selbergTerms_pos htP).le
  by_cases hdt : d * t ≤ z
  · have het : e * t ≤ z :=
      (Nat.mul_le_mul_right t (Nat.le_of_dvd
        (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hd))
        (Nat.dvd_of_mem_divisors he))).trans hdt
    simp only [ite_eq_left hdt, ite_eq_left het, le_refl]
  · simp only [ite_eq_right hdt, mul_zero]
    split_ifs <;> positivity

/-- The same bound in the quotient-cutoff form used in the explicit weights. -/
theorem truncated_div_sum_le_normalizer (s : BoundingSieve) (z : ℕ)
    {d : ℕ} (hd : d ∣ s.prodPrimes) :
    (s.selbergTerms d / s.nu d) *
        (∑ t ∈ (s.prodPrimes / d).divisors,
          if t ≤ z / d then s.selbergTerms t else 0) ≤ normalizer s z := by
  have hd0 : 0 < d :=
    Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hd)
  simpa only [Nat.le_div_iff_mul_le hd0, Nat.mul_comm] using
    truncated_complement_sum_le_normalizer s z hd

/-- The normalized explicit optimal-weight expression has absolute value at
most one. This bound is independent of the local sieve dimension. -/
theorem abs_normalized_complement_le_one (s : BoundingSieve) {z : ℕ}
    (hz : 1 ≤ z) {d : ℕ} (hd : d ∣ s.prodPrimes) :
    |(μ d : ℝ) * (s.selbergTerms d / s.nu d) /
        normalizer s z *
        (∑ t ∈ (s.prodPrimes / d).divisors,
          if t ≤ z / d then s.selbergTerms t else 0)| ≤ 1 := by
  have hG := normalizer_pos s hz
  have hnu := s.nu_pos_of_dvd_prodPrimes hd
  have hg := s.selbergTerms_pos hd
  have hsum : 0 ≤ ∑ t ∈ (s.prodPrimes / d).divisors,
      if t ≤ z / d then s.selbergTerms t else 0 := by
    apply sum_nonneg
    intro t ht
    split_ifs
    · exact (s.selbergTerms_pos ((Nat.dvd_of_mem_divisors ht).trans
        (Nat.div_dvd_of_dvd hd))).le
    · exact le_rfl
  have hmu : |(μ d : ℝ)| = 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree
      (s.squarefree_of_dvd_prodPrimes hd)
  rw [abs_mul, abs_div, abs_mul, hmu, one_mul,
    abs_of_pos (div_pos hg hnu), abs_of_pos hG, abs_of_nonneg hsum]
  rw [div_mul_eq_mul_div, div_le_one hG]
  exact truncated_div_sum_le_normalizer s z hd

end Problem337.SelbergOptimal

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.SelbergErrorBound

namespace OAI
/-!
# Remainder control for the Selberg square sieve

The estimates here retain the actual local remainder.  In particular no
prime distribution hypothesis is manufactured by passing to square weights.
-/

noncomputable section

open scoped BigOperators
open Finset

namespace Problem337.SelbergError

/-- A weighted version of the divisor expansion of the square sieve. -/
theorem sum_lambdaSquared_mul (P : ℕ) (hP : P ≠ 0)
    (lam f : ℕ → ℝ) :
    (∑ d ∈ P.divisors, BoundingSieve.lambdaSquared lam d * f d) =
      ∑ a ∈ P.divisors, ∑ b ∈ P.divisors,
        lam a * lam b * f (Nat.lcm a b) := by
  have henlarge (g : ℕ → ℕ → ℕ → ℝ) :
      (∑ d ∈ P.divisors, ∑ a ∈ d.divisors, ∑ b ∈ d.divisors,
        if d = Nat.lcm a b then g a b d else 0) =
      ∑ d ∈ P.divisors, ∑ a ∈ P.divisors, ∑ b ∈ P.divisors,
        if d = Nat.lcm a b then g a b d else 0 := by
    congr! 1 with d hd
    rw [Nat.mem_divisors] at hd
    have heq : ∀ a b, (a ∣ d ∧ b ∣ d ∧ d = Nat.lcm a b) =
        (d = Nat.lcm a b) := by
      simp +contextual [← and_assoc, Nat.dvd_lcm_left, Nat.dvd_lcm_right]
    simp_rw [← Nat.divisors_filter_dvd_of_dvd hd.2 hd.1,
      sum_filter, ite_sum_zero, ← ite_and, heq]
  calc
    _ = ∑ d ∈ P.divisors, ∑ a ∈ d.divisors, ∑ b ∈ d.divisors,
        if d = Nat.lcm a b then lam a * lam b * f d else 0 := by
      simp [BoundingSieve.lambdaSquared, sum_mul]
    _ = ∑ d ∈ P.divisors, ∑ a ∈ P.divisors, ∑ b ∈ P.divisors,
        if d = Nat.lcm a b then lam a * lam b * f d else 0 := henlarge _
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro a ha
      rw [sum_comm]
      apply sum_congr rfl
      intro b hb
      have hlcm : Nat.lcm a b ∈ P.divisors :=
        Nat.mem_divisors.mpr ⟨Nat.lcm_dvd_iff.mpr
          ⟨Nat.dvd_of_mem_divisors ha, Nat.dvd_of_mem_divisors hb⟩, hP⟩
      rw [sum_ite_eq_of_mem' _ _ _ hlcm]

/-- Absolute square weights are dominated by the square weights of absolute
values.  This inequality does not assume that the original weights are positive. -/
theorem abs_lambdaSquared_le (lam : ℕ → ℝ) (d : ℕ) :
    |BoundingSieve.lambdaSquared lam d| ≤
      BoundingSieve.lambdaSquared (fun n => |lam n|) d := by
  unfold BoundingSieve.lambdaSquared
  calc
    _ ≤ ∑ a ∈ d.divisors, |∑ b ∈ d.divisors,
        if d = Nat.lcm a b then lam a * lam b else 0| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ d.divisors, ∑ b ∈ d.divisors,
        |if d = Nat.lcm a b then lam a * lam b else 0| := by
      apply sum_le_sum
      intro a ha
      exact abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_ite, abs_mul, abs_zero]

/-- Exact local remainders can be bounded before any uniform estimate is made. -/
theorem errSum_lambdaSquared_le (s : BoundingSieve) (lam : ℕ → ℝ) :
    s.errSum (BoundingSieve.lambdaSquared lam) ≤
      ∑ a ∈ s.prodPrimes.divisors, ∑ b ∈ s.prodPrimes.divisors,
        |lam a| * |lam b| * |s.rem (Nat.lcm a b)| := by
  calc
    _ ≤ ∑ d ∈ s.prodPrimes.divisors,
        BoundingSieve.lambdaSquared (fun n => |lam n|) d * |s.rem d| := by
      apply sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_right (abs_lambdaSquared_le lam d) (abs_nonneg _)
    _ = _ := sum_lambdaSquared_mul s.prodPrimes
      BoundingSieve.prodPrimes_ne_zero _ _

/-- A factorizable local remainder envelope gives the usual weighted L1-square
bound for the square-sieve error. -/
theorem errSum_lambdaSquared_le_sq (s : BoundingSieve) (lam w : ℕ → ℝ)
    (hrem : ∀ a ∈ s.prodPrimes.divisors, ∀ b ∈ s.prodPrimes.divisors,
      |s.rem (Nat.lcm a b)| ≤ w a * w b) :
    s.errSum (BoundingSieve.lambdaSquared lam) ≤
      (∑ d ∈ s.prodPrimes.divisors, |lam d| * w d) ^ 2 := by
  calc
    _ ≤ ∑ a ∈ s.prodPrimes.divisors, ∑ b ∈ s.prodPrimes.divisors,
        |lam a| * |lam b| * |s.rem (Nat.lcm a b)| := errSum_lambdaSquared_le s lam
    _ ≤ ∑ a ∈ s.prodPrimes.divisors, ∑ b ∈ s.prodPrimes.divisors,
        |lam a| * |lam b| * (w a * w b) := by
      apply sum_le_sum
      intro a ha
      apply sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (hrem a ha b hb) (by positivity)
    _ = _ := by
      rw [sq, sum_mul_sum]
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro b hb
      ring

end Problem337.SelbergError

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.DivisorTupleBounds

namespace OAI
/-!
# Elementary summatory bounds for divisor tuples

These finite hyperbola estimates supply logarithmic remainder bounds for
square sieves.  They do not use a prime number theorem.
-/
noncomputable section
open scoped BigOperators
open Finset

namespace Problem337.SelbergError

/-- Ordered positive factor tuples, expressed by Dirichlet powers of zeta. -/
def divisorTupleCount (k n : ℕ) : ℕ :=
  (ArithmeticFunction.zeta ^ k) n

private lemma sum_divisorsAntidiagonal_le_rectangle (N : ℕ)
    (F : ℕ × ℕ → ℝ) (hF : ∀ x, 0 ≤ F x) :
    (∑ n ∈ Icc 1 N, ∑ x ∈ n.divisorsAntidiagonal, F x) ≤
      ∑ x ∈ Icc 1 N ×ˢ Icc 1 N, F x := by
  have hdisj : Set.PairwiseDisjoint (Icc 1 N : Finset ℕ)
      Nat.divisorsAntidiagonal := by
    intro n hn m hm hnm
    apply disjoint_left.mpr
    intro x hxn hxm
    exact hnm ((Nat.mem_divisorsAntidiagonal.mp hxn).1.symm.trans
      (Nat.mem_divisorsAntidiagonal.mp hxm).1)
  rw [← sum_biUnion hdisj]
  apply sum_le_sum_of_subset_of_nonneg
  · intro x hx
    obtain ⟨n, hn, hxn⟩ := mem_biUnion.mp hx
    obtain ⟨hprod, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hxn
    have ha : 0 < x.1 := by
      by_contra h
      have : x.1 = 0 := by omega
      simp [this] at hprod
      omega
    have hb : 0 < x.2 := by
      by_contra h
      have : x.2 = 0 := by omega
      simp [this] at hprod
      omega
    have haN : x.1 ≤ N := (Nat.le_of_dvd (by omega : 0 < n)
      ⟨x.2, hprod.symm⟩).trans (mem_Icc.mp hn).2
    have hbN : x.2 ≤ N := (Nat.le_of_dvd (by omega : 0 < n)
      ⟨x.1, by simpa [Nat.mul_comm] using hprod.symm⟩).trans (mem_Icc.mp hn).2
    exact mem_product.mpr ⟨mem_Icc.mpr ⟨ha, haN⟩, mem_Icc.mpr ⟨hb, hbN⟩⟩
  · intro x hx hxnot
    exact hF x

/-- The harmonic norm on an initial interval is submultiplicative for
Dirichlet convolution of nonnegative arithmetic functions. -/
theorem harmonic_convolution_le (f g : ArithmeticFunction ℕ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ((f * g) n : ℝ) / n) ≤
      (∑ a ∈ Icc 1 N, (f a : ℝ) / a) *
      (∑ b ∈ Icc 1 N, (g b : ℝ) / b) := by
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ x ∈ n.divisorsAntidiagonal,
        ((f x.1 : ℝ) / x.1) * ((g x.2 : ℝ) / x.2) := by
      apply sum_congr rfl
      intro n hn
      rw [ArithmeticFunction.mul_apply, Nat.cast_sum, sum_div]
      apply sum_congr rfl
      intro x hx
      have hp := (Nat.mem_divisorsAntidiagonal.mp hx).1
      rw [Nat.cast_mul, ← hp, Nat.cast_mul]
      ring
    _ ≤ ∑ x ∈ Icc 1 N ×ˢ Icc 1 N,
        ((f x.1 : ℝ) / x.1) * ((g x.2 : ℝ) / x.2) :=
      sum_divisorsAntidiagonal_le_rectangle N _ (by intro x; positivity)
    _ = _ := by rw [sum_product, sum_mul_sum]

lemma zeta_harmonic_sum (N : ℕ) :
    (∑ n ∈ Icc 1 N, (ArithmeticFunction.zeta n : ℝ) / n) =
      (harmonic N : ℝ) := by
  rw [harmonic_eq_sum_Icc, Rat.cast_sum]
  apply sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
  simp [ArithmeticFunction.zeta_apply_ne hn0]

/-- The harmonic sum over ordered `k`-factor tuples has at most the expected
`k` logarithmic factors. -/
theorem divisorTuple_harmonic_le (k N : ℕ) :
    (∑ n ∈ Icc 1 N, (divisorTupleCount k n : ℝ) / n) ≤
      (harmonic N : ℝ) ^ k := by
  induction k with
  | zero =>
    simp only [divisorTupleCount, pow_zero, ArithmeticFunction.one_apply]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_div, zero_div]
    by_cases hN : 1 ≤ N
    · simp [hN]
    · have : N = 0 := by omega
      simp [this]
  | succ k ih =>
    have h := harmonic_convolution_le (ArithmeticFunction.zeta ^ k)
      ArithmeticFunction.zeta N
    rw [zeta_harmonic_sum] at h
    calc
      _ ≤ (∑ n ∈ Icc 1 N, (divisorTupleCount k n : ℝ) / n) *
          (harmonic N : ℝ) := by simpa [divisorTupleCount, pow_succ] using h
      _ ≤ (harmonic N : ℝ) ^ k * (harmonic N : ℝ) :=
        mul_le_mul_of_nonneg_right ih (by rw [harmonic, Rat.cast_sum]; positivity)
      _ = _ := (pow_succ _ _).symm

/-- A uniform summatory bound, with one harmless extra logarithmic factor.
It holds also at `N = 0` and requires no squarefreeness restriction. -/
theorem divisorTuple_sum_le (k N : ℕ) :
    (∑ n ∈ Icc 1 N, (divisorTupleCount k n : ℝ)) ≤
      (N : ℝ) * (harmonic N : ℝ) ^ k := by
  calc
    _ ≤ ∑ n ∈ Icc 1 N, (N : ℝ) * ((divisorTupleCount k n : ℝ) / n) := by
      apply sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
      rw [← mul_div_assoc, le_div_iff₀ hn0]
      nlinarith [show (0 : ℝ) ≤ divisorTupleCount k n by positivity]
    _ = (N : ℝ) * ∑ n ∈ Icc 1 N, (divisorTupleCount k n : ℝ) / n :=
      (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (divisorTuple_harmonic_le k N) (by positivity)

/-- At a prime, there are exactly `k` ordered `k`-factor tuples. -/
theorem divisorTupleCount_prime (k p : ℕ) (hp : p.Prime) :
    divisorTupleCount k p = k := by
  induction k with
  | zero => simp [divisorTupleCount, hp.ne_one]
  | succ k ih =>
    have h1 : (ArithmeticFunction.zeta ^ k) 1 = 1 :=
      ArithmeticFunction.isMultiplicative_zeta.pow.1
    change (ArithmeticFunction.zeta ^ (k + 1)) p = k + 1
    rw [pow_succ, ArithmeticFunction.mul_zeta_apply, hp.divisors]
    change (ArithmeticFunction.zeta ^ k) p = k at ih
    simp [hp.ne_one.symm, h1, ih, Nat.add_comm]

/-- A squarefree number has one independent choice among `k` tuple positions
for every prime factor. -/
theorem divisorTupleCount_squarefree (k n : ℕ) (hn : Squarefree n) :
    divisorTupleCount k n = k ^ n.primeFactors.card := by
  have hmult := (ArithmeticFunction.isMultiplicative_zeta.pow
    (k := k)).prod_primeFactors hn
  change (ArithmeticFunction.zeta ^ k) n = _
  rw [← hmult]
  calc
    _ = ∏ p ∈ n.primeFactors, k := by
      apply prod_congr rfl
      intro p hp
      exact divisorTupleCount_prime k p (Nat.prime_of_mem_primeFactors hp)
    _ = _ := by simp

/-- Explicit elementary logarithmic summatory majorant. -/
theorem divisorTuple_sum_le_log (k N : ℕ) :
    (∑ n ∈ Icc 1 N, (divisorTupleCount k n : ℝ)) ≤
      (N : ℝ) * (1 + Real.log N) ^ k := by
  refine (divisorTuple_sum_le k N).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_left₀ (by rw [harmonic, Rat.cast_sum]; positivity)
    (harmonic_le_one_add_log N) k

/-- A finite squarefree support has a power-of-prime-count sum bounded by
an elementary divisor-tuple sum. -/
theorem sum_squarefree_pow_le (S : Finset ℕ) (k N : ℕ)
    (hS : ∀ n ∈ S, Squarefree n) (hSN : S ⊆ Icc 1 N) :
    (∑ n ∈ S, (k : ℝ) ^ n.primeFactors.card) ≤
      (N : ℝ) * (1 + Real.log N) ^ k := by
  calc
    _ = ∑ n ∈ S, (divisorTupleCount k n : ℝ) := by
      apply sum_congr rfl
      intro n hn
      rw [divisorTupleCount_squarefree k n (hS n hn), Nat.cast_pow]
    _ ≤ ∑ n ∈ Icc 1 N, (divisorTupleCount k n : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hSN (by intros; positivity)
    _ ≤ _ := divisorTuple_sum_le_log k N

end Problem337.SelbergError

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.OptimizedSelbergError

namespace OAI
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset

namespace Problem337.SelbergOptimal

/-- The actual optimal weights have a logarithmically bounded weighted mass.
This uses the sharp coefficient bound, not the crude inverse-density estimate. -/
theorem optimalWeight_primeFactor_mass_le (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    (∑ d ∈ s.prodPrimes.divisors, |optimalWeight s z d| *
      (2 : ℝ) ^ d.primeFactors.card) ≤ (z : ℝ) * (1 + Real.log z) ^ 2 := by
  calc
    _ ≤ ∑ d ∈ s.prodPrimes.divisors,
        if d ≤ z then (2 : ℝ) ^ d.primeFactors.card else 0 := by
      apply sum_le_sum
      intro d hd
      by_cases hdz : d ≤ z
      · rw [ite_eq_left hdz]
        have hw : |optimalWeight s z d| ≤ 1 := by
          rw [optimalWeight_formula s z d (Nat.dvd_of_mem_divisors hd)]
          convert abs_normalized_complement_le_one s hz (Nat.dvd_of_mem_divisors hd) using 1
          unfold complementNormalizer
          congr 1
          ring
        simpa using mul_le_mul_of_nonneg_right hw
          (by positivity : 0 ≤ (2 : ℝ) ^ d.primeFactors.card)
      · rw [ite_eq_right hdz, optimalWeight_eq_zero_of_lt s (lt_of_not_ge hdz)]
        simp
    _ = ∑ d ∈ s.prodPrimes.divisors.filter (fun d => d ≤ z),
        (2 : ℝ) ^ d.primeFactors.card := (sum_filter _ _).symm
    _ ≤ _ := SelbergError.sum_squarefree_pow_le _ 2 z
      (fun d hd => s.squarefree_of_mem_divisors_prodPrimes (mem_filter.mp hd).1)
      (by
        intro d hd
        obtain ⟨hdP, hdz⟩ := mem_filter.mp hd
        exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdP, hdz⟩)

/-- A dimension-two local remainder envelope gives an explicit logarithmic
error for the constructed optimal Selberg weights. -/
theorem errSum_optimalWeight_le_log (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z)
    (hrem : ∀ a ∈ s.prodPrimes.divisors, ∀ b ∈ s.prodPrimes.divisors,
      |s.rem (Nat.lcm a b)| ≤
        (2 : ℝ) ^ a.primeFactors.card * (2 : ℝ) ^ b.primeFactors.card) :
    s.errSum (BoundingSieve.lambdaSquared (optimalWeight s z)) ≤
      (z : ℝ) ^ 2 * (1 + Real.log z) ^ 4 := by
  calc
    _ ≤ (∑ d ∈ s.prodPrimes.divisors, |optimalWeight s z d| *
        (2 : ℝ) ^ d.primeFactors.card) ^ 2 :=
      SelbergError.errSum_lambdaSquared_le_sq s (optimalWeight s z)
        (fun d => (2 : ℝ) ^ d.primeFactors.card) hrem
    _ ≤ ((z : ℝ) * (1 + Real.log z) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (sum_nonneg (by intros; positivity))
        (optimalWeight_primeFactor_mass_le s hz) 2
    _ = _ := by ring

/-- Fully optimized finite Selberg inequality with explicit logarithmic error. -/
theorem siftedSum_le_log_error (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z)
    (hrem : ∀ a ∈ s.prodPrimes.divisors, ∀ b ∈ s.prodPrimes.divisors,
      |s.rem (Nat.lcm a b)| ≤
        (2 : ℝ) ^ a.primeFactors.card * (2 : ℝ) ^ b.primeFactors.card) :
    s.siftedSum ≤ s.totalMass / normalizer s z +
      (z : ℝ) ^ 2 * (1 + Real.log z) ^ 4 :=
  (siftedSum_le s hz).trans
    (add_le_add le_rfl (errSum_optimalWeight_le_log s hz hrem))

end Problem337.SelbergOptimal

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.GoldbachSieveLocal

namespace OAI
/-!
Finite local arithmetic for a possible binary Goldbach sieve.  These results
count roots of the polynomial `x * (u - x)` and provide its multiplicative local
density.  They do not assert any prime-pair bound or positive density of Goldbach
numbers.
-/

noncomputable section

open scoped BigOperators

namespace Problem337

/-- Residue classes removed by the binary Goldbach sieve. -/
def GoldbachSieveRoot (u d : ℕ) :=
  {x : ZMod d // x * ((u : ZMod d) - x) = 0}

/-- Local number of roots of `x * (u - x)` modulo `d`. -/
def goldbachSieveRootCount (u d : ℕ) : ℕ :=
  Nat.card (GoldbachSieveRoot u d)

/-- The Chinese remainder theorem separates the local root conditions. -/
def goldbachSieveRootEquiv (u a b : ℕ) (hab : a.Coprime b) :
    GoldbachSieveRoot u (a * b) ≃
      GoldbachSieveRoot u a × GoldbachSieveRoot u b := by
  let e := ZMod.chineseRemainder hab
  apply (Equiv.subtypeEquiv e.toEquiv ?_).trans Equiv.subtypeProdEquivProd
  intro x
  change x * ((u : ZMod (a * b)) - x) = 0 ↔
    (e x).1 * ((u : ZMod a) - (e x).1) = 0 ∧
      (e x).2 * ((u : ZMod b) - (e x).2) = 0
  have h := e.injective.eq_iff (a := x * ((u : ZMod (a * b)) - x)) (b := 0)
  simpa only [map_mul, map_sub, map_natCast, map_zero, Prod.mk_zero_zero,
    Prod.mul_def, Prod.sub_def, Prod.fst_natCast, Prod.snd_natCast,
    Prod.mk.injEq, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] using h.symm

/-- Root counts are multiplicative at coprime moduli, with no distribution hypothesis. -/
theorem goldbachSieveRootCount_mul (u a b : ℕ) (hab : a.Coprime b) :
    goldbachSieveRootCount u (a * b) =
      goldbachSieveRootCount u a * goldbachSieveRootCount u b := by
  unfold goldbachSieveRootCount
  rw [Nat.card_congr (goldbachSieveRootEquiv u a b hab), Nat.card_prod]

@[simp] theorem goldbachSieveRootCount_one (u : ℕ) :
    goldbachSieveRootCount u 1 = 1 := by
  unfold goldbachSieveRootCount GoldbachSieveRoot
  have e : {x : ZMod 1 // x * ((u : ZMod 1) - x) = 0} ≃ ZMod 1 :=
    Equiv.subtypeUnivEquiv (fun x => Subsingleton.elim _ _)
  rw [Nat.card_congr e, Nat.card_zmod]

/-- At a prime, the only roots are zero and the target residue. -/
theorem goldbachSieveRootCount_prime (u p : ℕ) (hp : p.Prime) :
    goldbachSieveRootCount u p = if p ∣ u then 1 else 2 := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hroots : (Finset.univ.filter
      (fun x : ZMod p => x * ((u : ZMod p) - x) = 0)) = {0, (u : ZMod p)} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      mul_eq_zero, sub_eq_zero, Finset.mem_insert, Finset.mem_singleton]
    tauto
  unfold goldbachSieveRootCount GoldbachSieveRoot
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hroots]
  by_cases h : p ∣ u
  · simp [h, (ZMod.natCast_eq_zero_iff u p).mpr h]
  · have hne : (u : ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff u p).not.mpr h
    simp [h, Ne.symm hne]

/-- A finite product of distinct primes gives the product of the local counts. -/
theorem goldbachSieveRootCount_prod_primes (u : ℕ) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    goldbachSieveRootCount u (∏ p ∈ s, p) =
      ∏ p ∈ s, goldbachSieveRootCount u p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      have hpp := hs p (Finset.mem_insert_self p s)
      have hsp : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
      have hcop : p.Coprime (∏ q ∈ s, q) := by
        apply Nat.Coprime.prod_right
        intro q hq
        apply (Nat.coprime_primes hpp (hsp q hq)).mpr
        intro heq
        exact hp (heq ▸ hq)
      rw [Finset.prod_insert hp, goldbachSieveRootCount_mul u p _ hcop,
        ih hsp, Finset.prod_insert hp]

/-- Exact squarefree local factor for the binary Goldbach sieve. -/
theorem goldbachSieveRootCount_squarefree (u d : ℕ) (hd : Squarefree d) :
    goldbachSieveRootCount u d =
      ∏ p ∈ d.primeFactors, if p ∣ u then 1 else 2 := by
  calc
    goldbachSieveRootCount u d =
        goldbachSieveRootCount u (∏ p ∈ d.primeFactors, p) := by
          rw [Nat.prod_primeFactors_of_squarefree hd]
    _ = ∏ p ∈ d.primeFactors, goldbachSieveRootCount u p :=
      goldbachSieveRootCount_prod_primes u d.primeFactors
        (fun p hp => (Nat.mem_primeFactors.mp hp).1)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      exact goldbachSieveRootCount_prime u p (Nat.mem_primeFactors.mp hp).1

/-- The exact finite local root density, normalized as an arithmetic function. -/
def goldbachSieveDensity (u : ℕ) : ArithmeticFunction ℝ where
  toFun d := (goldbachSieveRootCount u d : ℝ) / (d : ℝ)
  map_zero' := by simp

@[simp] theorem goldbachSieveDensity_apply (u d : ℕ) :
    goldbachSieveDensity u d = (goldbachSieveRootCount u d : ℝ) / (d : ℝ) := rfl

/-- The finite local density has exactly the multiplicativity required by a sieve. -/
theorem goldbachSieveDensity_isMultiplicative (u : ℕ) :
    (goldbachSieveDensity u).IsMultiplicative := by
  constructor
  · simp
  · intro a b hab
    simp only [goldbachSieveDensity_apply, goldbachSieveRootCount_mul u a b hab,
      Nat.cast_mul, mul_div_mul_comm]

/-- The local density at a prime is `1/p` or `2/p`. -/
theorem goldbachSieveDensity_prime (u p : ℕ) (hp : p.Prime) :
    goldbachSieveDensity u p = if p ∣ u then 1 / (p : ℝ) else 2 / (p : ℝ) := by
  rw [goldbachSieveDensity_apply, goldbachSieveRootCount_prime u p hp]
  split_ifs <;> norm_num

/-- All prime local root densities are positive. -/
theorem goldbachSieveDensity_prime_pos (u p : ℕ) (hp : p.Prime) :
    0 < goldbachSieveDensity u p := by
  rw [goldbachSieveDensity_prime u p hp]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  split_ifs <;> positivity

/-- At odd primes the sieve is nondegenerate. At two, this requires an even target. -/
theorem goldbachSieveDensity_prime_lt_one (u p : ℕ) (hp : p.Prime)
    (hparity : p = 2 → 2 ∣ u) : goldbachSieveDensity u p < 1 := by
  rw [goldbachSieveDensity_prime u p hp]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  split_ifs with h
  · rw [div_lt_one hpR]
    exact_mod_cast hp.one_lt
  · have hp2 : 2 < p := by
      have := hp.two_le
      by_contra hnot
      have heq : p = 2 := by omega
      exact h (heq ▸ hparity heq)
    rw [div_lt_one hpR]
    exact_mod_cast hp2

end Problem337

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.ResidueIntervalCount

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- The exact number of natural numbers below `N` in one residue class. -/
theorem card_range_zmod_eq {d : ℕ} [NeZero d] (N : ℕ) (r : ZMod d) :
    ((Finset.range N).filter (fun n : ℕ => (n : ZMod d) = r)).card =
      N / d + if r.val < N % d then 1 else 0 := by
  have hd : 0 < d := NeZero.pos d
  have he : (Finset.range N).filter (fun n : ℕ => (n : ZMod d) = r) =
      (Finset.range N).filter (fun n => Nat.ModEq d n r.val) := by
    apply Finset.filter_congr
    intro n hn
    simpa only [ZMod.natCast_zmod_val] using
      (ZMod.natCast_eq_natCast_iff n r.val d)
  rw [he, ← Nat.count_eq_card_filter_range,
    Nat.count_modEq_card N hd r.val, Nat.mod_eq_of_lt r.val_lt]

/-- Exact quotient/remainder decomposition for any collection of residues. -/
theorem card_range_zmod_mem {d : ℕ} [NeZero d] (N : ℕ) (S : Finset (ZMod d)) :
    ((Finset.range N).filter (fun n : ℕ => (n : ZMod d) ∈ S)).card =
      (N / d) * S.card + (S.filter (fun r => r.val < N % d)).card := by
  classical
  rw [← Finset.sum_card_fiberwise_eq_card_filter (Finset.range N) S
    (fun n : ℕ => (n : ZMod d))]
  simp_rw [card_range_zmod_eq]
  rw [Finset.sum_add_distrib]
  simp [mul_comm]

/-- The elementary progression-counting error is at most the number of
residue classes, uniformly in the interval length and modulus. -/
theorem abs_card_range_zmod_mem_sub {d : ℕ} [NeZero d]
    (N : ℕ) (S : Finset (ZMod d)) :
    |(((Finset.range N).filter (fun n : ℕ => (n : ZMod d) ∈ S)).card : ℝ) -
      (N : ℝ) * S.card / d| ≤ (S.card : ℝ) := by
  classical
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hr : ((N % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt N (NeZero.pos d)
  have hq : (N : ℝ) = (N / d : ℕ) * (d : ℝ) + (N % d : ℕ) := by
    exact_mod_cast (show N = (N / d) * d + N % d by
      simpa only [Nat.mul_comm] using (Nat.div_add_mod N d).symm)
  have hs : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have ht : (0 : ℝ) ≤ (S.filter (fun r => r.val < N % d)).card := Nat.cast_nonneg _
  have hts : ((S.filter (fun r => r.val < N % d)).card : ℝ) ≤ S.card := by
    exact_mod_cast Finset.card_filter_le S (fun r => r.val < N % d)
  have hfrac0 : (0 : ℝ) ≤ (N % d : ℕ) / d := by positivity
  have hfrac1 : ((N % d : ℕ) : ℝ) / d ≤ 1 := (div_le_one hd).2 hr.le
  have hmain : (N : ℝ) * S.card / d =
      (N / d : ℕ) * (S.card : ℝ) + ((N % d : ℕ) : ℝ) / d * S.card := by
    rw [hq]
    field_simp
  rw [card_range_zmod_mem, Nat.cast_add, Nat.cast_mul, hmain]
  rw [abs_le]
  constructor <;> nlinarith

end Problem337

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.PeriodicResidueCount

namespace OAI
noncomputable section

namespace Problem337

/-- A periodic predicate has one full period's worth of solutions in each block. -/
theorem periodic_count_mul {p : ℕ → Prop} [DecidablePred p] {d : ℕ}
    (hp : Function.Periodic p d) (q : ℕ) :
    Nat.count p (q * d) = q * Nat.count p d := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, Nat.count_add']
    have hshift : (fun k => p (k + d)) = p := by
      funext k
      exact hp k
    simp only [hshift, ih]
    ring

/-- Exact quotient-and-remainder formula for a periodic counting function. -/
theorem periodic_count_div_mod {p : ℕ → Prop} [DecidablePred p] {d : ℕ}
    (hp : Function.Periodic p d) (N : ℕ) :
    Nat.count p N = (N / d) * Nat.count p d + Nat.count p (N % d) := by
  conv_lhs => rw [← Nat.mod_add_div N d]
  rw [Nat.count_add']
  have hshift : (fun k => p (k + d * (N / d))) = p := by
    funext k
    simpa [Nat.mul_comm] using hp.nsmul (N / d) k
  simp only [hshift]
  rw [Nat.mul_comm d, periodic_count_mul hp]
  omega

/-- The count on an initial interval differs from its periodic mean by at most the number
of allowed residues in one period. This bound is uniform in the length of the interval. -/
theorem periodic_count_discrepancy {p : ℕ → Prop} [DecidablePred p] {d : ℕ}
    (hd : 0 < d) (hp : Function.Periodic p d) (N : ℕ) :
    |(Nat.count p N : ℝ) - (N : ℝ) * Nat.count p d / d| ≤ Nat.count p d := by
  have hcount := periodic_count_div_mod hp N
  have hrem := Nat.count_monotone p (Nat.mod_lt N hd).le
  have hdiv := Nat.mod_add_div N d
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hremR : (Nat.count p (N % d) : ℝ) ≤ Nat.count p d := by exact_mod_cast hrem
  have hmodR : ((N % d : ℕ) : ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt N hd).le
  have hdivR : ((N % d : ℕ) : ℝ) + (d : ℝ) * (N / d : ℕ) = N := by exact_mod_cast hdiv
  have hcountR : (Nat.count p N : ℝ) =
      (N / d : ℕ) * (Nat.count p d : ℝ) + Nat.count p (N % d) := by exact_mod_cast hcount
  have hnonneg : (0 : ℝ) ≤ Nat.count p d := by positivity
  have hterm0 : 0 ≤ ((N % d : ℕ) : ℝ) * Nat.count p d / d := by positivity
  have hterm : ((N % d : ℕ) : ℝ) * Nat.count p d / d ≤ Nat.count p d := by
    apply (div_le_iff₀ hdR).2
    nlinarith [mul_le_mul_of_nonneg_right hmodR hnonneg]
  have heq : (Nat.count p N : ℝ) - (N : ℝ) * Nat.count p d / d =
      Nat.count p (N % d) - ((N % d : ℕ) : ℝ) * Nat.count p d / d := by
    rw [hcountR, ← hdivR]
    field_simp
    ring
  rw [heq, abs_le]
  constructor <;> linarith [show (0 : ℝ) ≤ Nat.count p (N % d) by positivity]

/-- Shifting a periodic predicate does not change its mass over a full period. -/
theorem periodic_count_shift_period {p : ℕ → Prop} [DecidablePred p] {d : ℕ}
    (hp : Function.Periodic p d) (a : ℕ) :
    Nat.count (fun n => p (a + n)) d = Nat.count p d := by
  have h₁ := Nat.count_add p a d
  have h₂ := Nat.count_add' p a d
  have hshift : (fun n => p (n + d)) = p := funext hp
  simp only [hshift] at h₂
  omega

/-- Counting a predicate on a shifted natural interval is the same as counting
its translate on an initial interval. -/
theorem filter_Ico_card_eq_count_shift (p : ℕ → Prop) [DecidablePred p]
    (a N : ℕ) :
    ((Finset.Ico a (a + N)).filter p).card =
      Nat.count (fun n => p (a + n)) N := by
  rw [Nat.count_eq_card_filter_range, ← Nat.Ico_zero_eq_range]
  have hmap := Finset.map_add_left_Ico 0 N a
  rw [Nat.add_zero] at hmap
  rw [← hmap, Finset.filter_map, Finset.card_map]
  rfl

/-- Sharp periodic discrepancy on any shifted interval: the error is bounded
by one period's mass, independent of both endpoints. -/
theorem periodic_Ico_count_discrepancy {p : ℕ → Prop} [DecidablePred p] {d : ℕ}
    (hd : 0 < d) (hp : Function.Periodic p d) (a N : ℕ) :
    |(((Finset.Ico a (a + N)).filter p).card : ℝ) -
      (N : ℝ) * Nat.count p d / d| ≤ Nat.count p d := by
  have hshift : Function.Periodic (fun n => p (a + n)) d := by
    intro n
    simpa only [Nat.add_assoc] using hp (a + n)
  have h := periodic_count_discrepancy hd hshift N
  rw [periodic_count_shift_period hp a] at h
  simpa only [filter_Ico_card_eq_count_shift] using h

/-- The periodic mass of a predicate on residue classes is its finite cardinality. -/
theorem zmod_predicate_period_count (d : ℕ) [NeZero d]
    (P : ZMod d → Prop) [DecidablePred P] :
    Nat.count (fun n : ℕ => P (n : ZMod d)) d =
      (Finset.univ.filter P).card := by
  classical
  simpa [Nat.count_eq_card_filter_range, Nat.div_self (NeZero.pos d)] using
    (card_range_zmod_mem d (Finset.univ.filter P))

/-- Residue classes are equidistributed up to one copy of the allowed set on
any natural interval, without a primality or coprimality assumption. -/
theorem zmod_predicate_Ico_discrepancy (d : ℕ) [NeZero d]
    (P : ZMod d → Prop) [DecidablePred P] (a N : ℕ) :
    |(((Finset.Ico a (a + N)).filter (fun n : ℕ => P (n : ZMod d))).card : ℝ) -
      (N : ℝ) * (Finset.univ.filter P).card / d| ≤ (Finset.univ.filter P).card := by
  have hp : Function.Periodic (fun n : ℕ => P (n : ZMod d)) d := by
    intro n
    simp
  have h := periodic_Ico_count_discrepancy (NeZero.pos d) hp a N
  simpa only [zmod_predicate_period_count d P] using h

end Problem337

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.GoldbachSieveRemainder

namespace OAI
/-!
The exact finite progression error for the binary Goldbach polynomial. No
prime-distribution estimate or sieve-density lower bound is assumed here.
-/

noncomputable section

namespace Problem337

/-- The local root-count definition is the cardinality of the corresponding
finite set whenever the modulus is nonzero. -/
theorem goldbachSieveRootCount_eq_filter_card (u d : ℕ) [NeZero d] :
    goldbachSieveRootCount u d =
      (Finset.univ.filter (fun x : ZMod d => x * ((u : ZMod d) - x) = 0)).card := by
  classical
  unfold goldbachSieveRootCount GoldbachSieveRoot
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- On the natural interval used for ordered positive prime pairs, the
truncated natural subtraction agrees with subtraction in the residue ring. -/
theorem goldbach_polynomial_dvd_iff_zmod (u d n : ℕ) (hn : n ≤ u) :
    d ∣ n * (u - n) ↔
      (n : ZMod d) * ((u : ZMod d) - (n : ZMod d)) = 0 := by
  rw [← Nat.cast_sub hn, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]

/-- Sharp, uniform error for counting divisibility of `n*(u-n)` on `1 ≤ n < u`.
The formulation includes the empty intervals at `u=0` and `u=1`. -/
theorem goldbach_polynomial_count_discrepancy (u d : ℕ) [NeZero d] :
    |(((Finset.Icc 1 (u - 1)).filter (fun n => d ∣ n * (u - n))).card : ℝ) -
      ((u - 1 : ℕ) : ℝ) * goldbachSieveRootCount u d / d| ≤
        goldbachSieveRootCount u d := by
  classical
  have hI : Finset.Icc 1 (u - 1) = Finset.Ico 1 (1 + (u - 1)) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hfilter : (Finset.Icc 1 (u - 1)).filter (fun n => d ∣ n * (u - n)) =
      (Finset.Ico 1 (1 + (u - 1))).filter
        (fun n : ℕ => (n : ZMod d) * ((u : ZMod d) - (n : ZMod d)) = 0) := by
    rw [← hI]
    apply Finset.filter_congr
    intro n hn
    exact goldbach_polynomial_dvd_iff_zmod u d n
      ((Finset.mem_Icc.mp hn).2.trans (Nat.sub_le u 1))
  rw [hfilter, goldbachSieveRootCount_eq_filter_card]
  exact zmod_predicate_Ico_discrepancy d
    (fun x : ZMod d => x * ((u : ZMod d) - x) = 0) 1 (u - 1)

/-- The same error with the normalized multiplicative sieve density. -/
theorem goldbach_polynomial_count_density_discrepancy (u d : ℕ) [NeZero d] :
    |(((Finset.Icc 1 (u - 1)).filter (fun n => d ∣ n * (u - n))).card : ℝ) -
      goldbachSieveDensity u d * ((u - 1 : ℕ) : ℝ)| ≤
        goldbachSieveRootCount u d := by
  simpa only [goldbachSieveDensity_apply, div_mul_eq_mul_div, mul_div_assoc, mul_comm] using
    goldbach_polynomial_count_discrepancy u d

end Problem337

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.PrimePairSieveModel

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.PrimePairSieve

/-- Pushing a finite set through a noninjective map retains the multiplicity
of each image value. In particular, the two ordered Goldbach pairs with
coordinates exchanged must not be identified by the polynomial map. -/
def fiberWeight (A : Finset ℕ) (f : ℕ → ℕ) (y : ℕ) : ℝ :=
  ((A.filter (fun x => f x = y)).card : ℝ)

lemma fiberWeight_nonneg (A : Finset ℕ) (f : ℕ → ℕ) (y : ℕ) :
    0 ≤ fiberWeight A f y := by
  exact Nat.cast_nonneg _

lemma sum_fiberWeight_indicator (A : Finset ℕ) (f : ℕ → ℕ)
    (p : ℕ → Prop) [DecidablePred p] :
    (∑ y ∈ A.image f, if p y then fiberWeight A f y else 0) =
      ((A.filter (fun x => p (f x))).card : ℝ) := by
  classical
  rw [← Finset.sum_filter]
  unfold fiberWeight
  rw [← Nat.cast_sum]
  congr 1
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hx, _, hp⟩
    exact ⟨hx, hp⟩
  · rintro ⟨hx, hp⟩
    exact ⟨hx, Finset.mem_image_of_mem f hx, hp⟩

/-- A concrete `BoundingSieve` attached to any polynomial image, with exact
fiber weights rather than an unjustified injectivity assumption. -/
def imageSieve (A : Finset ℕ) (f : ℕ → ℕ) (P : ℕ)
    (hP : Squarefree P) (ν : ArithmeticFunction ℝ)
    (hν : ν.IsMultiplicative)
    (hνpos : ∀ p : ℕ, p.Prime → p ∣ P → 0 < ν p)
    (hνlt : ∀ p : ℕ, p.Prime → p ∣ P → ν p < 1) : BoundingSieve where
  support := A.image f
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fiberWeight A f
  weights_nonneg := fiberWeight_nonneg A f
  totalMass := A.card
  nu := ν
  nu_mult := hν
  nu_pos_of_prime := hνpos
  nu_lt_one_of_prime := hνlt

lemma imageSieve_multSum (A : Finset ℕ) (f : ℕ → ℕ) (P : ℕ)
    (hP : Squarefree P) (ν : ArithmeticFunction ℝ)
    (hν : ν.IsMultiplicative)
    (hνpos : ∀ p : ℕ, p.Prime → p ∣ P → 0 < ν p)
    (hνlt : ∀ p : ℕ, p.Prime → p ∣ P → ν p < 1) (d : ℕ) :
    (imageSieve A f P hP ν hν hνpos hνlt).multSum d =
      ((A.filter (fun x => d ∣ f x)).card : ℝ) := by
  exact sum_fiberWeight_indicator A f (fun y => d ∣ y)

lemma imageSieve_siftedSum (A : Finset ℕ) (f : ℕ → ℕ) (P : ℕ)
    (hP : Squarefree P) (ν : ArithmeticFunction ℝ)
    (hν : ν.IsMultiplicative)
    (hνpos : ∀ p : ℕ, p.Prime → p ∣ P → 0 < ν p)
    (hνlt : ∀ p : ℕ, p.Prime → p ∣ P → ν p < 1) :
    (imageSieve A f P hP ν hν hνpos hνlt).siftedSum =
      ((A.filter (fun x => P.Coprime (f x))).card : ℝ) := by
  exact sum_fiberWeight_indicator A f (fun y => P.Coprime y)

/-- First coordinates of the ordered representations of `N` by two primes. -/
def primePairs (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (N - 1)).filter (fun x => x.Prime ∧ (N - x).Prime)

/-- The original integer coordinates left after sieving both prime factors. -/
def siftedPairs (N P : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (N - 1)).filter (fun x => P.Coprime (x * (N - x)))

/-- A prime pair is either sifted or has a coordinate among the prime divisors
of `P`. This is the exact small-prime correction, valid even for `N=0,1`. -/
theorem primePairs_subset (N P : ℕ) (hP : P ≠ 0) :
    primePairs N ⊆ siftedPairs N P ∪
      (P.primeFactors ∪ P.primeFactors.image (fun p => N - p)) := by
  intro x hx
  obtain ⟨hxI, hxprime, hother⟩ := Finset.mem_filter.mp hx
  have hxN : x ≤ N := by
    have := (Finset.mem_Icc.mp hxI).2
    omega
  by_cases hxdvd : x ∣ P
  · exact Finset.mem_union_right _ (Finset.mem_union_left _
      (Nat.mem_primeFactors.mpr ⟨hxprime, hxdvd, hP⟩))
  by_cases hydvd : N - x ∣ P
  · apply Finset.mem_union_right
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨N - x, Nat.mem_primeFactors.mpr ⟨hother, hydvd, hP⟩,
      Nat.sub_sub_self hxN⟩
  apply Finset.mem_union_left
  apply Finset.mem_filter.mpr
  exact ⟨hxI, ((hxprime.coprime_iff_not_dvd.mpr hxdvd).symm).mul_right
    ((hother.coprime_iff_not_dvd.mpr hydvd).symm)⟩

/-- At most twice the number of sieving primes is lost when passing from
ordered prime pairs to sifted polynomial values with multiplicities. -/
theorem card_primePairs_le_sifted (N P : ℕ) (hP : P ≠ 0) :
    (primePairs N).card ≤ (siftedPairs N P).card + 2 * P.primeFactors.card := by
  calc
    (primePairs N).card ≤
        (siftedPairs N P ∪ (P.primeFactors ∪
          P.primeFactors.image (fun p => N - p))).card :=
      Finset.card_le_card (primePairs_subset N P hP)
    _ ≤ (siftedPairs N P).card + (P.primeFactors ∪
          P.primeFactors.image (fun p => N - p)).card := Finset.card_union_le _ _
    _ ≤ (siftedPairs N P).card +
        (P.primeFactors.card + (P.primeFactors.image (fun p => N - p)).card) :=
      Nat.add_le_add_left (Finset.card_union_le _ _) _
    _ ≤ (siftedPairs N P).card + 2 * P.primeFactors.card := by
      have := Finset.card_image_le (s := P.primeFactors) (f := fun p => N - p)
      omega

/-- The exact polynomial divisor count is the remainder term supplied to the
Selberg sieve; no analytic approximation is built into this model. -/
lemma imageSieve_rem (A : Finset ℕ) (f : ℕ → ℕ) (P : ℕ)
    (hP : Squarefree P) (ν : ArithmeticFunction ℝ)
    (hν : ν.IsMultiplicative)
    (hνpos : ∀ p : ℕ, p.Prime → p ∣ P → 0 < ν p)
    (hνlt : ∀ p : ℕ, p.Prime → p ∣ P → ν p < 1) (d : ℕ) :
    (imageSieve A f P hP ν hν hνpos hνlt).rem d =
      ((A.filter (fun x => d ∣ f x)).card : ℝ) - ν d * A.card := by
  rw [BoundingSieve.rem, imageSieve_multSum]
  rfl

/-- A fully concrete prime-pair Λ² bound with ordered-pair multiplicities and
an explicit small-prime correction. The main coefficient and its arithmetic
remainder are still to be estimated by the sieve application. -/
theorem primePairs_lambdaSquared_bound (N P : ℕ)
    (hP : Squarefree P) (ν : ArithmeticFunction ℝ)
    (hν : ν.IsMultiplicative)
    (hνpos : ∀ p : ℕ, p.Prime → p ∣ P → 0 < ν p)
    (hνlt : ∀ p : ℕ, p.Prime → p ∣ P → ν p < 1)
    (w : ℕ → ℝ) (hw : w 1 = 1) :
    ((primePairs N).card : ℝ) ≤
      ((Finset.Icc 1 (N - 1)).card : ℝ) *
        (∑ d ∈ P.divisors, BoundingSieve.lambdaSquared w d * ν d) +
      (∑ d ∈ P.divisors, |BoundingSieve.lambdaSquared w d| *
        |(((Finset.Icc 1 (N - 1)).filter
            (fun x => d ∣ x * (N - x))).card : ℝ) -
          ν d * (Finset.Icc 1 (N - 1)).card|) +
      2 * P.primeFactors.card := by
  let s := imageSieve (Finset.Icc 1 (N - 1)) (fun x => x * (N - x))
    P hP ν hν hνpos hνlt
  have hcard : ((primePairs N).card : ℝ) ≤
      ((siftedPairs N P).card : ℝ) + 2 * P.primeFactors.card := by
    exact_mod_cast card_primePairs_le_sifted N P hP.ne_zero
  have hs : s.siftedSum = ((siftedPairs N P).card : ℝ) :=
    imageSieve_siftedSum _ _ _ _ _ _ _ _
  have hb := s.siftedSum_le_mainSum_errSum_of_upperMoebius
    (BoundingSieve.lambdaSquared w) (BoundingSieve.upperMoebius_lambdaSquared w hw)
  have herr : s.errSum (BoundingSieve.lambdaSquared w) =
      ∑ d ∈ P.divisors, |BoundingSieve.lambdaSquared w d| *
        |(((Finset.Icc 1 (N - 1)).filter
            (fun x => d ∣ x * (N - x))).card : ℝ) -
          ν d * (Finset.Icc 1 (N - 1)).card| := by
    unfold BoundingSieve.errSum
    simp only [s, imageSieve_rem]
    rfl
  rw [hs, herr] at hb
  change ((siftedPairs N P).card : ℝ) ≤
    ((Finset.Icc 1 (N - 1)).card : ℝ) *
      (∑ d ∈ P.divisors, BoundingSieve.lambdaSquared w d * ν d) + _ at hb
  linarith

end Problem337.PrimePairSieve

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.GoldbachSieveApplication

namespace OAI
/-!
A finite, unconditional Selberg upper bound for ordered prime pairs with the
actual Goldbach local density and explicit root-count error. The analytic
estimates for the optimizing weights and denominator are separate tasks.
-/

noncomputable section
open scoped BigOperators

namespace Problem337

/-- The actual Goldbach local density and progression error may be inserted in
the multiplicity-preserving Selberg model. All arithmetic approximation input
has been discharged; the weights are still arbitrary with `w 1 = 1`. -/
theorem goldbach_primePairs_lambdaSquared_bound (N P : ℕ)
    (hN : 2 ∣ N) (hP : Squarefree P) (w : ℕ → ℝ) (hw : w 1 = 1) :
    ((PrimePairSieve.primePairs N).card : ℝ) ≤
      ((N - 1 : ℕ) : ℝ) *
        (∑ d ∈ P.divisors, BoundingSieve.lambdaSquared w d * goldbachSieveDensity N d) +
      (∑ d ∈ P.divisors, |BoundingSieve.lambdaSquared w d| * goldbachSieveRootCount N d) +
      2 * P.primeFactors.card := by
  have hpos : ∀ p : ℕ, p.Prime → p ∣ P → 0 < goldbachSieveDensity N p := by
    intro p hp _
    exact goldbachSieveDensity_prime_pos N p hp
  have hlt : ∀ p : ℕ, p.Prime → p ∣ P → goldbachSieveDensity N p < 1 := by
    intro p hp _
    exact goldbachSieveDensity_prime_lt_one N p hp (fun _ => hN)
  have hb := PrimePairSieve.primePairs_lambdaSquared_bound N P hP
    (goldbachSieveDensity N) (goldbachSieveDensity_isMultiplicative N)
    hpos hlt w hw
  have hcard : (Finset.Icc 1 (N - 1)).card = N - 1 := by simp
  rw [hcard] at hb
  refine hb.trans (add_le_add (add_le_add le_rfl ?_) le_rfl)
  apply Finset.sum_le_sum
  intro d hd
  have hd0 : d ≠ 0 := by
    have hdiv := (Nat.mem_divisors.mp hd).1
    intro hzero
    subst d
    exact hP.ne_zero (by simpa using hdiv)
  let : NeZero d := ⟨hd0⟩
  exact mul_le_mul_of_nonneg_left (goldbach_polynomial_count_density_discrepancy N d)
    (abs_nonneg _)

end Problem337

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.GoldbachSieveRootBounds

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

instance goldbachSieveRootFintype (u d : ℕ) [NeZero d] :
    Fintype (GoldbachSieveRoot u d) :=
  inferInstanceAs (Fintype {x : ZMod d // x * ((u : ZMod d) - x) = 0})

instance goldbachSieveRootNonempty (u d : ℕ) : Nonempty (GoldbachSieveRoot u d) :=
  ⟨⟨0, by simp⟩⟩

/-- Reduction modulo two possibly noncoprime moduli is injective when the
source modulus is their least common multiple. This remains true on roots. -/
def goldbachSieveRootLCMEmbedding (u a b : ℕ) :
    GoldbachSieveRoot u (a.lcm b) ↪
      GoldbachSieveRoot u a × GoldbachSieveRoot u b := by
  let e : ZMod (a.lcm b) →+* ZMod a × ZMod b :=
    ZMod.castHom (dvd_refl (a.lcm b)) _
  have einj : Function.Injective e := ZMod.castHom_injective _
  have he (x : GoldbachSieveRoot u (a.lcm b)) :
      (e x.val).1 * ((u : ZMod a) - (e x.val).1) = 0 ∧
        (e x.val).2 * ((u : ZMod b) - (e x.val).2) = 0 := by
    have h := congrArg e x.property
    simpa only [map_mul, map_sub, map_natCast, map_zero, Prod.mul_def,
      Prod.sub_def, Prod.ext_iff, Prod.fst_natCast, Prod.snd_natCast,
      Prod.fst_zero, Prod.snd_zero] using h
  refine ⟨fun x => (⟨(e x.val).1, (he x).1⟩, ⟨(e x.val).2, (he x).2⟩), ?_⟩
  intro x y hxy
  apply Subtype.ext
  apply einj
  apply Prod.ext
  · exact congrArg (fun z : GoldbachSieveRoot u a × GoldbachSieveRoot u b => z.1.val) hxy
  · exact congrArg (fun z : GoldbachSieveRoot u a × GoldbachSieveRoot u b => z.2.val) hxy

/-- LCM-submultiplicativity of the root count. This needs no squarefreeness. -/
theorem goldbachSieveRootCount_lcm_le (u a b : ℕ) [NeZero a] [NeZero b] :
    goldbachSieveRootCount u (a.lcm b) ≤
      goldbachSieveRootCount u a * goldbachSieveRootCount u b := by
  unfold goldbachSieveRootCount
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective (goldbachSieveRootLCMEmbedding u a b)
    (goldbachSieveRootLCMEmbedding u a b).injective

/-- Zero is always a root, so each positive modulus has positive local count. -/
theorem goldbachSieveRootCount_pos (u d : ℕ) [NeZero d] :
    0 < goldbachSieveRootCount u d := by
  exact Nat.card_pos

/-- The local root count cannot exceed the modulus. -/
theorem goldbachSieveRootCount_le (u d : ℕ) [NeZero d] :
    goldbachSieveRootCount u d ≤ d := by
  calc
    goldbachSieveRootCount u d ≤ Nat.card (ZMod d) :=
      Nat.card_le_card_of_injective (fun x : GoldbachSieveRoot u d => x.val)
        Subtype.val_injective
    _ = d := Nat.card_zmod d

/-- Exact exponent of two in a squarefree local root count. -/
theorem goldbachSieveRootCount_eq_two_pow (u d : ℕ) (hd : Squarefree d) :
    goldbachSieveRootCount u d =
      2 ^ (d.primeFactors.filter (fun p => ¬p ∣ u)).card := by
  rw [goldbachSieveRootCount_squarefree u d hd]
  have hf : (∏ p ∈ d.primeFactors, if p ∣ u then 1 else 2) =
      ∏ p ∈ d.primeFactors.filter (fun p => ¬p ∣ u), (2 : ℕ) := by
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro p hp
    split_ifs <;> simp_all
  rw [hf, Finset.prod_const]

/-- Squarefree local root counts are bounded by the number of subsets of
prime factors, uniformly in the target. -/
theorem goldbachSieveRootCount_le_two_pow (u d : ℕ) (hd : Squarefree d) :
    goldbachSieveRootCount u d ≤ 2 ^ d.primeFactors.card := by
  rw [goldbachSieveRootCount_eq_two_pow u d hd]
  exact Nat.pow_le_pow_right (by omega) (Finset.card_filter_le _ _)

end Problem337

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.GoldbachSelbergBound

namespace OAI
noncomputable section
open scoped BigOperators
open Finset

namespace Problem337.GoldbachSelberg

/-- The actual multiplicity-preserving sieve for an even target. -/
def sieve (N P : ℕ) (hN : 2 ∣ N) (hP : Squarefree P) : BoundingSieve :=
  PrimePairSieve.imageSieve (Icc 1 (N - 1)) (fun x => x * (N - x)) P hP
    (goldbachSieveDensity N) (goldbachSieveDensity_isMultiplicative N)
    (fun p hp _ => goldbachSieveDensity_prime_pos N p hp)
    (fun p hp _ => goldbachSieveDensity_prime_lt_one N p hp (fun _ => hN))

/-- A concrete finite denominator, independent of proof-valued sieve parameters. -/
def denominator (N P z : ℕ) : ℝ :=
  ∑ d ∈ P.divisors, if d ≤ z then
    goldbachSieveDensity N d *
      ∏ p ∈ d.primeFactors, (1 - goldbachSieveDensity N p)⁻¹ else 0

theorem normalizer_eq_denominator (N P z : ℕ) (hN : 2 ∣ N) (hP : Squarefree P) :
    SelbergOptimal.normalizer (sieve N P hN hP) z = denominator N P z := by
  unfold SelbergOptimal.normalizer denominator
  apply sum_congr rfl
  intro d hd
  rw [BoundingSieve.selbergTerms_apply]
  rfl

theorem denominator_pos (N P : ℕ) (hN : 2 ∣ N) (hP : Squarefree P)
    {z : ℕ} (hz : 1 ≤ z) : 0 < denominator N P z := by
  rw [← normalizer_eq_denominator N P z hN hP]
  exact SelbergOptimal.normalizer_pos _ hz

/-- The local error of this actual sieve is bounded by its actual root count. -/
theorem rem_bound (N P d : ℕ) (hN : 2 ∣ N) (hP : Squarefree P) [NeZero d] :
    |(sieve N P hN hP).rem d| ≤ goldbachSieveRootCount N d := by
  unfold sieve
  rw [PrimePairSieve.imageSieve_rem]
  simpa using goldbach_polynomial_count_density_discrepancy N d

/-- The polynomial root count yields the dimension-two factorizable remainder
bound required by the optimized logarithmic error estimate. -/
theorem rem_lcm_bound (N P : ℕ) (hN : 2 ∣ N) (hP : Squarefree P)
    (a : ℕ) (ha : a ∈ P.divisors) (b : ℕ) (hb : b ∈ P.divisors) :
    |(sieve N P hN hP).rem (Nat.lcm a b)| ≤
      (2 : ℝ) ^ a.primeFactors.card * (2 : ℝ) ^ b.primeFactors.card := by
  let : NeZero a := ⟨(Nat.pos_of_mem_divisors ha).ne'⟩
  let : NeZero b := ⟨(Nat.pos_of_mem_divisors hb).ne'⟩
  let : NeZero (Nat.lcm a b) := ⟨Nat.lcm_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  have ha2 := goldbachSieveRootCount_le_two_pow N a
    (hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors ha))
  have hb2 := goldbachSieveRootCount_le_two_pow N b
    (hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors hb))
  calc
    _ ≤ (goldbachSieveRootCount N (Nat.lcm a b) : ℝ) := rem_bound N P _ hN hP
    _ ≤ (goldbachSieveRootCount N a : ℝ) * goldbachSieveRootCount N b := by
      exact_mod_cast goldbachSieveRootCount_lcm_le N a b
    _ ≤ _ := by exact_mod_cast Nat.mul_le_mul ha2 hb2

/-- An unconditional, explicit finite upper sieve for ordered Goldbach pairs.
Only evenness, squarefreeness of the chosen sieving product, and `z ≥ 1` are
assumed. The remaining denominator is an actual finite arithmetic sum; no
prime-distribution or unproved remainder estimate is hidden in a premise. -/
theorem primePairs_le (N P : ℕ) (hN : 2 ∣ N) (hP : Squarefree P)
    {z : ℕ} (hz : 1 ≤ z) :
    ((PrimePairSieve.primePairs N).card : ℝ) ≤
      ((N - 1 : ℕ) : ℝ) / denominator N P z +
      (z : ℝ) ^ 2 * (1 + Real.log z) ^ 4 + 2 * P.primeFactors.card := by
  let s := sieve N P hN hP
  have he := SelbergOptimal.siftedSum_le_log_error s hz
    (fun a ha b hb => rem_lcm_bound N P hN hP a ha b hb)
  have hsum : s.siftedSum = ((PrimePairSieve.siftedPairs N P).card : ℝ) :=
    PrimePairSieve.imageSieve_siftedSum _ _ _ _ _ _ _ _
  have hmass : s.totalMass = ((N - 1 : ℕ) : ℝ) := by
    simp [s, sieve, PrimePairSieve.imageSieve]
  have hnorm : SelbergOptimal.normalizer s z = denominator N P z :=
    normalizer_eq_denominator N P z hN hP
  rw [hsum, hmass, hnorm] at he
  have hpairs : ((PrimePairSieve.primePairs N).card : ℝ) ≤
      (PrimePairSieve.siftedPairs N P).card + 2 * P.primeFactors.card := by
    exact_mod_cast PrimePairSieve.card_primePairs_le_sifted N P hP.ne_zero
  linarith

/-- With the primorial cutoff, the denominator is a sum over every squarefree
integer up to the cutoff, not an unspecified subset of them. -/
theorem denominator_primorial (N z : ℕ) :
    denominator N (primorial z) z =
      ∑ d ∈ Icc 1 z, if Squarefree d then
        goldbachSieveDensity N d *
          ∏ p ∈ d.primeFactors, (1 - goldbachSieveDensity N p)⁻¹ else 0 := by
  classical
  unfold denominator
  rw [← sum_filter]
  have hsets : (primorial z).divisors.filter (fun d => d ≤ z) =
      (Icc 1 z).filter Squarefree := by
    ext d
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨hd, hdz⟩
      exact ⟨⟨Nat.pos_of_mem_divisors hd, hdz⟩,
        (squarefree_primorial z).squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)⟩
    · rintro ⟨⟨hdpos, hdz⟩, hsq⟩
      exact ⟨Nat.mem_divisors.mpr
        ⟨hsq.dvd_primorial.trans (primorial_dvd_primorial hdz),
          primorial_ne_zero z⟩, hdz⟩
  rw [hsets, sum_filter]

/-- The explicit prime-pair sieve at the canonical primorial product. -/
theorem primePairs_le_primorial (N : ℕ) (hN : 2 ∣ N) {z : ℕ} (hz : 1 ≤ z) :
    ((PrimePairSieve.primePairs N).card : ℝ) ≤
      ((N - 1 : ℕ) : ℝ) / denominator N (primorial z) z +
      (z : ℝ) ^ 2 * (1 + Real.log z) ^ 4 + 2 * (Nat.primesLE z).card := by
  simpa only [primeFactors_primorial] using
    primePairs_le N (primorial z) hN (squarefree_primorial z) hz

end Problem337.GoldbachSelberg

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.SmoothRankin

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

/-- A finite nonnegative sum over smooth numbers is bounded by the finite
Euler product. Only the local prime-power series need to be summable. -/
theorem smooth_sum_le_euler_product
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (hf1 : f 1 = 1)
    (hmul : ∀ {m n}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hsum : ∀ {p : ℕ}, p.Prime → Summable (fun j : ℕ => ‖f (p ^ j)‖))
    (N : ℕ) (s : Finset ℕ) (hs : ∀ n ∈ s, n ∈ N.smoothNumbers) :
    (∑ n ∈ s, f n) ≤ ∏ p ∈ N.primesBelow, ∑' j : ℕ, f (p ^ j) := by
  classical
  obtain ⟨_, hprod⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    hf1 hmul hsum N
  calc
    (∑ n ∈ s, f n) = ∑ n ∈ s.subtype (fun n => n ∈ N.smoothNumbers), f n :=
      (Finset.sum_subtype_of_mem f hs).symm
    _ ≤ ∑' n : N.smoothNumbers, f n :=
      hprod.summable.sum_le_tsum _ (fun n _ => hf n)
    _ = ∏ p ∈ N.primesBelow, ∑' j : ℕ, f (p ^ j) := hprod.tsum_eq

/-- The elementary exponential weight used in Rankin's tail estimate. -/
theorem rankin_weight_bound {V β : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hn : Real.exp V ≤ (n : ℝ)) :
    1 ≤ Real.exp (-β * V) * (n : ℝ) ^ β := by
  have hpow := Real.rpow_le_rpow (le_of_lt (Real.exp_pos V)) hn hβ
  rw [← Real.exp_mul] at hpow
  have h := mul_le_mul_of_nonneg_left hpow (le_of_lt (Real.exp_pos (-β * V)))
  have hid : Real.exp (-β * V) * Real.exp (V * β) = 1 := by
    rw [← Real.exp_add]
    have : -β * V + V * β = 0 := by ring
    rw [this, Real.exp_zero]
  rwa [hid] at h

/-- Rankin's trick followed by a finite Euler product. This form applies to
`f n = τ(n)^r / n`; the local weight then has exponent `-1 + β`. -/
theorem smooth_rankin_bound
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (hf1 : f 1 = 1)
    (hmul : ∀ {m n}, Nat.Coprime m n → f (m * n) = f m * f n)
    {V β : ℝ} (hβ : 0 ≤ β)
    (hsum : ∀ {p : ℕ}, p.Prime →
      Summable (fun j : ℕ => ‖f (p ^ j) * ((p ^ j : ℕ) : ℝ) ^ β‖))
    (N : ℕ) (s : Finset ℕ) (hs : ∀ n ∈ s, n ∈ N.smoothNumbers)
    (hlarge : ∀ n ∈ s, Real.exp V ≤ (n : ℝ)) :
    (∑ n ∈ s, f n) ≤ Real.exp (-β * V) *
      (∏ p ∈ N.primesBelow, ∑' j : ℕ, f (p ^ j) * ((p ^ j : ℕ) : ℝ) ^ β) := by
  have hg : ∀ n : ℕ, 0 ≤ f n * (n : ℝ) ^ β := by
    intro n
    exact mul_nonneg (hf n) (Real.rpow_nonneg (Nat.cast_nonneg n) β)
  have hg1 : f 1 * (1 : ℝ) ^ β = 1 := by simp [hf1]
  have hgmul : ∀ {m n : ℕ}, Nat.Coprime m n →
      f (m * n) * ((m * n : ℕ) : ℝ) ^ β =
        (f m * (m : ℝ) ^ β) * (f n * (n : ℝ) ^ β) := by
    intro m n hmn
    rw [hmul hmn, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring
  have heuler := smooth_sum_le_euler_product (fun n => f n * (n : ℝ) ^ β)
    hg (by simpa using hg1) hgmul hsum N s hs
  calc
    (∑ n ∈ s, f n) ≤ ∑ n ∈ s, Real.exp (-β * V) * (f n * (n : ℝ) ^ β) := by
      apply Finset.sum_le_sum
      intro n hn
      have h := mul_le_mul_of_nonneg_left (rankin_weight_bound hβ (hlarge n hn)) (hf n)
      nlinarith
    _ = Real.exp (-β * V) * ∑ n ∈ s, f n * (n : ℝ) ^ β := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-β * V) *
        (∏ p ∈ N.primesBelow, ∑' j : ℕ, f (p ^ j) * ((p ^ j : ℕ) : ℝ) ^ β) :=
      mul_le_mul_of_nonneg_left heuler (le_of_lt (Real.exp_pos _))

/-- The multiplicative weight occurring in divisor harmonic moments. -/
def divisorHarmonicWeight (r n : ℕ) : ℝ :=
  (n.divisors.card : ℝ) ^ r / (n : ℝ)

theorem divisorHarmonicWeight_nonneg (r n : ℕ) : 0 ≤ divisorHarmonicWeight r n := by
  unfold divisorHarmonicWeight
  positivity

theorem divisorHarmonicWeight_one (r : ℕ) : divisorHarmonicWeight r 1 = 1 := by
  simp [divisorHarmonicWeight]

theorem divisorHarmonicWeight_mul (r : ℕ) {m n : ℕ} (h : m.Coprime n) :
    divisorHarmonicWeight r (m * n) = divisorHarmonicWeight r m * divisorHarmonicWeight r n := by
  simp only [divisorHarmonicWeight, h.card_divisors_mul, Nat.cast_mul, mul_pow]
  ring

theorem divisorHarmonicWeight_prime_power (r : ℕ) {p : ℕ} (hp : p.Prime) (j : ℕ)
    (β : ℝ) :
    divisorHarmonicWeight r (p ^ j) * ((p ^ j : ℕ) : ℝ) ^ β =
      ((j + 1 : ℕ) : ℝ) ^ r * ((p : ℝ) ^ (β - 1)) ^ j := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpow : (0 : ℝ) < (p : ℝ) ^ j := pow_pos hpR j
  simp only [divisorHarmonicWeight, Nat.divisors_prime_pow hp, Finset.card_map,
    Finset.card_range, Nat.cast_pow]
  rw [Real.rpow_pow_comm (le_of_lt hpR), Real.rpow_sub_one (ne_of_gt hpow)]
  ring

theorem summable_successor_pow_geometric (r : ℕ) {q : ℝ} (hq : 0 < q) (hqone : q < 1) :
    Summable (fun j : ℕ => ‖((j + 1 : ℕ) : ℝ) ^ r * q ^ j‖) := by
  have hnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hq] using hqone
  have h := (summable_norm_pow_mul_geometric_of_norm_lt_one r hnorm).comp_injective
    Nat.succ_injective
  have h' := h.mul_right q⁻¹
  apply h'.congr
  intro j
  change ‖((j + 1 : ℕ) : ℝ) ^ r * q ^ (j + 1)‖ * q⁻¹ =
    ‖((j + 1 : ℕ) : ℝ) ^ r * q ^ j‖
  rw [pow_succ, ← mul_assoc, norm_mul, Real.norm_eq_abs q, abs_of_pos hq]
  field_simp

theorem divisorHarmonicWeight_local_summable (r : ℕ) {β : ℝ} (hβ : β < 1)
    {p : ℕ} (hp : p.Prime) :
    Summable (fun j : ℕ => ‖divisorHarmonicWeight r (p ^ j) * ((p ^ j : ℕ) : ℝ) ^ β‖) := by
  simp_rw [divisorHarmonicWeight_prime_power r hp]
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact summable_successor_pow_geometric r (Real.rpow_pos_of_pos (by linarith) _)
    (Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith))

/-- Concrete smooth initial-interval Rankin estimate for any natural moment order. -/
theorem divisor_smooth_rankin_bound (r : ℕ) {V β : ℝ} (hβ : 0 ≤ β) (hβone : β < 1)
    (N : ℕ) (s : Finset ℕ) (hs : ∀ n ∈ s, n ∈ N.smoothNumbers)
    (hlarge : ∀ n ∈ s, Real.exp V ≤ (n : ℝ)) :
    (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤ Real.exp (-β * V) *
      (∏ p ∈ N.primesBelow, ∑' j : ℕ,
        ((j + 1 : ℕ) : ℝ) ^ r * ((p : ℝ) ^ (β - 1)) ^ j) := by
  have h := smooth_rankin_bound (divisorHarmonicWeight r) (divisorHarmonicWeight_nonneg r)
    (divisorHarmonicWeight_one r) (divisorHarmonicWeight_mul r) hβ
    (divisorHarmonicWeight_local_summable r hβone) N s hs hlarge
  change (∑ n ∈ s, divisorHarmonicWeight r n) ≤ _
  apply h.trans_eq
  apply congrArg (fun x : ℝ => Real.exp (-β * V) * x)
  apply Finset.prod_congr rfl
  intro p hp
  apply tsum_congr
  intro j
  exact divisorHarmonicWeight_prime_power r (Nat.prime_of_mem_primesBelow hp) j β

/-- The unweighted finite Euler-product bound for harmonic divisor moments. -/
theorem divisor_harmonic_sum_le_euler_product (r N : ℕ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, n ∈ N.smoothNumbers) :
    (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤
      ∏ p ∈ N.primesBelow, ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) ^ r * ((p : ℝ)⁻¹) ^ j := by
  have hlarge : ∀ n ∈ s, Real.exp (0 : ℝ) ≤ (n : ℝ) := by
    intro n hn
    rw [Real.exp_zero]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ne_zero_of_mem_smoothNumbers (hs n hn))
  simpa [Real.rpow_neg_one] using divisor_smooth_rankin_bound r (le_refl (0 : ℝ)) (by norm_num : (0 : ℝ) < 1)
    N s hs hlarge

/-- A local Euler factor, in the indexing convenient for Rankin's trick. -/
def divisorEulerFactor (r p : ℕ) (β : ℝ) : ℝ :=
  ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) ^ r * ((p : ℝ) ^ (β - 1)) ^ j

theorem divisorEulerFactor_one_le (r : ℕ) {p : ℕ} (hp : p.Prime) {β : ℝ}
    (hβ : β < 1) : 1 ≤ divisorEulerFactor r p β := by
  have hs := divisorHarmonicWeight_local_summable r hβ hp
  simp_rw [divisorHarmonicWeight_prime_power r hp] at hs
  have h := hs.of_norm.sum_le_tsum {0} (by
    intro j _
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    positivity)
  simpa [divisorEulerFactor] using h

/-- Logarithmic local-factor estimates turn the Rankin Euler product into a
single exponential. This is the precise smooth initial-interval bound used in the
divisor-moment decomposition. -/
theorem divisor_smooth_rankin_log_bound (r : ℕ) {V β C : ℝ}
    (hβ : 0 ≤ β) (hβone : β < 1) (N : ℕ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, n ∈ N.smoothNumbers)
    (hlarge : ∀ n ∈ s, Real.exp V ≤ (n : ℝ))
    (hlocal : ∀ p ∈ N.primesBelow,
      Real.log (divisorEulerFactor r p β) ≤ C * (p : ℝ) ^ (β - 1)) :
    (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤
      Real.exp (-β * V + C * ∑ p ∈ N.primesBelow, (p : ℝ) ^ (β - 1)) := by
  have hpos : ∀ p ∈ N.primesBelow, 0 < divisorEulerFactor r p β := by
    intro p hp
    have := divisorEulerFactor_one_le r (Nat.prime_of_mem_primesBelow hp) hβone
    linarith
  have hprodpos : 0 < ∏ p ∈ N.primesBelow, divisorEulerFactor r p β := Finset.prod_pos hpos
  have hlog : Real.log (∏ p ∈ N.primesBelow, divisorEulerFactor r p β) ≤
      C * ∑ p ∈ N.primesBelow, (p : ℝ) ^ (β - 1) := by
    rw [Real.log_prod (fun p hp => ne_of_gt (hpos p hp)), Finset.mul_sum]
    exact Finset.sum_le_sum hlocal
  have hprod := (Real.log_le_iff_le_exp hprodpos).mp hlog
  have hrank := divisor_smooth_rankin_bound r hβ hβone N s hs hlarge
  change (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤
    Real.exp (-β * V) * ∏ p ∈ N.primesBelow, divisorEulerFactor r p β at hrank
  calc
    (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤
        Real.exp (-β * V) * ∏ p ∈ N.primesBelow, divisorEulerFactor r p β := hrank
    _ ≤ Real.exp (-β * V) *
        Real.exp (C * ∑ p ∈ N.primesBelow, (p : ℝ) ^ (β - 1)) :=
      mul_le_mul_of_nonneg_left hprod (le_of_lt (Real.exp_pos _))
    _ = Real.exp (-β * V + C * ∑ p ∈ N.primesBelow, (p : ℝ) ^ (β - 1)) :=
      (Real.exp_add _ _).symm

end Problem337

end

end OAI


open Finset

namespace CentralSelberg

theorem prime_log_mass (m : ℕ) (hm : 0 < m) :
    (∑ p ∈ m.primeFactors, Real.log (p:ℝ)) ≤ Real.log m := by
  rw [← Real.log_prod (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)]
  rw [← Nat.cast_prod]
  apply Real.log_le_log
  · exact_mod_cast Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
  · exact_mod_cast Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m)

/-- An elementary upper bound for the weighted prime harmonic sum via counting multiples. -/
theorem weighted_harmonic (y : ℕ) (hy : 1 ≤ y) :
    (∑ p ∈ y.primesLE, Real.log (p:ℝ)/(p:ℝ)) ≤ 2*Real.log y := by
  let T := Finset.Ioc 0 y
  have hcnt (p : ℕ) : ((T.filter (p ∣ ·)).card:ℝ) = (y/p:ℕ) := by
    exact_mod_cast Nat.Ioc_filter_dvd_card_eq_div y p
  have hsum : (∑ p ∈ y.primesLE, ((y/p:ℕ):ℝ)*Real.log p) ≤ (y:ℝ)*Real.log y := by
    calc
      _ = ∑ p ∈ y.primesLE, ∑ k ∈ T, if p ∣ k then Real.log p else 0 := by
        refine sum_congr rfl fun p _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcnt]
      _ = ∑ k ∈ T, ∑ p ∈ y.primesLE, if p ∣ k then Real.log p else 0 := Finset.sum_comm
      _ ≤ ∑ _k ∈ T, Real.log y := by
        refine sum_le_sum fun k hk => ?_
        obtain ⟨hkpos, hky⟩ := Finset.mem_Ioc.mp hk
        rw [← Finset.sum_filter]
        have heq : (y.primesLE.filter (· ∣ k)) = k.primeFactors := by
          ext p
          simp only [Finset.mem_filter, Nat.mem_primesLE, Nat.mem_primeFactors]
          exact ⟨fun h => ⟨h.1.2, h.2, hkpos.ne'⟩, fun h => ⟨⟨(Nat.le_of_dvd hkpos h.2.1).trans hky, h.1⟩, h.2.1⟩⟩
        rw [heq]
        exact (prime_log_mass _ hkpos).trans (Real.log_le_log (by exact_mod_cast hkpos) (by exact_mod_cast hky))
      _ = _ := by simp [T]
  have hyR : (0:ℝ) < y := by exact_mod_cast hy
  apply (le_of_mul_le_mul_left (a := (y:ℝ)) ?_ hyR)
  calc
    _ = ∑ p ∈ y.primesLE, (y:ℝ)*(Real.log p/p) := Finset.mul_sum ..
    _ ≤ ∑ p ∈ y.primesLE, 2*(((y/p:ℕ):ℝ)*Real.log p) := by
      refine sum_le_sum fun p hp => ?_
      obtain ⟨hpy,hprime⟩ := Nat.mem_primesLE.mp hp
      have hp0 : (0:ℝ) < p := by exact_mod_cast hprime.pos
      have hd : 1 ≤ y/p := (Nat.le_div_iff_mul_le hprime.pos).mpr (by simpa)
      have hdiv : y ≤ 2*((y/p)*p) := by
        have he := Nat.div_add_mod y p
        have hr := Nat.mod_lt y hprime.pos
        have hpq := Nat.mul_le_mul_right p hd
        rw [Nat.mul_comm p] at he
        omega
      have hr : (y:ℝ) ≤ 2*(((y/p:ℕ):ℝ)*p) := by exact_mod_cast hdiv
      rw [← mul_div_assoc, div_le_iff₀ hp0]
      calc
        _ ≤ (2*(((y/p:ℕ):ℝ)*p))*Real.log p :=
          mul_le_mul_of_nonneg_right hr (Real.log_nonneg (by exact_mod_cast hprime.one_le))
        _ = _ := by ring
    _ ≤ _ := by rw [← Finset.mul_sum]; linarith

end CentralSelberg


open Finset
namespace CentralSelberg

/-- First logarithmic moment of a finite Euler product. -/
theorem powerset_moment (s : Finset ℕ) (g l : ℕ → ℝ)
    (hg : ∀ i ∈ s, 0 ≤ g i) :
    (∑ t ∈ s.powerset, (∏ i ∈ t, g i)*(∑ i ∈ t, l i)) =
      (∏ i ∈ s, (1+g i)) * (∑ i ∈ s, g i/(1+g i)*l i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hn : 1+g a ≠ 0 := by have := hg a (Finset.mem_insert_self ..); linarith
    have hi := ih (fun p hp => hg p (mem_insert_of_mem hp))
    rw [Finset.sum_powerset_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hexp : (∑ t ∈ s.powerset, (∏ i ∈ insert a t, g i)*(∑ i ∈ insert a t, l i)) =
        g a*l a * (∏ i ∈ s, (1+g i)) +
        g a * (∑ t ∈ s.powerset, (∏ i ∈ t, g i)*(∑ i ∈ t, l i)) := by
      rw [Finset.prod_one_add s, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t ht => ?_
      have hat : a ∉ t := fun h => ha ((Finset.mem_powerset.mp ht) h)
      rw [Finset.prod_insert hat, Finset.sum_insert hat]
      ring
    rw [hexp, hi]
    field_simp
    ring

end CentralSelberg


open Finset
open OAI.Problem337
namespace CentralSelberg
noncomputable section

def rho (n p : ℕ) := goldbachSieveDensity n p

def wgt (n p : ℕ) : ℝ := rho n p * (1-rho n p)⁻¹

def loc (n p : ℕ) : ℝ := if 2<p ∧ p∣n then 1+1/((p:ℝ)-2) else 1

theorem rho_bounds (n : ℕ) (hn : 2∣n) (p : ℕ) (hp : p.Prime) :
    0 < rho n p ∧ rho n p < 1 :=
  ⟨goldbachSieveDensity_prime_pos n p hp, goldbachSieveDensity_prime_lt_one n p hp (fun _ => hn)⟩

theorem wgt_pos (n : ℕ) (hn : 2∣n) (p : ℕ) (hp : p.Prime) : 0 < wgt n p := by
  have h := rho_bounds n hn p hp
  exact mul_pos h.1 (inv_pos.mpr (by linarith [h.2]))

theorem wgt_ratio (n : ℕ) (hn : 2∣n) (p : ℕ) (hp : p.Prime) :
    wgt n p/(1+wgt n p) = rho n p := by
  have h := (rho_bounds n hn p hp).2
  have hpos := wgt_pos n hn p hp
  unfold wgt at *
  field_simp
  ring

theorem harmonic_product (y : ℕ) :
    Real.log ((y:ℝ)+1) ≤ ∏ p ∈ y.primesLE, (1-(p:ℝ)⁻¹)⁻¹ := by
  let S := Finset.Icc 1 y
  have hsm (k : ℕ) (hk : k ∈ S) : k ∈ (y+1).smoothNumbers :=
    Nat.mem_smoothNumbers_of_lt (Finset.mem_Icc.mp hk).1 (by have := (Finset.mem_Icc.mp hk).2; omega)
  have H := divisor_harmonic_sum_le_euler_product 0 (y+1) S hsm
  simp only [pow_zero, one_mul, one_div] at H
  have hgeo (p : ℕ) (hp : p∈y.primesLE) : (∑' j : ℕ, ((p:ℝ)⁻¹)^j) = (1-(p:ℝ)⁻¹)⁻¹ := by
    apply tsum_geometric_of_lt_one
    · positivity
    · exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt)
  calc
    _ ≤ (harmonic y:ℝ) := by simpa using log_add_one_le_harmonic y
    _ = ∑ k ∈ S, (k:ℝ)⁻¹ := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      rfl
    _ ≤ _ := H.trans_eq (Finset.prod_congr rfl hgeo)

end
end CentralSelberg


open Finset OAI.Problem337
namespace CentralSelberg
noncomputable section

def singular (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors.filter (fun p => 2<p), (1+1/((p:ℝ)-2))

theorem factor_one_le (n p : ℕ) : 1 ≤ loc n p := by
  unfold loc
  split
  · rename_i h
    have : (2:ℝ)<p := by exact_mod_cast h.1
    linarith [show 0≤1/((p:ℝ)-2) by positivity]
  · rfl

theorem singular_one_le (n : ℕ) : 1 ≤ singular n := by
  apply Finset.one_le_prod₀
  intro p hp
  have h : (2:ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2
  linarith [show 0 ≤ 1/((p:ℝ)-2) by positivity]

theorem local_correction (n y : ℕ) (hn : 0<n) :
    (∏ p ∈ y.primesLE, loc n p) ≤ singular n := by
  let T := y.primesLE.filter (fun p => 2<p ∧ p∣n)
  have sub : T ⊆ n.primeFactors.filter (fun p => 2<p) := by
    intro p hp
    obtain ⟨h,ho,hd⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primesLE h,hd,hn.ne'⟩,ho⟩
  change (∏ p ∈ y.primesLE, if 2<p ∧ p∣n then _ else 1) ≤ _
  rw [← Finset.prod_filter]
  exact Finset.prod_le_prod_of_subset_of_one_le₀ sub (fun p hp => by
    have h : (2:ℝ)<p := by exact_mod_cast (Finset.mem_filter.mp hp).2.1
    positivity) (fun p hp _ => by
    have h : (2:ℝ)<p := by exact_mod_cast (Finset.mem_filter.mp hp).2
    linarith [show 0 ≤ 1/((p:ℝ)-2) by positivity])

theorem euler_mass (n y : ℕ) (hn : 2∣n) (hnp : 0<n) :
    (Real.log ((y:ℝ)+1))^2 ≤ 2*singular n*(∏ p ∈ y.primesLE, (1+wgt n p)) := by
  let T := y.primesLE
  have hloc (p : ℕ) (hp : p ∈ T) :
      ((1-(p:ℝ)⁻¹)⁻¹)^2 ≤ (if p=2 then 2 else 1)*loc n p*(1+wgt n p) := by
    have hpP := Nat.prime_of_mem_primesLE hp
    have hr := goldbachSieveDensity_prime n p hpP
    unfold wgt rho loc
    rw [hr]
    by_cases h2 : p=2
    · subst p; norm_num [hn]
    · have hh : 2 < p := by have := hpP.two_le; omega
      have hrp : (2:ℝ) < p := by exact_mod_cast hh
      have hp0 : (0:ℝ)<p := by linarith
      by_cases hd : p∣n
      · simp only [hh,hd,h2,if_true,true_and,if_false,one_mul]
        have hp1 : 0 < (p:ℝ) - 1 := by linarith
        have hp2 : 0 < (p:ℝ) - 2 := by linarith
        field_simp [hp1, hp2]
        nlinarith [sq_nonneg (p:ℝ)]
      · simp only [hh,hd,h2,if_true,true_and,if_false,one_mul]
        have hp1 : 0 < (p:ℝ) - 1 := by linarith
        have hp2 : 0 < (p:ℝ) - 2 := by linarith
        field_simp [hp1, hp2]
        nlinarith [sq_nonneg (p:ℝ)]
  have htwo : (∏ p ∈ T, (if p=2 then (2:ℝ) else 1)) ≤ 2 := by
    rw [Finset.prod_ite_eq']; split <;> norm_num
  have hpos := Finset.prod_nonneg (s := T) (f := fun p => 1+wgt n p) (fun p hp => by
    have := wgt_pos n hn p (Nat.prime_of_mem_primesLE hp); linarith)
  have hcorr := local_correction n y hnp
  have hcpos := Finset.prod_nonneg (s := T) (f := loc n)
    (fun p hp => by linarith [factor_one_le n p])
  have htwo' := mul_le_mul htwo hcorr hcpos (by norm_num : (0:ℝ) ≤ 2)
  calc
    _ ≤ (∏ p ∈ T, (1-(p:ℝ)⁻¹)⁻¹)^2 :=
      pow_le_pow_left₀ (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) y])) (harmonic_product y) _
    _ = ∏ p ∈ T, ((1-(p:ℝ)⁻¹)⁻¹)^2 := (Finset.prod_pow ..).symm
    _ ≤ ∏ p ∈ T, (if p=2 then 2 else 1)*loc n p*(1+wgt n p) := Finset.prod_le_prod₀
      (fun p hp => sq_nonneg _) hloc
    _ ≤ _ := by
      simp only [Finset.prod_mul_distrib]
      exact mul_le_mul_of_nonneg_right htwo' hpos

end
end CentralSelberg


open Finset OAI.Problem337
namespace CentralSelberg
noncomputable section

def mass (n y : ℕ) : ℝ := ∏ p ∈ y.primesLE, (1+wgt n p)
def index (t : Finset ℕ) : ℕ := ∏ p ∈ t, p
def weight (n : ℕ) (t : Finset ℕ) : ℝ := ∏ p ∈ t, wgt n p

theorem denominator_as_sum (n y z : ℕ) :
    GoldbachSelberg.denominator n (primorial y) z =
      ∑ t ∈ y.primesLE.powerset, if index t ≤ z then weight n t else 0 := by
  classical
  let P := primorial y
  have prime (t : Finset ℕ) (ht : t∈y.primesLE.powerset) : ∀ p∈t, p.Prime :=
    fun p hp => Nat.prime_of_mem_primesLE ((Finset.mem_powerset.mp ht) hp)
  have hfac (t : Finset ℕ) (ht : t∈y.primesLE.powerset) :
      (index t).primeFactors=t := Nat.primeFactors_prod (prime t ht)
  have hmap : P.divisors = y.primesLE.powerset.image index := by
    ext d
    constructor
    · intro hd
      have hsq := (squarefree_primorial y).squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
      have hmono := Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) (primorial_ne_zero y)
      rw [primeFactors_primorial] at hmono
      exact Finset.mem_image.mpr ⟨d.primeFactors, Finset.mem_powerset.mpr hmono, Nat.prod_primeFactors_of_squarefree hsq⟩
    · rintro hd
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hd
      exact Nat.mem_divisors.mpr ⟨Finset.prod_dvd_prod_of_subset _ _ _ (Finset.mem_powerset.mp ht),primorial_ne_zero y⟩
  unfold GoldbachSelberg.denominator
  change (∑ d ∈ P.divisors, _) = _
  rw [hmap, Finset.sum_image (fun a ha b hb hh => (hfac a ha).symm.trans ((congrArg Nat.primeFactors hh).trans (hfac b hb)))]
  refine Finset.sum_congr rfl fun t ht => ?_
  split_ifs
  · rw [hfac t ht, index, (goldbachSieveDensity_isMultiplicative n).map_prod_of_prime t (prime t ht)]
    exact (Finset.prod_mul_distrib).symm
  · rfl

theorem retained (n y : ℕ) (hn : 2∣n) (hy : 2≤y) :
    mass n y ≤ 2 * GoldbachSelberg.denominator n (primorial y) (y^8) := by
  let T := y.primesLE.powerset
  let W := weight n
  let D := GoldbachSelberg.denominator n (primorial y) (y^8)
  have wp (t : Finset ℕ) (ht : t ∈ T) : 0 ≤ W t :=
    Finset.prod_nonneg fun p hp => (wgt_pos n hn p (Nat.prime_of_mem_primesLE ((Finset.mem_powerset.mp ht) hp))).le
  have total : (∑ t ∈ T, W t) = mass n y := (Finset.prod_one_add _).symm
  have heavy_point (t : Finset ℕ) (ht : t ∈ T) :
      (if y^8 < index t then W t else 0)*(8*Real.log y) ≤ W t*Real.log (index t) := by
    have hip : 0 < index t := Finset.prod_pos fun p hp =>
      (Nat.prime_of_mem_primesLE ((Finset.mem_powerset.mp ht) hp)).pos
    split
    · rename_i hl
      apply mul_le_mul_of_nonneg_left _ (wp t ht)
      have hlog := Real.log_le_log (show (0:ℝ) < ((y^8:ℕ):ℝ) by positivity) (show ((y^8:ℕ):ℝ) ≤ index t by exact_mod_cast hl.le)
      simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] using hlog
    · rw [zero_mul]
      exact mul_nonneg (wp t ht) (Real.log_nonneg (by exact_mod_cast hip))
  have mean := powerset_moment y.primesLE (wgt n) (fun p => Real.log (p:ℝ))
    (fun p hp => (wgt_pos n hn p (Nat.prime_of_mem_primesLE hp)).le)
  have hsumlog (t : Finset ℕ) (ht : t∈T) :
      Real.log (index t) = ∑ p ∈ t, Real.log (p:ℝ) := by
    unfold index
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp; exact_mod_cast (Nat.prime_of_mem_primesLE ((Finset.mem_powerset.mp ht) hp)).ne_zero
  have bound : (∑ p ∈ y.primesLE, wgt n p/(1+wgt n p)*Real.log p) ≤ 4*Real.log y := by
    calc
      _ ≤ ∑ p ∈ y.primesLE, 2*(Real.log p/p) := by
        refine sum_le_sum fun p hp => ?_
        have hpP := Nat.prime_of_mem_primesLE hp
        have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpP.one_le)
        rw [wgt_ratio n hn p hpP]
        unfold rho
        rw [goldbachSieveDensity_prime n p hpP]
        split <;> ring_nf <;> first | rfl | nlinarith [mul_nonneg hlog (inv_nonneg.mpr (Nat.cast_nonneg p : (0:ℝ) ≤ _))]
      _ ≤ _ := by rw [←Finset.mul_sum]; linarith [weighted_harmonic y (by omega)]
  have hmass : 0 ≤ mass n y := Finset.prod_nonneg (fun p hp => by
    linarith [wgt_pos n hn p (Nat.prime_of_mem_primesLE hp)])
  have moment : (∑ t ∈ T, W t*Real.log (index t)) ≤ mass n y * (4*Real.log y) := by
    calc
      _ = ∑ t ∈ y.primesLE.powerset, (∏ p ∈ t, wgt n p)*(∑ p ∈ t, Real.log p) :=
        sum_congr rfl (fun t ht => by rw [hsumlog t ht]; rfl)
      _ = _ := mean
      _ ≤ _ := mul_le_mul_of_nonneg_left bound hmass
  have hdiff : (∑ t ∈ T, if y^8 < index t then W t else 0) = mass n y - D := by
    rw [← total, show D = _ from denominator_as_sum n y (y^8), ← Finset.sum_sub_distrib]
    apply sum_congr rfl; intro t _; by_cases h : index t ≤ y^8 <;> simp [h,not_lt.mpr,lt_of_not_ge,W]
  have hh := (sum_le_sum heavy_point).trans moment
  rw [← Finset.sum_mul, hdiff] at hh
  have hl : 0 < Real.log y := Real.log_pos (by exact_mod_cast (show 1<y by omega))
  change mass n y ≤ 2*D
  apply (le_of_mul_le_mul_right (a := Real.log y) ?_ hl)
  linarith only [hh]

end
end CentralSelberg


open Filter Topology
namespace CentralSelberg

/-- A small prime cutoff with enough logarithmic length for the denominator. -/
theorem scales :
    ∀ᶠ n : ℕ in atTop, ∃ y : ℕ, 2≤y ∧
       Real.log (n:ℝ) ≤ 32*Real.log ((y:ℝ)+1) ∧
       (((y^8:ℕ):ℝ)^2*(1+Real.log (y^8:ℕ))^4 + 2*(y:ℝ)) * (Real.log n)^2 ≤ 18*n := by
  have hs := (isLittleO_log_rpow_rpow_atTop (6:ℝ) (by norm_num : (0:ℝ)<1/2)).bound (by norm_num : (0:ℝ)<1)
  have hs' := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hs
  have hl := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1
  filter_upwards [hs',hl,eventually_ge_atTop (2^32:ℕ)] with n hn hlog hn32
  change 1 ≤ Real.log (n:ℝ) at hlog
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hn1 : 1 ≤ (n:ℝ) := by linarith [show (2:ℝ)^32 ≤ n by exact_mod_cast hn32]
  have hbig : (Real.log n)^6 ≤ Real.sqrt n := by
    have hr : (n:ℝ)^(1/2:ℝ) = Real.sqrt n := (Real.sqrt_eq_rpow _).symm
    simpa only [Real.norm_eq_abs, Real.rpow_natCast_mul, Real.rpow_ofNat, abs_of_nonneg (by positivity : 0≤(Real.log n)^6),
      abs_of_nonneg (Real.rpow_nonneg hn0.le _), one_mul, hr, abs_of_nonneg (Real.sqrt_nonneg _)] using hn
  let u : ℝ := (n:ℝ)^(1/32:ℝ)
  let y := ⌊u⌋₊
  have hu : 0≤u := Real.rpow_nonneg hn0.le _
  have hu32 : u^32 = n := by
    rw [show u^32 = (n:ℝ)^((1/32:ℝ)*32) from (Real.rpow_mul_natCast hn0.le _ _).symm]
    norm_num
  have hy2 : 2≤y := by
    apply (Nat.le_floor_iff hu).mpr
    by_contra! h
    have hp := pow_lt_pow_left₀ h hu (by decide : 32≠0)
    rw [hu32] at hp
    exact (not_lt_of_ge (show (2:ℝ)^32 ≤ n by exact_mod_cast hn32)) hp
  have hyp : (0:ℝ)<y := by exact_mod_cast (show 0<y by omega)
  have hyr : (1:ℝ)≤y := by exact_mod_cast (show 1≤y by omega)
  have hlow := pow_le_pow_left₀ hyp.le (Nat.floor_le hu : (y:ℝ) ≤ u) 32
  have hhigh := pow_le_pow_left₀ hu (Nat.lt_floor_add_one u).le 32
  rw [hu32] at hlow hhigh
  have hylog : Real.log (n:ℝ) ≤ 32*Real.log ((y:ℝ)+1) := by
    have hh := Real.log_le_log hn0 hhigh
    simpa only [Real.log_pow, Nat.cast_ofNat, y] using hh
  have hy16 : (y:ℝ)^16 ≤ Real.sqrt n := by
    apply (Real.le_sqrt (by positivity) hn0.le).mpr
    convert hlow using 1 <;> ring
  have hy1 : (y:ℝ) ≤ Real.sqrt n := by
    exact (le_self_pow₀ hyr (by decide : 16≠0)).trans hy16
  have hly : Real.log ((y^8:ℕ):ℝ) ≤ Real.log n := by
    apply Real.log_le_log (by positivity)
    rw [Nat.cast_pow]
    exact (pow_le_pow_right₀ hyr (by decide : 8≤32)).trans hlow
  have hp4 : (1+Real.log ((y^8:ℕ):ℝ))^4 ≤ (2*Real.log n)^4 :=
    pow_le_pow_left₀ (by have := Real.log_nonneg (show (1:ℝ)≤(y^8:ℕ) by exact_mod_cast (Nat.one_le_pow _ _ (by omega : 1≤y))); linarith) (by linarith) _
  rw [Nat.cast_pow] at hp4
  have hsqr := Real.sq_sqrt hn0.le
  have hmain : Real.sqrt n*(Real.log n)^6 ≤ n := by nlinarith [mul_le_mul_of_nonneg_left hbig (Real.sqrt_nonneg n)]
  have hminor : Real.sqrt n*(Real.log n)^2 ≤ n :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hlog (by decide : 2≤6)) (Real.sqrt_nonneg n)).trans hmain
  refine ⟨y,hy2,hylog,?_⟩
  rw [Nat.cast_pow]
  calc
    _ ≤ (Real.sqrt n*(2*Real.log n)^4 + 2*Real.sqrt n)*(Real.log n)^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply add_le_add _ (by linarith only [hy1])
      apply mul_le_mul (by convert hy16 using 1 <;> ring) hp4 (by positivity) (Real.sqrt_nonneg n)
    _ ≤ _ := by linarith only [hmain,hminor]

end CentralSelberg

open Finset Filter OAI.Problem337
namespace CentralSelberg
noncomputable section

def w (k : ℕ) : ℝ := if k.Prime then Real.log k else 0
def C (n : ℕ) : ℝ := ∑ p ∈ (range (n+1)).filter (fun p => n ≤ 3*p ∧ 3*p ≤ 2*n), w p*w (n-p)

theorem center_card (n : ℕ) (hn : 2 ≤ n) : C n ≤ ((PrimePairSieve.primePairs n).card:ℝ)*(Real.log n)^2 := by
  let T := (range (n+1)).filter (fun p => n ≤ 3*p ∧ 3*p ≤ 2*n)
  have hw (k : ℕ) (hk : k.Prime) : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk.one_le)
  calc
    _ ≤ ∑ p ∈ T, if p∈PrimePairSieve.primePairs n then (Real.log n)^2 else 0 := by
      refine sum_le_sum fun p hp => ?_
      obtain ⟨hpx,h1,h2⟩ := Finset.mem_filter.mp hp
      have hp' := Finset.mem_range.mp hpx
      by_cases hpP : p.Prime
      · by_cases hqP : (n-p).Prime
        · have mem : p∈PrimePairSieve.primePairs n := Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨hpP.one_le, by have := hqP.one_le; omega⟩, hpP,hqP⟩
          rw [if_pos mem, w, if_pos hpP, w, if_pos hqP, pow_two]
          exact mul_le_mul
            (Real.log_le_log (by exact_mod_cast hpP.pos) (by exact_mod_cast (show p≤n by omega)))
            (Real.log_le_log (by exact_mod_cast hqP.pos) (by exact_mod_cast Nat.sub_le n p))
            (hw _ hqP) (Real.log_nonneg (by exact_mod_cast (show 1≤n by omega)))
        · simp [w,hqP,PrimePairSieve.primePairs]
      · simp [w,hpP,PrimePairSieve.primePairs]
    _ = ((T.filter (·∈PrimePairSieve.primePairs n)).card:ℝ)*(Real.log n)^2 := by rw [←sum_filter]; simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_card (fun p hp => (mem_filter.mp hp).2))) (sq_nonneg _)

theorem central_upper :
    ∃ K : ℝ, 0<K ∧ ∃ X : ℕ, ∀ n≥X, Even n → C n ≤ K*(n:ℝ)* singular n := by
  obtain ⟨X,hX⟩ := eventually_atTop.mp scales
  refine ⟨4114,by norm_num,max X 2,?_⟩
  intro n hn he
  have hn2 : 2 ≤ n := (le_max_right ..).trans hn
  have hn0 : 0<n := by omega
  obtain ⟨y,hy,hlog,herr⟩ := hX n ((le_max_left ..).trans hn)
  have he' : 2∣n := even_iff_two_dvd.mp he
  have zpos : 1≤ y^8 := Nat.one_le_pow _ _ (by omega)
  let D := GoldbachSelberg.denominator n (primorial y) (y^8)
  have hD : 0<D := GoldbachSelberg.denominator_pos n _ he' (squarefree_primorial _) zpos
  have hsing := singular_one_le n
  have hDen : (Real.log n)^2 ≤ 4096 * singular n * D := by
    have hp : 0≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1≤n by omega))
    have hsq := pow_le_pow_left₀ hp hlog 2
    have hEu := euler_mass n y he' hn0
    have hcut := retained n y he' hy
    change _ ≤ 2*singular n * mass n y at hEu
    change mass n y ≤ 2*D at hcut
    nlinarith only [hsq,hEu,mul_le_mul_of_nonneg_left hcut (a := singular n) (by linarith)]
  have first : (((n-1:ℕ):ℝ)/D)*(Real.log n)^2 ≤ 4096*(n:ℝ)*singular n := by
    have hnle : ((n-1:ℕ):ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
    calc
      _ ≤ ((n:ℝ)/D)*(Real.log n)^2 := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hnle hD.le) (sq_nonneg _)
      _ ≤ ((n:ℝ)/D)*(4096*singular n*D) := mul_le_mul_of_nonneg_left hDen (by positivity)
      _ = _ := by field_simp
  have hcard : ((Nat.primesLE y).card:ℝ) ≤ y := by
    exact_mod_cast Finset.card_le_card (s := y.primesLE) (t := Icc 1 y) (fun p hp =>
      Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE hp).one_le,(Nat.mem_primesLE.mp hp).1⟩) |>.trans_eq (by simp)
  have hs := GoldbachSelberg.primePairs_le n (primorial y) he' (squarefree_primorial _) zpos
  rw [primeFactors_primorial] at hs
  change _ ≤ ((n-1:ℕ):ℝ)/D + _ + _ at hs
  have hb := center_card n hn2
  have heP := mul_le_mul_of_nonneg_right hs (sq_nonneg (Real.log n))
  have hbc := mul_le_mul_of_nonneg_right hcard (sq_nonneg (Real.log n))
  have hsn := mul_le_mul_of_nonneg_left hsing (Nat.cast_nonneg (α:=ℝ) n)
  nlinarith only [hb, heP, hbc, herr, first, hsn]

end
end CentralSelberg


open Finset OAI.Problem337
namespace ShiftSieve
noncomputable section

/-- Shifted prime pairs `m`, `m + d` with `m` in a window. -/
def shiftPairs (a Z d : ℕ) : Finset ℕ :=
  (Icc a (a+Z)).filter (fun m => m.Prime ∧ (m+d).Prime)

theorem shift_dvd_iff (d e m : ℕ) :
    e ∣ m*(m+d) ↔
      ((m+d : ℕ) : ZMod e) * ((d : ZMod e) - ((m+d : ℕ) : ZMod e)) = 0 := by
  have h : ((m+d : ℕ) : ZMod e) * ((d : ZMod e) - ((m+d : ℕ) : ZMod e)) =
      -((m*(m+d) : ℕ) : ZMod e) := by
    push_cast; ring
  rw [h, neg_eq_zero, ZMod.natCast_eq_zero_iff]

theorem shift_count_discrepancy (a Z d e : ℕ) [NeZero e] :
    |(((Icc a (a+Z)).filter (fun m => e ∣ m*(m+d))).card : ℝ) -
      goldbachSieveDensity d e * ((Z+1 : ℕ) : ℝ)| ≤ goldbachSieveRootCount d e := by
  classical
  have hI : Icc a (a+Z) = Ico a (a+(Z+1)) := by
    ext n; simp only [mem_Icc, mem_Ico]; omega
  have hcard : ((Icc a (a+Z)).filter (fun m => e ∣ m*(m+d))).card =
      ((Ico (a+d) ((a+d)+(Z+1))).filter
        (fun n : ℕ => (n : ZMod e) * ((d : ZMod e) - (n : ZMod e)) = 0)).card := by
    rw [hI]
    apply Finset.card_bij (fun m _ => m + d)
    · intro m hm
      simp only [mem_filter, mem_Ico] at hm ⊢
      exact ⟨by omega, (shift_dvd_iff d e m).mp hm.2⟩
    · intro m1 _ m2 _ h
      omega
    · intro n hn
      simp only [mem_filter, mem_Ico] at hn
      refine ⟨n - d, ?_, by omega⟩
      simp only [mem_filter, mem_Ico]
      have hnd : n - d + d = n := by omega
      refine ⟨by omega, ?_⟩
      rw [shift_dvd_iff, hnd]
      exact hn.2
  have h := zmod_predicate_Ico_discrepancy e
    (fun x : ZMod e => x * ((d : ZMod e) - x) = 0) (a+d) (Z+1)
  have e1 : goldbachSieveDensity d e * ((Z+1 : ℕ) : ℝ) =
      ((Z+1 : ℕ) : ℝ) * (goldbachSieveRootCount d e : ℝ) / e := by
    rw [goldbachSieveDensity_apply]; ring
  rw [hcard, e1, goldbachSieveRootCount_eq_filter_card d e]
  exact h

def shiftSieve (a Z d P : ℕ) (hd : 2 ∣ d) (hP : Squarefree P) : BoundingSieve :=
  PrimePairSieve.imageSieve (Icc a (a+Z)) (fun m => m*(m+d)) P hP
    (goldbachSieveDensity d) (goldbachSieveDensity_isMultiplicative d)
    (fun p hp _ => goldbachSieveDensity_prime_pos d p hp)
    (fun p hp _ => goldbachSieveDensity_prime_lt_one d p hp (fun _ => hd))

theorem normalizer_eq_denominator (a Z d P z : ℕ) (hd : 2 ∣ d) (hP : Squarefree P) :
    SelbergOptimal.normalizer (shiftSieve a Z d P hd hP) z =
      GoldbachSelberg.denominator d P z := by
  unfold SelbergOptimal.normalizer GoldbachSelberg.denominator
  apply sum_congr rfl
  intro e he
  rw [BoundingSieve.selbergTerms_apply]
  rfl

theorem rem_bound (a Z d P e : ℕ) (hd : 2 ∣ d) (hP : Squarefree P) [NeZero e] :
    |(shiftSieve a Z d P hd hP).rem e| ≤ goldbachSieveRootCount d e := by
  unfold shiftSieve
  rw [PrimePairSieve.imageSieve_rem, Nat.card_Icc, show a + Z + 1 - a = Z + 1 by omega]
  simpa using shift_count_discrepancy a Z d e

theorem rem_lcm_bound (a Z d P : ℕ) (hd : 2 ∣ d) (hP : Squarefree P)
    (u : ℕ) (hu : u ∈ P.divisors) (v : ℕ) (hv : v ∈ P.divisors) :
    |(shiftSieve a Z d P hd hP).rem (Nat.lcm u v)| ≤
      (2 : ℝ) ^ u.primeFactors.card * (2 : ℝ) ^ v.primeFactors.card := by
  let : NeZero u := ⟨(Nat.pos_of_mem_divisors hu).ne'⟩
  let : NeZero v := ⟨(Nat.pos_of_mem_divisors hv).ne'⟩
  let : NeZero (Nat.lcm u v) := ⟨Nat.lcm_ne_zero (NeZero.ne u) (NeZero.ne v)⟩
  have hu2 := goldbachSieveRootCount_le_two_pow d u
    (hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors hu))
  have hv2 := goldbachSieveRootCount_le_two_pow d v
    (hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors hv))
  calc
    _ ≤ (goldbachSieveRootCount d (Nat.lcm u v) : ℝ) := rem_bound a Z d P _ hd hP
    _ ≤ (goldbachSieveRootCount d u : ℝ) * goldbachSieveRootCount d v := by
      exact_mod_cast goldbachSieveRootCount_lcm_le d u v
    _ ≤ _ := by exact_mod_cast Nat.mul_le_mul hu2 hv2

theorem sifted_le (a Z d P : ℕ) (hd : 2 ∣ d) (hP : Squarefree P) {z : ℕ} (hz : 1 ≤ z) :
    ((((Icc a (a+Z)).filter (fun m => P.Coprime (m*(m+d)))).card : ℕ) : ℝ) ≤
      ((Z+1 : ℕ) : ℝ) / GoldbachSelberg.denominator d P z +
      (z : ℝ) ^ 2 * (1 + Real.log z) ^ 4 := by
  let s := shiftSieve a Z d P hd hP
  have he := SelbergOptimal.siftedSum_le_log_error s hz
    (fun u hu v hv => rem_lcm_bound a Z d P hd hP u hu v hv)
  have hsum : s.siftedSum =
      ((((Icc a (a+Z)).filter (fun m => P.Coprime (m*(m+d)))).card : ℕ) : ℝ) :=
    PrimePairSieve.imageSieve_siftedSum _ _ _ _ _ _ _ _
  have hmass : s.totalMass = ((Z+1 : ℕ) : ℝ) := by
    show (((Icc a (a+Z)).card : ℕ) : ℝ) = _
    rw [Nat.card_Icc, show a + Z + 1 - a = Z + 1 by omega]
  have hnorm : SelbergOptimal.normalizer s z = GoldbachSelberg.denominator d P z :=
    normalizer_eq_denominator a Z d P z hd hP
  rw [hsum, hmass, hnorm] at he
  exact he

theorem shiftPairs_le (a Z d y : ℕ) (hd : 2 ∣ d) {z : ℕ} (hz : 1 ≤ z) :
    ((shiftPairs a Z d).card : ℝ) ≤
      ((Z+1 : ℕ) : ℝ) / GoldbachSelberg.denominator d (primorial y) z +
      (z : ℝ) ^ 2 * (1 + Real.log z) ^ 4 + y := by
  have hsub : shiftPairs a Z d ⊆
      (Icc a (a+Z)).filter (fun m => (primorial y).Coprime (m*(m+d))) ∪ y.primesLE := by
    intro m hm
    obtain ⟨hmI, hm1, hm2⟩ := mem_filter.mp hm
    by_cases hmy : m ≤ y
    · exact mem_union_right _ (Nat.mem_primesLE.mpr ⟨hmy, hm1⟩)
    · apply mem_union_left
      refine mem_filter.mpr ⟨hmI, ?_⟩
      have key (x : ℕ) (hx : x.Prime) (hxy : y < x) : (primorial y).Coprime x := by
        refine (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hx).mpr ?_))
        intro hdv
        have hmem : x ∈ (primorial y).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hx, hdv, primorial_ne_zero y⟩
        rw [primeFactors_primorial] at hmem
        have := (Nat.mem_primesLE.mp hmem).1
        omega
      exact (key m hm1 (by omega)).mul_right (key (m+d) hm2 (by omega))
  have hc1 := card_le_card hsub
  have hc2 := card_union_le
    ((Icc a (a+Z)).filter (fun m => (primorial y).Coprime (m*(m+d)))) y.primesLE
  have hc3 : (y.primesLE).card ≤ y := by
    have := Finset.card_le_card (s := y.primesLE) (t := Icc 1 y) (fun p hp =>
      Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE hp).one_le,(Nat.mem_primesLE.mp hp).1⟩)
    simpa using this
  have hcast : ((shiftPairs a Z d).card : ℝ) ≤
      ((((Icc a (a+Z)).filter (fun m => (primorial y).Coprime (m*(m+d)))).card : ℕ) : ℝ)
        + y := by
    exact_mod_cast hc1.trans (hc2.trans (Nat.add_le_add_left hc3 _))
  have hs := sifted_le a Z d (primorial y) hd (squarefree_primorial y) hz
  linarith

end
end ShiftSieve

open Filter
namespace ShiftSieve

theorem main_weighted : ∃ K : ℝ, 0 < K ∧ ∃ Z₀ : ℕ, ∀ Z : ℕ, Z₀ ≤ Z → ∀ a d : ℕ, 0 < d →
    Even d → ((shiftPairs a Z d).card : ℝ) * (Real.log Z)^2 ≤
      K * (Z : ℝ) * CentralSelberg.singular d := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp CentralSelberg.scales
  refine ⟨8210, by norm_num, max X 2, ?_⟩
  intro Z hZ a d hd0 hde
  have hZ2 : 2 ≤ Z := (le_max_right ..).trans hZ
  obtain ⟨y, hy, hlog, herr⟩ := hX Z ((le_max_left ..).trans hZ)
  have hd2 : 2 ∣ d := even_iff_two_dvd.mp hde
  have zpos : 1 ≤ y^8 := Nat.one_le_pow _ _ (by omega)
  let D := GoldbachSelberg.denominator d (primorial y) (y^8)
  have hD : 0 < D := GoldbachSelberg.denominator_pos d _ hd2 (squarefree_primorial _) zpos
  have hsing := CentralSelberg.singular_one_le d
  have hDen : (Real.log Z)^2 ≤ 4096 * CentralSelberg.singular d * D := by
    have hp : 0 ≤ Real.log Z := Real.log_nonneg (by exact_mod_cast (show 1 ≤ Z by omega))
    have hsq := pow_le_pow_left₀ hp hlog 2
    have hEu := CentralSelberg.euler_mass d y hd2 hd0
    have hcut := CentralSelberg.retained d y hd2 hy
    change _ ≤ 2 * CentralSelberg.singular d * CentralSelberg.mass d y at hEu
    change CentralSelberg.mass d y ≤ 2 * D at hcut
    nlinarith only [hsq, hEu, mul_le_mul_of_nonneg_left hcut
      (a := CentralSelberg.singular d) (by linarith)]
  have hZ1 : (((Z+1 : ℕ) : ℝ)) ≤ 2 * (Z : ℝ) := by
    have : (2 : ℝ) ≤ Z := by exact_mod_cast hZ2
    push_cast; linarith
  have first : (((Z+1 : ℕ) : ℝ) / D) * (Real.log Z)^2 ≤
      4096 * (((Z+1 : ℕ) : ℝ)) * CentralSelberg.singular d := by
    calc
      _ ≤ (((Z+1 : ℕ) : ℝ) / D) * (4096 * CentralSelberg.singular d * D) :=
        mul_le_mul_of_nonneg_left hDen (by positivity)
      _ = _ := by field_simp
  have hs := shiftPairs_le a Z d y hd2 zpos
  have heP := mul_le_mul_of_nonneg_right hs (sq_nonneg (Real.log Z))
  have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg y
  have hT : 0 ≤ ((y^8 : ℕ) : ℝ)^2 * (1 + Real.log ((y^8 : ℕ) : ℝ))^4 := by
    have : 0 ≤ Real.log ((y^8 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast zpos)
    positivity
  have hZr : (0 : ℝ) ≤ Z := Nat.cast_nonneg Z
  have hsq0 : 0 ≤ (Real.log Z)^2 := sq_nonneg _
  have e1 : ((((Z+1 : ℕ) : ℝ)) / D + ((y^8 : ℕ) : ℝ)^2 * (1 + Real.log ((y^8 : ℕ) : ℝ))^4 + y)
      * (Real.log Z)^2 =
      (((Z+1 : ℕ) : ℝ) / D) * (Real.log Z)^2 +
      (((y^8 : ℕ) : ℝ)^2 * (1 + Real.log ((y^8 : ℕ) : ℝ))^4 + y) * (Real.log Z)^2 := by ring
  have e2 : (((y^8 : ℕ) : ℝ)^2 * (1 + Real.log ((y^8 : ℕ) : ℝ))^4 + y) * (Real.log Z)^2 ≤
      (((y^8 : ℕ) : ℝ)^2 * (1 + Real.log ((y^8 : ℕ) : ℝ))^4 + 2 * (y : ℝ)) * (Real.log Z)^2 :=
    mul_le_mul_of_nonneg_right (by linarith) hsq0
  have h3 : 4096 * (((Z+1 : ℕ) : ℝ)) * CentralSelberg.singular d ≤
      8192 * (Z : ℝ) * CentralSelberg.singular d := by
    have := mul_le_mul_of_nonneg_right hZ1 (by linarith : (0 : ℝ) ≤ CentralSelberg.singular d)
    nlinarith only [this]
  have h4 : (18 : ℝ) * Z ≤ 18 * (Z : ℝ) * CentralSelberg.singular d := by
    nlinarith only [hsing, hZr]
  nlinarith only [heP, e1, e2, first, herr, h3, h4]

theorem singular_eq (d : ℕ) :
    CentralSelberg.singular d =
      ∏ l ∈ d.primeFactors.filter (fun l => 2 < l), (((l:ℝ)-1)/((l:ℝ)-2)) := by
  unfold CentralSelberg.singular
  apply Finset.prod_congr rfl
  intro l hl
  have h : (2 : ℝ) < l := by exact_mod_cast (Finset.mem_filter.mp hl).2
  have h2 : (l : ℝ) - 2 ≠ 0 := by linarith
  field_simp
  ring

end ShiftSieve

theorem shifted_pair_upper :
    ∃ K : ℝ, 0 < K ∧ ∃ Z₀ : ℕ, ∀ Z : ℕ, Z₀ ≤ Z → ∀ a d : ℕ, 0 < d → Even d → d ≤ Z →
      (((Finset.Icc a (a + Z)).filter (fun m => m.Prime ∧ (m + d).Prime)).card : ℝ) ≤
        K * (Z : ℝ) * (∏ l ∈ d.primeFactors.filter (fun l => 2 < l), (((l:ℝ)-1)/((l:ℝ)-2))) / (Real.log (Z : ℝ))^2 := by
  obtain ⟨K, hK, Z₀, h⟩ := ShiftSieve.main_weighted
  refine ⟨K, hK, max Z₀ 2, ?_⟩
  intro Z hZ a d hd hde _
  have hZ2 : 2 ≤ Z := (le_max_right ..).trans hZ
  have hlogpos : 0 < Real.log (Z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Z by omega))
  rw [le_div_iff₀ (by positivity), ← ShiftSieve.singular_eq]
  exact h Z ((le_max_left ..).trans hZ) a d hd hde



open Finset

namespace GoldbachSquareMean

private def oddFactors (n : ℕ) : Finset ℕ := n.primeFactors.filter (2 < ·)

private noncomputable def singular (n : ℕ) : ℝ :=
  ∏ p ∈ oddFactors n, (1 + 1 / ((p : ℝ) - 2))

private noncomputable def increment (p : ℕ) : ℝ := (1 + 1 / ((p : ℝ) - 2))^2 - 1

private theorem increment_nonneg {p : ℕ} (hp : 3 ≤ p) : 0 ≤ increment p := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have h : 0 ≤ 1 / ((p : ℝ) - 2) := div_nonneg zero_le_one (by linarith)
  unfold increment
  nlinarith [sq_nonneg (1 / ((p : ℝ) - 2))]

/-- A telescoping rational product bounds the averaged Euler factors at integers from 5 onwards. -/
private theorem tail_product (N : ℕ) (hN : 4 ≤ N) :
    ∏ p ∈ Icc 5 N, (1 + increment p / (p : ℝ)) ≤ 2 * ((N : ℝ) - 2) / N := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hI : Icc 5 (k + 1) = insert (k + 1) (Icc 5 k) := by
      ext j
      simp only [mem_Icc, mem_insert]
      omega
    rw [hI, prod_insert (by simp)]
    have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
    have hinc := increment_nonneg (p := k + 1) (by omega)
    calc
      _ ≤ (1 + increment (k+1) / ((k+1 : ℕ) : ℝ)) * (2 * ((k : ℝ) - 2) / k) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ ≤ _ := by
        simp only [increment, Nat.cast_succ]
        rw [show (k : ℝ) + 1 - 2 = (k : ℝ) - 1 by ring]
        have h0 : (k : ℝ) ≠ 0 := by linarith
        have h1 : (k : ℝ) - 1 ≠ 0 := by linarith
        have h2 : (k : ℝ) + 1 ≠ 0 := by linarith
        calc
          _ = 2 * ((k : ℝ) - 1) / (k + 1) - 2 / ((k + 1) * (k - 1 : ℝ)^2) := by
            field_simp [h0, h1, h2]
            ring
          _ ≤ _ := sub_le_self _ (by positivity)

/-- Every odd prime factor of a positive integer at most `M` is 3 or lies in this tail. -/
private def candidates (M : ℕ) : Finset ℕ := insert 3 (Icc 5 (M+4))

private theorem candidates_ge_three {M p : ℕ} (hp : p ∈ candidates M) : 3 ≤ p := by
  rcases mem_insert.mp hp with rfl | hp
  · decide
  · have := (mem_Icc.mp hp).1
    omega

private theorem candidates_product (M : ℕ) :
    ∏ p ∈ candidates M, (1 + increment p / (p : ℝ)) ≤ 4 := by
  have htail := tail_product (M+4) (by omega)
  have hpos : (0 : ℝ) < (M+4 : ℕ) := by positivity
  have hbound : 2 * (((M+4 : ℕ) : ℝ) - 2) / (M+4 : ℕ) ≤ 2 :=
    (div_le_iff₀ hpos).mpr (by linarith)
  rw [candidates, prod_insert (by simp)]
  have hthree : 1 + increment 3 / (3 : ℝ) = 2 := by norm_num [increment]
  change (1 + increment 3 / (3 : ℝ)) * _ ≤ 4
  rw [hthree]
  linarith [htail.trans hbound]

private theorem oddFactors_subset {M n : ℕ} (hn : n ≤ M) : oddFactors n ⊆ candidates M := by
  intro p hp
  obtain ⟨hdiv, hodd⟩ := mem_filter.mp hp
  have hpN := Nat.le_of_mem_primeFactors hdiv
  have hfour : p ≠ 4 := by
    rintro rfl
    exact (by decide : ¬ Nat.Prime 4) (Nat.prime_of_mem_primeFactors hdiv)
  by_cases h : p = 3
  · exact mem_insert.mpr (Or.inl h)
  · exact mem_insert.mpr (Or.inr (mem_Icc.mpr ⟨by omega, by omega⟩))

private def divisorProduct (t : Finset ℕ) : ℕ := ∏ p ∈ t, p

private noncomputable def subsetWeight (t : Finset ℕ) : ℝ := ∏ p ∈ t, increment p

/-- A subset of the odd prime factors contributes only at multiples of its product. -/
private theorem square_le_divisor_sum {n M : ℕ} (hn : n ≤ M) :
    singular n ^ 2 ≤ ∑ t ∈ (candidates M).powerset,
      if divisorProduct t ∣ n then subsetWeight t else 0 := by
  classical
  let A := oddFactors n
  have hdiv (t : Finset ℕ) (ht : t ∈ A.powerset) : divisorProduct t ∣ n := by
    have hsub : t ⊆ n.primeFactors :=
      (mem_powerset.mp ht).trans (filter_subset _ _)
    exact (Finset.prod_dvd_prod_of_subset t n.primeFactors id hsub).trans n.prod_primeFactors_dvd
  calc
    singular n ^ 2 = ∏ p ∈ A, (1 + increment p) := by
      unfold singular
      rw [← Finset.prod_pow]
      apply prod_congr rfl
      intro p _
      dsimp [increment]
      ring
    _ = ∑ t ∈ A.powerset, subsetWeight t := Finset.prod_one_add A
    _ = ∑ t ∈ A.powerset, if divisorProduct t ∣ n then subsetWeight t else 0 := by
      exact sum_congr rfl fun t ht ↦ (ite_eq_left (hdiv t ht)).symm
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · exact fun t ht ↦ mem_powerset.mpr ((mem_powerset.mp ht).trans (oddFactors_subset hn))
      · intro t ht _
        split_ifs
        · exact prod_nonneg fun p hp ↦ increment_nonneg (candidates_ge_three (mem_powerset.mp ht hp))
        · exact le_rfl

private theorem multiples_count (M d : ℕ) : ((Icc 1 M).filter (fun n ↦ d ∣ n)).card = M / d := by
  have sets : (Icc 1 M).filter (fun n ↦ d ∣ n) = (range M.succ).filter (fun n ↦ n ≠ 0 ∧ d ∣ n) := by
    ext n
    simp only [mem_filter, mem_Icc, mem_range]
    omega
  rw [sets, Nat.card_multiples']

/-- Average the expanded factors using the exact count `M / d` of positive multiples. -/
private theorem head_square (M : ℕ) : (∑ n ∈ Icc 1 M, singular n ^ 2) ≤ 4*(M : ℝ) := by
  classical
  let P := candidates M
  calc
    (∑ n ∈ Icc 1 M, singular n ^ 2) ≤ ∑ n ∈ Icc 1 M, ∑ t ∈ P.powerset,
        if divisorProduct t ∣ n then subsetWeight t else 0 :=
      sum_le_sum fun n hn ↦ square_le_divisor_sum (mem_Icc.mp hn).2
    _ = ∑ t ∈ P.powerset, ∑ n ∈ Icc 1 M,
        if divisorProduct t ∣ n then subsetWeight t else 0 := Finset.sum_comm
    _ ≤ ∑ t ∈ P.powerset, (M : ℝ) * (∏ p ∈ t, increment p / (p : ℝ)) := by
      apply sum_le_sum
      intro t ht
      have hw : 0 ≤ subsetWeight t := prod_nonneg fun p hp ↦
        increment_nonneg (candidates_ge_three (mem_powerset.mp ht hp))
      rw [← sum_filter, sum_const, multiples_count, nsmul_eq_mul]
      calc
        _ ≤ ((M : ℝ) / (divisorProduct t : ℝ)) * subsetWeight t :=
          mul_le_mul_of_nonneg_right Nat.cast_div_le hw
        _ = _ := by
          rw [Finset.prod_div_distrib]
          simp only [divisorProduct, Nat.cast_prod, subsetWeight]
          ring
    _ = (M : ℝ) * ∏ p ∈ P, (1 + increment p / (p : ℝ)) := by
      rw [← Finset.mul_sum, Finset.prod_one_add]
    _ ≤ 4 * (M : ℝ) := by
      rw [mul_comm (4 : ℝ)]
      exact mul_le_mul_of_nonneg_left (candidates_product M) (Nat.cast_nonneg _)

noncomputable def Sf (d : ℕ) : ℝ :=
  ∏ l ∈ d.primeFactors.filter (fun l => 2 < l), (((l:ℝ)-1)/((l:ℝ)-2))

theorem Sf_eq (d : ℕ) : Sf d = singular d := by
  unfold Sf singular oddFactors
  refine prod_congr rfl fun p hp => ?_
  have h2 : (2:ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2
  have h : (p:ℝ) - 2 ≠ 0 := by linarith
  field_simp
  ring

theorem Sf_nonneg (d : ℕ) : 0 ≤ Sf d := by
  unfold Sf
  refine prod_nonneg fun p hp => ?_
  have h2 : (2:ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2
  exact div_nonneg (by linarith) (by linarith)

theorem Sf_sq_sum (M : ℕ) : (∑ n ∈ Icc 1 M, Sf n ^ 2) ≤ 4 * (M : ℝ) := by
  simp_rw [Sf_eq]
  exact head_square M

end GoldbachSquareMean

namespace MeanCond
open Finset Filter
open scoped Topology

private theorem theta_bounds : ∃ K : ℕ, ∀ n ≥ K,
    (19/20 : ℝ) * n < Chebyshev.theta n ∧ Chebyshev.theta n < (21/20 : ℝ) * n := by
  have limN : Tendsto (fun n : ℕ ↦ Chebyshev.theta n / (n : ℝ)) atTop (𝓝 1) :=
    Chebyshev.tendsto_theta_div_atTop.comp tendsto_natCast_atTop_atTop
  apply Filter.eventually_atTop.mp
  filter_upwards [limN.eventually_const_lt (show (19/20 : ℝ) < 1 by norm_num),
    limN.eventually_lt_const (show (1 : ℝ) < 21/20 by norm_num),
    eventually_ge_atTop (1 : ℕ)] with n hlo hhi hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact ⟨(lt_div_iff₀ hn').mp hlo, (div_lt_iff₀ hn').mp hhi⟩

private theorem window_le (a b : ℕ) (hab : a ≤ b) :
    Chebyshev.theta (b:ℝ) - Chebyshev.theta (a:ℝ) ≤
      (((Finset.Ioc a b).filter Nat.Prime).card : ℝ) * Real.log b := by
  have expand (n : ℕ) : Chebyshev.theta (n : ℝ) =
      ∑ p ∈ Ioc 0 n, (if p.Prime then Real.log (p:ℝ) else 0) := by
    simp [Chebyshev.theta, sum_filter]
  have split := Finset.sum_union (f := fun p : ℕ => if p.Prime then Real.log (p:ℝ) else 0)
    (Finset.Ioc_disjoint_Ioc_of_le (a := 0) (b := a) (c := a) (d := b) le_rfl)
  rw [Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hab] at split
  have h1 : Chebyshev.theta (b:ℝ) - Chebyshev.theta (a:ℝ) =
      ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log (p:ℝ) := by
    rw [expand, expand, split, sum_filter]
    ring
  rw [h1]
  calc ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log (p:ℝ)
      ≤ ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log (b:ℝ) := by
        refine sum_le_sum fun p hp => ?_
        have hp' := mem_filter.mp hp
        have h2 := (mem_Ioc.mp hp'.1)
        exact Real.log_le_log (by exact_mod_cast hp'.2.pos) (by exact_mod_cast h2.2)
    _ = _ := by simp

theorem card_lower : ∃ K : ℕ, ∀ s : ℕ, K ≤ s →
    (17/40 : ℝ) * s ≤ (((Icc s (2*s)).filter Nat.Prime).card : ℝ) * Real.log s := by
  obtain ⟨K, hK⟩ := theta_bounds
  refine ⟨K+2, fun s hs => ?_⟩
  have h1 := window_le s (2*s) (by omega)
  have hbs := hK s (by omega)
  have hb2s := hK (2*s) (by omega)
  push_cast at h1 hb2s
  have hs2 : (2:ℝ) ≤ s := by exact_mod_cast (by omega : 2 ≤ s)
  have hlog : Real.log (2*(s:ℝ)) ≤ 2 * Real.log s := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    have : Real.log 2 ≤ Real.log s := Real.log_le_log (by norm_num) hs2
    linarith
  have hsub : ((Ioc s (2*s)).filter Nat.Prime).card ≤ ((Icc s (2*s)).filter Nat.Prime).card :=
    card_le_card (filter_subset_filter _ Ioc_subset_Icc_self)
  have hsubR : (((Ioc s (2*s)).filter Nat.Prime).card : ℝ) ≤
      (((Icc s (2*s)).filter Nat.Prime).card : ℝ) := by exact_mod_cast hsub
  have hc0 : (0:ℝ) ≤ (((Ioc s (2*s)).filter Nat.Prime).card : ℝ) := Nat.cast_nonneg _
  have hL : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
  have e1 := mul_le_mul_of_nonneg_left hlog hc0
  have e2 := mul_le_mul_of_nonneg_right hsubR hL
  nlinarith [hb2s.1, hbs.2]

theorem regroup (s : ℕ) (S : ℕ → ℝ) (P : Finset ℕ) (hP : ∀ p ∈ P, s ≤ p ∧ p ≤ 2*s) :
    ∑ p ∈ P, ∑ q ∈ P.filter (fun q => p < q), S (q-p) =
      ∑ d ∈ Icc 1 s, S d * ((P.filter (fun p => p + d ∈ P)).card : ℝ) := by
  have h1 : ∀ p ∈ P, ∑ q ∈ P.filter (fun q => p < q), S (q-p) =
      ∑ d ∈ Icc 1 s, if p + d ∈ P then S d else 0 := by
    intro p hp
    rw [← sum_filter]
    obtain ⟨hp1, hp2⟩ := hP p hp
    refine sum_nbij' (fun q => q - p) (fun d => d + p) ?_ ?_ ?_ ?_ ?_
    · intro q hq
      simp only [mem_filter, mem_Icc] at hq ⊢
      obtain ⟨hqP, hpq⟩ := hq
      obtain ⟨hq1, hq2⟩ := hP q hqP
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rwa [show p + (q - p) = q by omega]
    · intro d hd
      simp only [mem_filter, mem_Icc] at hd ⊢
      obtain ⟨⟨hd1, hd2⟩, hdP⟩ := hd
      refine ⟨?_, by omega⟩
      rwa [add_comm]
    · intro q hq
      simp only [mem_filter] at hq
      show q - p + p = q
      omega
    · intro d _
      show d + p - p = d
      omega
    · intro q _
      rfl
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun d _ => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]

theorem pair_bound (s : ℕ) (hs3 : 3 ≤ s) (K L : ℝ) (hK : 0 ≤ K)
    (hd : ∀ d : ℕ, 0 < d → Even d → d ≤ s →
      ((((Icc s (s + s)).filter (fun m => m.Prime ∧ (m + d).Prime)).card : ℕ) : ℝ) ≤
        K * (s : ℝ) * GoldbachSquareMean.Sf d / L ^ 2) :
    ∑ p ∈ (Icc s (2*s)).filter Nat.Prime,
        ∑ q ∈ ((Icc s (2*s)).filter Nat.Prime).filter (fun q => p < q),
          GoldbachSquareMean.Sf (q - p) ≤
      K * (s : ℝ) / L ^ 2 * ∑ d ∈ Icc 1 s, GoldbachSquareMean.Sf d ^ 2 := by
  set P := (Icc s (2*s)).filter Nat.Prime with hPdef
  have hP : ∀ p ∈ P, s ≤ p ∧ p ≤ 2*s := fun p hp => mem_Icc.mp (mem_filter.mp hp).1
  rw [regroup s _ P hP, mul_sum]
  refine sum_le_sum fun d hdm => ?_
  have hd1 := mem_Icc.mp hdm
  have hSn := GoldbachSquareMean.Sf_nonneg d
  have hbound : ((P.filter (fun p => p + d ∈ P)).card : ℝ) ≤
      K * (s : ℝ) * GoldbachSquareMean.Sf d / L ^ 2 := by
    by_cases hev : Even d
    · refine le_trans ?_ (hd d (by omega) hev hd1.2)
      have hsub : P.filter (fun p => p + d ∈ P) ⊆
          (Icc s (s + s)).filter (fun m => m.Prime ∧ (m + d).Prime) := by
        intro p hp
        simp only [hPdef, mem_filter, mem_Icc] at hp ⊢
        obtain ⟨⟨hp1, hp2⟩, hq⟩ := hp
        exact ⟨⟨hp1.1, by omega⟩, hp2, hq.2⟩
      exact_mod_cast card_le_card hsub
    · have hem : P.filter (fun p => p + d ∈ P) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro p hp hq
        simp only [hPdef, mem_filter, mem_Icc] at hp hq
        have hpodd : Odd p := hp.2.odd_of_ne_two (by omega)
        have hqodd : Odd (p + d) := hq.2.odd_of_ne_two (by omega)
        exact hev ((Nat.odd_add.mp hqodd).mp hpodd)
      rw [hem]
      simp only [card_empty, Nat.cast_zero]
      have : (0:ℝ) ≤ K * (s : ℝ) * GoldbachSquareMean.Sf d / L ^ 2 := by
        exact div_nonneg (mul_nonneg (mul_nonneg hK (Nat.cast_nonneg _)) hSn) (sq_nonneg L)
      exact this
  calc GoldbachSquareMean.Sf d * ((P.filter (fun p => p + d ∈ P)).card : ℝ)
      ≤ GoldbachSquareMean.Sf d * (K * (s : ℝ) * GoldbachSquareMean.Sf d / L ^ 2) :=
        mul_le_mul_of_nonneg_left hbound hSn
    _ = K * (s : ℝ) / L ^ 2 * GoldbachSquareMean.Sf d ^ 2 := by ring

end MeanCond

end Conjectures.Goldbach.RobustInputs

namespace Conjectures.Goldbach.BSD
open Conjectures.Goldbach.RobustInputs
open Finset Filter
open scoped Topology

private def Nn (X : ℕ) : Finset ℕ := (Icc X (6*X/5)).filter (fun n => Even n)
private def Ww (X : ℕ) : Finset ℕ := (Icc ((X+1)/2) (2*X/3)).filter Nat.Prime
private def Qq (X : ℕ) : Finset ℕ := (Icc ((X+1)/2) (3*X/5)).filter Nat.Prime
private def Pp (X : ℕ) : Finset ℕ := (Icc ((X+1)/2) (2*((X+1)/2))).filter Nat.Prime
private def Hh (X n : ℕ) : ℕ := ((Ww X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card

private theorem Ww_sub (X : ℕ) (hX : 4 ≤ X) : Ww X ⊆ Pp X := by
  intro p hp
  obtain ⟨h1, h2⟩ := mem_filter.mp hp
  obtain ⟨h3, h4⟩ := mem_Icc.mp h1
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, h2⟩

private theorem Qq_sub (X : ℕ) : Qq X ⊆ Ww X := by
  intro p hp
  obtain ⟨h1, h2⟩ := mem_filter.mp hp
  obtain ⟨h3, h4⟩ := mem_Icc.mp h1
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, h2⟩

private theorem q_lower : ∃ K : ℕ, ∀ X : ℕ, K ≤ X →
    (1/25:ℝ) * X ≤ (((Qq X).card : ℕ) : ℝ) * Real.log X := by
  obtain ⟨K, hK⟩ := MeanCond.theta_bounds
  refine ⟨2*K+300, fun X hX => ?_⟩
  have h1 := MeanCond.window_le ((X+1)/2) (3*X/5) (by omega)
  have ha := hK ((X+1)/2) (by omega)
  have hb := hK (3*X/5) (by omega)
  have hsub : (((Ioc ((X+1)/2) (3*X/5)).filter Nat.Prime).card) ≤ (Qq X).card :=
    card_le_card (filter_subset_filter _ Ioc_subset_Icc_self)
  have hsubR : ((((Ioc ((X+1)/2) (3*X/5)).filter Nat.Prime).card : ℕ) : ℝ) ≤ (((Qq X).card : ℕ) : ℝ) := by
    exact_mod_cast hsub
  have hb1 : 1 ≤ 3*X/5 := by omega
  have hbR : (1:ℝ) ≤ ((3*X/5 : ℕ) : ℝ) := by exact_mod_cast hb1
  have hlog : Real.log ((3*X/5 : ℕ) : ℝ) ≤ Real.log X :=
    Real.log_le_log (by linarith) (by exact_mod_cast (by omega : 3*X/5 ≤ X))
  have hl0 : 0 ≤ Real.log ((3*X/5 : ℕ) : ℝ) := Real.log_nonneg hbR
  have e1 := mul_le_mul hsubR hlog hl0 (Nat.cast_nonneg _)
  have c1 : (3*(X:ℝ)) ≤ 5 * ((3*X/5 : ℕ) : ℝ) + 4 := by
    have : 3*X ≤ 5*(3*X/5) + 4 := by omega
    exact_mod_cast this
  have c2 : 2 * (((X+1)/2 : ℕ) : ℝ) ≤ (X:ℝ) + 1 := by
    have : 2*((X+1)/2) ≤ X + 1 := by omega
    exact_mod_cast this
  have hXR : (300:ℝ) ≤ X := by exact_mod_cast (by omega : 300 ≤ X)
  nlinarith [hb.1, ha.2]

private theorem p_upper (X : ℕ) (hX : 4 ≤ X) :
    (((Pp X).card : ℕ) : ℝ) * Real.log X ≤ (4 * Real.log 4) * X := by
  have hs : 2 ≤ (X+1)/2 := by omega
  have hsR : (2:ℝ) ≤ (((X+1)/2 : ℕ) : ℝ) := by exact_mod_cast hs
  have hXR : (4:ℝ) ≤ X := by exact_mod_cast hX
  have hmass : ((Pp X).card:ℝ) * Real.log (((X+1)/2 : ℕ) : ℝ) ≤ Real.log 4 * ((2*((X+1)/2) : ℕ) : ℝ) := by
    calc
      _ = ∑ _p ∈ Pp X, Real.log (((X+1)/2 : ℕ) : ℝ) := by simp [nsmul_eq_mul]
      _ ≤ ∑ p ∈ Pp X, Real.log (p:ℝ) := by
        exact sum_le_sum fun p hp => Real.log_le_log (by linarith)
          (by exact_mod_cast (mem_Icc.mp (mem_filter.mp hp).1).1)
      _ ≤ ∑ p ∈ (2*((X+1)/2)).primesLE, Real.log (p:ℝ) := by
        apply sum_le_sum_of_subset_of_nonneg
        · exact fun p hp => Nat.mem_primesLE.mpr ⟨(mem_Icc.mp (mem_filter.mp hp).1).2,(mem_filter.mp hp).2⟩
        · intro p hp _
          exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le)
      _ ≤ _ := by
        rw [← Chebyshev.theta_eq_sum_primesLE_log]
        exact Chebyshev.theta_le_log4_mul_x (by positivity)
  have hXs : X ≤ ((X+1)/2) * ((X+1)/2) := by nlinarith [Nat.div_add_mod (X+1) 2, Nat.mod_lt (X+1) (show 0 < 2 by norm_num)]
  have hlog : Real.log X ≤ 2 * Real.log (((X+1)/2 : ℕ) : ℝ) := by
    have := Real.log_le_log (by linarith) (show (X:ℝ) ≤ ((((X+1)/2 : ℕ) : ℝ))^2 by
      rw [sq]; exact_mod_cast hXs)
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have h2s : ((2*((X+1)/2) : ℕ) : ℝ) ≤ 2 * X := by
    have : 2*((X+1)/2) ≤ 2 * X := by omega
    exact_mod_cast this
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hc0 : (0:ℝ) ≤ ((Pp X).card:ℝ) := Nat.cast_nonneg _
  push_cast at hmass h2s
  nlinarith [mul_le_mul_of_nonneg_left hlog hc0, mul_le_mul_of_nonneg_left h2s hl4]

private theorem lost (E P D : Finset ℕ) :
    let H := fun n => (P.filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card
    let good := fun n => ∃ p ∈ P, p ≤ n ∧ Nat.Prime (n-p) ∧ n-p ∉ D
    (∑ n ∈ E, H n) ≤ (∑ n ∈ E.filter good, H n) + P.card*D.card := by
  classical
  intro H good
  rw [← Finset.sum_filter_add_sum_filter_not E good]
  apply Nat.add_le_add_left
  let T := E.filter (fun n => ¬ good n)
  calc
    (∑ n ∈ T, H n) =
        ∑ p ∈ P, (T.filter (fun n => p ≤ n ∧ Nat.Prime (n-p))).card := by
          simp only [H, Finset.card_filter]
          exact Finset.sum_comm
    _ ≤ ∑ _p ∈ P, D.card := by
      apply sum_le_sum
      intro p hp
      apply Finset.card_le_card_of_injOn (fun n => n-p)
      · intro n hn
        obtain ⟨hnT, hpn, hprime⟩ := mem_filter.mp hn
        by_contra hmiss
        exact (mem_filter.mp hnT).2 ⟨p,hp,hpn,hprime,hmiss⟩
      · intro n hn m hm he
        have hn' := (mem_filter.mp hn).2.1
        have hm' := (mem_filter.mp hm).2.1
        change n-p = m-p at he
        omega
    _ = _ := by simp

private theorem collisions (E P : Finset ℕ) :
    (∑ n ∈ E, ((P.filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card *
      ((P.filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card - 1))) =
    ∑ p ∈ P, ∑ q ∈ P.erase p,
      (E.filter (fun n => p≤n ∧ q≤n ∧ Nat.Prime (n-p) ∧ Nat.Prime (n-q))).card := by
  classical
  have h1 : ∀ n, (P.filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card *
      ((P.filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card - 1)
      = ∑ p ∈ P, ∑ q ∈ P.erase p,
        if (p ≤ n ∧ Nat.Prime (n-p)) ∧ (q ≤ n ∧ Nat.Prime (n-q)) then 1 else 0 := by
    intro n
    set S := P.filter (fun p => p ≤ n ∧ Nat.Prime (n-p)) with hS
    have : S.card * (S.card - 1) = ∑ p ∈ S, ((P.erase p |>.filter
        (fun q => q ≤ n ∧ Nat.Prime (n-q))).card) := by
      have h2 : ∑ p ∈ S, ((P.erase p |>.filter
          (fun q => q ≤ n ∧ Nat.Prime (n-q))).card) = ∑ p ∈ S, (S.card - 1) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [← Finset.card_erase_of_mem hp]
        congr 1
        ext q
        simp only [hS, Finset.mem_erase, Finset.mem_filter]
        tauto
      rw [h2, Finset.sum_const, smul_eq_mul]
    rw [this, hS, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs with h
    · rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro q _
      simp [h]
    · symm
      apply Finset.sum_eq_zero
      intro q _
      simp [h]
  rw [Finset.sum_congr rfl (fun n _ => h1 n), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases a : p ≤ n <;> by_cases b : q ≤ n <;> simp [a, b]

private theorem offDiagonal (P : Finset ℕ) (K : ℕ → ℕ → ℝ) (symm : ∀ p q, K p q = K q p) :
    (∑ p ∈ P, ∑ q ∈ P.erase p, K p q) =
    2 * ∑ p ∈ P, ∑ q ∈ P.filter (p < ·), K p q := by
  classical
  have row (p : ℕ) :
      (∑ q ∈ P.erase p, K p q) = ∑ q ∈ P,
        ((if p < q then K p q else 0) + (if q < p then K q p else 0)) := by
    rw [show P.erase p = P.filter (· ≠ p) by ext q; simp [and_comm], Finset.sum_filter]
    apply sum_congr rfl
    intro q _
    rcases lt_trichotomy p q with h | rfl | h
    · simp [h, h.ne', h.asymm]
    · simp
    · simp [h, h.ne, h.asymm, symm q p]
  simp_rw [row, Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := P) (t := P) (f := fun p q => if q < p then K q p else 0)]
  simp only [Finset.sum_filter]
  ring

private theorem logBound : ∀ᶠ X : ℕ in atTop, (Real.log (X:ℝ))^4 ≤ X := by
  have h := (isLittleO_log_rpow_rpow_atTop (4:ℝ) (by norm_num : (0:ℝ)<1)).bound (by norm_num : (0:ℝ)<1)
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually h, eventually_ge_atTop (1:ℕ)] with X hX h1
  have hx : 0 ≤ (X:ℝ) := Nat.cast_nonneg _
  simpa only [Real.rpow_one, Real.norm_eq_abs, one_mul, Real.rpow_ofNat,
    abs_of_nonneg (by positivity : 0 ≤ (Real.log (X:ℝ))^4), abs_of_nonneg hx] using hX

private theorem first_moment (X : ℕ) (hX : 8 ≤ X) :
    (Qq X).card ^ 2 ≤ ∑ n ∈ Nn X, Hh X n := by
  classical
  have h1 : ∑ n ∈ Nn X, Hh X n = ∑ p ∈ Ww X, ((Nn X).filter (fun n => p ≤ n ∧ Nat.Prime (n-p))).card := by
    simp only [Hh, Finset.card_filter]
    exact Finset.sum_comm
  rw [h1]
  calc (Qq X).card ^ 2 = ∑ _p ∈ Qq X, (Qq X).card := by simp [sq]
    _ ≤ ∑ p ∈ Qq X, ((Nn X).filter (fun n => p ≤ n ∧ Nat.Prime (n-p))).card := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
      obtain ⟨hp1, hp2⟩ := mem_Icc.mp hpI
      apply Finset.card_le_card_of_injOn (fun q => p + q)
      · intro q hq
        obtain ⟨hqI, hqp⟩ := mem_filter.mp hq
        obtain ⟨hq1, hq2⟩ := mem_Icc.mp hqI
        obtain ⟨i, hi⟩ := hpp.odd_of_ne_two (by omega)
        obtain ⟨j, hj⟩ := hqp.odd_of_ne_two (by omega)
        show p + q ∈ (Nn X).filter (fun n => p ≤ n ∧ Nat.Prime (n-p))
        refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, ⟨i+j+1, by omega⟩⟩, by omega, ?_⟩
        simpa using hqp
      · intro q _ q' _ h
        change p + q = p + q' at h
        omega
    _ ≤ _ := sum_le_sum_of_subset (Qq_sub X)

private theorem second_moment : ∃ b : ℝ, 0 < b ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀,
    (∑ n ∈ Nn X, (Hh X n : ℝ)^2) ≤ b * X * ((X:ℝ) / (Real.log X)^2)^2 := by
  classical
  obtain ⟨A, hA, Z₀, hbase⟩ := shifted_pair_upper
  obtain ⟨N₃, hlogB⟩ := eventually_atTop.mp logBound
  refine ⟨1 + 32*A^2, by positivity, max 16 (max (2*Z₀+4) N₃), ?_⟩
  intro X hX
  have h16 : 16 ≤ X := by omega
  have hZX : Z₀ ≤ X := by omega
  have hx : (0:ℝ) < X := by exact_mod_cast (show 0<X by omega)
  set L := Real.log (X:ℝ) with hLdef
  have hL : 0 < L := Real.log_pos (by exact_mod_cast (show 1<X by omega))
  have hlog4 : L^4 ≤ X := hlogB X (by omega)
  set s := (X+1)/2 with hsdef
  have hsZ : Z₀ ≤ s := by omega
  have hs3 : 3 ≤ s := by omega
  have hsR : (3:ℝ) ≤ s := by exact_mod_cast hs3
  have hLs : 0 < Real.log (s:ℝ) := Real.log_pos (by linarith)
  have hXs : X ≤ s * s := by
    nlinarith [Nat.div_add_mod (X+1) 2, Nat.mod_lt (X+1) (show 0 < 2 by norm_num)]
  have hLL : L ≤ 2 * Real.log (s:ℝ) := by
    have := Real.log_le_log hx (show (X:ℝ) ≤ (s:ℝ)^2 by rw [sq]; exact_mod_cast hXs)
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hpair (p q : ℕ) (hp : p ∈ Ww X) (hq : q ∈ Ww X) (hpq : p < q) :
      (((Nn X).filter (fun n => p≤n ∧ q≤n ∧ Nat.Prime (n-p) ∧ Nat.Prime (n-q))).card : ℝ)
        ≤ A*X*GoldbachSquareMean.Sf (q-p)/L^2 := by
    obtain ⟨hpI,hpp⟩ := mem_filter.mp hp
    obtain ⟨hqI,hqp⟩ := mem_filter.mp hq
    obtain ⟨hp0, hp1⟩ := mem_Icc.mp hpI
    obtain ⟨hq0, hq1⟩ := mem_Icc.mp hqI
    obtain ⟨i, hi⟩ := hpp.odd_of_ne_two (by omega)
    obtain ⟨j, hj⟩ := hqp.odd_of_ne_two (by omega)
    have he : Even (q-p) := ⟨j-i, by omega⟩
    apply le_trans _ (hbase X hZX (X-q) (q-p) (by omega) he (by omega))
    exact_mod_cast (show ((Nn X).filter (fun n => p≤n ∧ q≤n ∧ Nat.Prime (n-p) ∧ Nat.Prime (n-q))).card ≤
        ((Finset.Icc (X-q) (X-q+X)).filter (fun m => m.Prime ∧ (m + (q-p)).Prime)).card by
      apply card_le_card_of_injOn (fun n => n-q)
      · intro n hn
        obtain ⟨hnE,hpn,hqn,hnp,hnq⟩ := mem_filter.mp hn
        obtain ⟨hnmin,hnmax⟩ := mem_Icc.mp (mem_filter.mp hnE).1
        change n-q ∈ (Icc (X-q) (X-q+X)).filter _
        apply mem_filter.mpr
        exact ⟨mem_Icc.mpr ⟨by omega,by omega⟩, hnq, by simpa only [show n-q+(q-p)=n-p by omega] using hnp⟩
      · intro n hn m hm hh
        have hqn := (mem_filter.mp hn).2.2.1
        have hqm := (mem_filter.mp hm).2.2.1
        change n-q=m-q at hh
        omega)
  have hsym (p q : ℕ) :
      (((Nn X).filter (fun n => p≤n ∧ q≤n ∧ Nat.Prime (n-p) ∧ Nat.Prime (n-q))).card : ℝ)
       = (((Nn X).filter (fun n => q≤n ∧ p≤n ∧ Nat.Prime (n-q) ∧ Nat.Prime (n-p))).card : ℝ) := by
    congr 2; ext n; simp only [mem_filter]; tauto
  have hPB := MeanCond.pair_bound s hs3 A (Real.log (s:ℝ)) hA.le
    (fun d hd0 hev hds => hbase s hsZ s d hd0 hev hds)
  have hSq := GoldbachSquareMean.Sf_sq_sum s
  have hmono : ∑ p ∈ Ww X, ∑ q ∈ (Ww X).filter (p < ·), GoldbachSquareMean.Sf (q-p) ≤
      ∑ p ∈ Pp X, ∑ q ∈ (Pp X).filter (p < ·), GoldbachSquareMean.Sf (q-p) := by
    calc _ ≤ ∑ p ∈ Ww X, ∑ q ∈ (Pp X).filter (p < ·), GoldbachSquareMean.Sf (q-p) :=
          sum_le_sum fun p _ => sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (Ww_sub X (by omega)))
            (fun _ _ _ => GoldbachSquareMean.Sf_nonneg _)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (Ww_sub X (by omega))
            (fun p _ _ => sum_nonneg fun q _ => GoldbachSquareMean.Sf_nonneg _)
  have hPB' : ∑ p ∈ Pp X, ∑ q ∈ (Pp X).filter (p < ·), GoldbachSquareMean.Sf (q-p) ≤
      A * (s:ℝ) / (Real.log (s:ℝ))^2 * (4 * (s:ℝ)) :=
    hPB.trans (mul_le_mul_of_nonneg_left hSq (by positivity))
  have hsX : (s:ℝ) ≤ X := by exact_mod_cast (show s ≤ X by omega)
  have hmean : ∑ p ∈ Ww X, ∑ q ∈ (Ww X).filter (p < ·), GoldbachSquareMean.Sf (q-p) ≤
      16 * A * (X:ℝ)^2 / L^2 := by
    refine hmono.trans (hPB'.trans ?_)
    have hs0 : (0:ℝ) < s := by linarith
    have h1 : A * (s:ℝ) / (Real.log (s:ℝ))^2 * (4 * (s:ℝ)) = 4 * A * (s:ℝ)^2 / (Real.log (s:ℝ))^2 := by
      field_simp
    rw [h1, div_le_div_iff₀ (by positivity) (by positivity)]
    have : L^2 ≤ 4 * (Real.log (s:ℝ))^2 := by nlinarith
    have hs2 : (s:ℝ)^2 ≤ (X:ℝ)^2 := by gcongr
    have hA4 : 0 ≤ A * 4 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hs2 hA4, mul_nonneg (mul_nonneg hA.le (sq_nonneg (s:ℝ))) (sq_nonneg L),
      mul_le_mul_of_nonneg_left this (mul_nonneg hA.le (sq_nonneg (s:ℝ)))]
  set F := A*(X:ℝ)/L^2 with hF
  have hF0 : 0 ≤ F := by positivity
  have htri : (∑ p ∈ Ww X, ∑ q ∈ (Ww X).filter (p < ·),
      ((((Nn X).filter (fun n => p≤n ∧ q≤n ∧ Nat.Prime (n-p) ∧ Nat.Prime (n-q))).card : ℕ) : ℝ))
      ≤ F * (16 * A * (X:ℝ)^2 / L^2) := by
    calc
      _ ≤ ∑ p ∈ Ww X, ∑ q ∈ (Ww X).filter (p < ·), F*GoldbachSquareMean.Sf (q-p) := by
        apply sum_le_sum
        intro p hp
        apply sum_le_sum
        intro q hq
        obtain ⟨hq, hpq⟩ := mem_filter.mp hq
        have h := hpair p q hp hq hpq
        convert h using 1
        rw [hF]; ring
      _ = F*(∑ p ∈ Ww X, ∑ q ∈ (Ww X).filter (p < ·), GoldbachSquareMean.Sf (q-p)) := by
        simp only [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hmean hF0
  have hcoll := collisions (Nn X) (Ww X)
  have hcollR : (∑ n ∈ Nn X, ((Hh X n * (Hh X n - 1) : ℕ):ℝ)) =
      ∑ p ∈ Ww X, ∑ q ∈ (Ww X).erase p,
        ((((Nn X).filter (fun n => p≤n ∧ q≤n ∧ Nat.Prime (n-p) ∧ Nat.Prime (n-q))).card : ℕ) : ℝ) := by
    exact_mod_cast hcoll
  rw [offDiagonal (Ww X) (fun p q =>
    ((((Nn X).filter (fun n => p≤n ∧ q≤n ∧ Nat.Prime (n-p) ∧ Nat.Prime (n-q))).card : ℕ) : ℝ))
    (fun p q => by
      change _ = _
      exact hsym p q)] at hcollR
  have hdiag : (∑ n ∈ Nn X, (Hh X n:ℝ)) ≤ (X:ℝ)^2 := by
    have he : (Nn X).card ≤ X := (card_filter_le ..).trans (by simp; omega)
    have hp : (Ww X).card ≤ X := (card_filter_le ..).trans (by simp; omega)
    calc
      _ ≤ ∑ _n ∈ Nn X, ((Ww X).card:ℝ) := sum_le_sum fun n _ => by exact_mod_cast (card_filter_le (Ww X) _)
      _ = ((Nn X).card:ℝ)*((Ww X).card:ℝ) := by simp [nsmul_eq_mul]
      _ ≤ (X:ℝ)*(X:ℝ) := mul_le_mul (by exact_mod_cast he) (by exact_mod_cast hp) (by positivity) (by positivity)
      _ = _ := by ring
  have hsplit (n : ℕ) : (Hh X n:ℝ)^2 = ((Hh X n * (Hh X n - 1):ℕ):ℝ) + Hh X n := by
    have h (k : ℕ) : k^2 = k*(k-1)+k := by cases k <;> simp <;> ring
    exact_mod_cast h (Hh X n)
  simp_rw [hsplit]
  rw [sum_add_distrib, hcollR]
  set R := (X:ℝ) / L^2 with hR
  have hRL : R * L^2 = X := by rw [hR]; field_simp
  have hR0 : 0 ≤ R := by positivity
  have hdiag2 : (X:ℝ)^2 ≤ X * R^2 := by
    have : (X:ℝ)^2 = R^2 * (L^2)^2 := by rw [← hRL]; ring
    rw [this]
    have h4 : (L^2)^2 ≤ X := by nlinarith [hlog4]
    nlinarith [mul_le_mul_of_nonneg_left h4 (sq_nonneg R)]
  have hoff : 2 * (F * (16 * A * (X:ℝ)^2 / L^2)) = 32 * A^2 * X * R^2 := by
    rw [hF, hR]; field_simp; ring
  nlinarith [htri, hdiag, hdiag2, hoff]

end Conjectures.Goldbach.BSD

open Conjectures.Goldbach.BSD
open Finset

theorem Conjectures.Goldbach.BeaumontScaledDeletionSurvival :
    let H := fun n : ℕ => ((Finset.range (n+1)).filter (fun p => p.Prime ∧ p ≤ n ∧ (n-p).Prime ∧ n ≤ 3*p ∧ 3*p ≤ 2*n)).card; let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n); let M := fun X : ℕ => (X:ℝ)/(Real.log (X:ℝ))^2; ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ D : Finset ℕ, (D.card:ℝ) ≤ c*(X:ℝ)/Real.log (X:ℝ) → δ*(X:ℝ) ≤ (((E X).filter (fun n => ∃ p ≤ n, p.Prime ∧ (n-p).Prime ∧ n ≤ 3*p ∧ 3*p ≤ 2*n ∧ n-p ∉ D)).card:ℝ) := by
  intro H E M
  classical
  obtain ⟨k, hq⟩ := q_lower
  obtain ⟨b, hb, X₁, hsec⟩ := second_moment
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hcu : 0 < 4 * Real.log 4 := by positivity
  refine ⟨1/(1250*(4 * Real.log 4)), 1/(1250^2*b), by positivity, by positivity, max 16 (max k X₁), ?_⟩
  intro X hX D hD
  have hx : (0:ℝ) < X := by exact_mod_cast (show 0<X by omega)
  have hL : 0 < Real.log (X:ℝ) := Real.log_pos (by exact_mod_cast (show 1<X by omega))
  set L := Real.log (X:ℝ) with hLdef
  set R := (X:ℝ) / L^2 with hR
  have hRL : R * L^2 = X := by rw [hR]; field_simp
  have hR0 : 0 < R := by positivity
  have hQ := hq X (by omega)
  have hP := p_upper X (by omega)
  have hfm : (((Qq X).card:ℝ))^2 ≤ ∑ n ∈ Nn X, (Hh X n:ℝ) := by
    exact_mod_cast first_moment X (by omega)
  set G := (Nn X).filter (fun n => ∃ p ∈ Ww X, p ≤ n ∧ Nat.Prime (n-p) ∧ n-p ∉ D) with hG
  have hlostN : (∑ n ∈ Nn X, Hh X n) ≤ (∑ n ∈ G, Hh X n) + (Ww X).card * D.card :=
    lost (Nn X) (Ww X) D
  have hlost : (∑ n ∈ Nn X, (Hh X n:ℝ)) ≤ (∑ n ∈ G, (Hh X n:ℝ)) + ((Ww X).card:ℝ) * D.card := by
    exact_mod_cast hlostN
  have hWP : ((Ww X).card:ℝ) ≤ (Pp X).card := by
    exact_mod_cast card_le_card (Ww_sub X (by omega))
  have hq0 : (0:ℝ) ≤ (Qq X).card := Nat.cast_nonneg _
  have hD0 : (0:ℝ) ≤ D.card := Nat.cast_nonneg _
  have hP0 : (0:ℝ) ≤ (Pp X).card := Nat.cast_nonneg _
  have hDL : (D.card:ℝ) * L ≤ 1/(1250*(4 * Real.log 4)) * X := by
    have := mul_le_mul_of_nonneg_right hD hL.le
    rw [div_mul_cancel₀ _ hL.ne'] at this
    exact this
  have hqsq : (X:ℝ) * R / 625 ≤ ((Qq X).card:ℝ)^2 := by
    have h1 : (X:ℝ)/25 ≤ (Qq X).card * L := by linarith
    have h2 := pow_le_pow_left₀ (by positivity) h1 2
    have h3 : (X:ℝ) * R / 625 * L^2 ≤ ((Qq X).card:ℝ)^2 * L^2 := by
      have : (X:ℝ) * R / 625 * L^2 = ((X:ℝ)/25)^2 := by
        rw [show (X:ℝ) * R / 625 * L^2 = X * (R * L^2) / 625 by ring, hRL]; ring
      rw [this]; nlinarith [h2]
    exact le_of_mul_le_mul_right h3 (by positivity)
  have hcost : ((Ww X).card:ℝ) * D.card ≤ (X:ℝ) * R / 1250 := by
    have h1 : ((Pp X).card:ℝ) * L ≤ (4 * Real.log 4) * X := hP
    have h2 := mul_le_mul h1 hDL (by positivity) (by positivity)
    have h3 : ((Ww X).card:ℝ) * D.card * L^2 ≤ (X:ℝ) * R / 1250 * L^2 := by
      have e : (X:ℝ) * R / 1250 * L^2 = (X:ℝ) * (R * L^2) / 1250 := by ring
      rw [e, hRL]
      have e2 : (4 * Real.log 4 * X) * (1/(1250*(4 * Real.log 4)) * X) = (X:ℝ)*X/1250 := by
        field_simp
      have : ((Ww X).card:ℝ) * D.card * L^2 ≤ ((Pp X).card:ℝ) * L * (D.card * L) := by
        have := mul_le_mul_of_nonneg_right hWP (mul_nonneg hD0 (sq_nonneg L))
        nlinarith [this]
      nlinarith [this, h2, e2]
    exact le_of_mul_le_mul_right h3 (by positivity)
  have hgood : (X:ℝ) * R / 1250 ≤ ∑ n ∈ G, (Hh X n:ℝ) := by linarith
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ (X:ℝ) * R / 1250) hgood 2
  have hCS := sq_sum_le_card_mul_sum_sq (s:=G) (f:=fun n => (Hh X n:ℝ))
  have hrest : (∑ n ∈ G, (Hh X n:ℝ)^2) ≤ b * X * R^2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun n _ _ => sq_nonneg _)).trans
      (hsec X (by omega))
  have htop := hsq.trans (hCS.trans (mul_le_mul_of_nonneg_left hrest (Nat.cast_nonneg (α:=ℝ) G.card)))
  have hsub : G ⊆ (E X).filter (fun n => ∃ p ≤ n, p.Prime ∧ (n-p).Prime ∧ n ≤ 3*p ∧ 3*p ≤ 2*n ∧ n-p ∉ D) := by
    intro n hn
    obtain ⟨hnN, p, hpW, hpn, hpp, hpD⟩ := mem_filter.mp hn
    obtain ⟨hnI, hnE⟩ := mem_filter.mp hnN
    obtain ⟨hpI, hpPr⟩ := mem_filter.mp hpW
    obtain ⟨hn1, hn2⟩ := mem_Icc.mp hnI
    obtain ⟨hp1, hp2⟩ := mem_Icc.mp hpI
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hnE⟩,
      p, hpn, hpPr, hpp, by omega, by omega, hpD⟩
  have hcard : (G.card:ℝ) ≤ (((E X).filter (fun n => ∃ p ≤ n, p.Prime ∧ (n-p).Prime ∧ n ≤ 3*p ∧ 3*p ≤ 2*n ∧ n-p ∉ D)).card:ℝ) := by
    exact_mod_cast card_le_card hsub
  refine le_trans ?_ hcard
  have hXR : 0 < (b * X * R^2) := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  apply le_of_mul_le_mul_right _ hXR
  nlinarith [htop, hRL]

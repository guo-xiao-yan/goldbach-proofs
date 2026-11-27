import Mathlib

section
namespace OAI
namespace Ostmann
open scoped Classical BigOperators
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
structure PrimitiveComplexCharacter where
  modulus : ℕ
  positive : 0 < modulus
  character : DirichletCharacter ℂ modulus
  primitive : character.IsPrimitive
  nontrivial : character ≠ 1
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
noncomputable def PrimitiveComplexCharacter.L (χ : PrimitiveComplexCharacter) : ℂ → ℂ :=
  @DirichletCharacter.LFunction χ.modulus ⟨χ.positive.ne'⟩ χ.character
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
structure ComplexZeroEnumeration (χ : PrimitiveComplexCharacter) where
  zeros : ℕ → ℂ
  in_strip : ∀ i, 0 < (zeros i).re ∧ (zeros i).re < 1
  actual_zero : ∀ i, χ.L (zeros i) = 0
  finite_height : ∀ T : ℝ, {i | |(zeros i).im| ≤ T}.Finite
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
noncomputable def ComplexZeroEnumeration.V14 {χ : PrimitiveComplexCharacter}
    (Z : ComplexZeroEnumeration χ) (T : ℝ) : Finset ℕ := (Z.finite_height T).toFinset
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
noncomputable def ComplexZeroEnumeration.count {χ : PrimitiveComplexCharacter}
    (Z : ComplexZeroEnumeration χ) (σ T : ℝ) : ℕ :=
  ((Z.V14 T).filter (fun i => σ ≤ (Z.zeros i).re)).card
end Ostmann
end OAI
end
section
namespace OAI
namespace Ostmann
open Complex MeasureTheory Set
open scoped Interval BigOperators
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
structure RectangleIntegrable (f : ℂ → ℂ) (a b c d : ℝ) : Prop where
  bottom : IntervalIntegrable (fun x : ℝ => f (x + c * I)) volume a b
  top : IntervalIntegrable (fun x : ℝ => f (x + d * I)) volume a b
  right : IntervalIntegrable (fun y : ℝ => f (b + y * I)) volume c d
  left : IntervalIntegrable (fun y : ℝ => f (a + y * I)) volume c d
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
theorem RectangleIntegrable.add {f g : ℂ → ℂ} {a b c d : ℝ}
    (hf : RectangleIntegrable f a b c d) (hg : RectangleIntegrable g a b c d) :
    RectangleIntegrable (fun z => f z + g z) a b c d :=
  ⟨hf.bottom.add hg.bottom, hf.top.add hg.top, hf.right.add hg.right, hf.left.add hg.left⟩
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
theorem RectangleIntegrable.const_mul {f : ℂ → ℂ} {a b c d : ℝ}
    (hf : RectangleIntegrable f a b c d) (v : ℂ) :
    RectangleIntegrable (fun z => v * f z) a b c d :=
  ⟨hf.bottom.const_mul v, hf.top.const_mul v, hf.right.const_mul v, hf.left.const_mul v⟩
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
theorem RectangleIntegrable.sum {ι : Type*} (S : Finset ι) {f : ι → ℂ → ℂ} {a b c d : ℝ}
    (h : ∀ i ∈ S, RectangleIntegrable (f i) a b c d) :
    RectangleIntegrable (fun z => ∑ i ∈ S, f i z) a b c d := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact ⟨by simp, by simp, by simp, by simp⟩
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
end Ostmann
end OAI
end
section
namespace OAI
namespace Ostmann
open scoped BigOperators
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
structure PrimitiveRealCharacter where
  modulus : ℕ
  positive : 0 < modulus
  character : DirichletCharacter ℝ modulus
  primitive : character.IsPrimitive
  nontrivial : character ≠ 1
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
noncomputable def PrimitiveRealCharacter.V2g (χ : PrimitiveRealCharacter) :
    DirichletCharacter ℂ χ.modulus := χ.character.ringHomComp Complex.ofRealHom
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
noncomputable def PrimitiveRealCharacter.L (χ : PrimitiveRealCharacter) : ℂ → ℂ :=
  @DirichletCharacter.LFunction χ.modulus ⟨χ.positive.ne'⟩ χ.V2g
end Ostmann
end OAI
end
section
section
namespace Int
variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R] [FloorRing R]
theorem V1zr (a : R) : |fract a| ≤ 1 := by
  rw [abs_fract]
  exact (fract_lt_one a).le
end Int
end
end
section
section
namespace Complex
theorem Vkv {r : ℂ} {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun u : ℝ => (u : ℂ) ^ r) (Set.Icc a b) :=
  ((continuous_ofReal.continuousOn :
      ContinuousOn (fun u : ℝ => (u : ℂ)) (Set.Icc a b)).cpow continuousOn_const
    (fun _ hu => (ofReal_mem_slitPlane).2 (lt_of_lt_of_le ha hu.1))).mono Set.Subset.rfl
end Complex
end
end
section
section
open scoped Topology
open Real Set Filter Topology MeasureTheory Complex
noncomputable def Vq (s : ℂ) (u : ℝ) : ℂ :=
  ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)
theorem V8c (u : ℝ) (hu : 1 ≤ u) (s : ℂ) :
    ‖Vq s u‖ ≤ u ^ (-s.re - 1) := by
  have hu0 : 0 < u := one_pos.trans_le hu
  have hfract_le1 : ‖((Int.fract u : ℝ) : ℂ)‖ ≤ 1 := by simpa using Int.V1zr u
  have hle : ‖Vq s u‖ ≤ ‖(u : ℂ) ^ (-s - 1)‖ := by
    calc
      _ = ‖((Int.fract u : ℝ) : ℂ)‖ * ‖(u : ℂ) ^ (-s - 1)‖ := by rw [Vq, norm_mul]
      _ ≤ 1 * ‖(u : ℂ) ^ (-s - 1)‖ := by
        exact mul_le_mul_of_nonneg_right hfract_le1 (norm_nonneg _)
      _ = ‖(u : ℂ) ^ (-s - 1)‖ := one_mul _
  have hb : ‖(u : ℂ) ^ (-s - 1)‖ = u ^ (-s.re - 1) := by
    have hre : (-s - 1).re = -s.re - 1 := by
      simp [sub_eq_add_neg]
    simpa [hre] using Complex.norm_cpow_eq_rpow_re_of_pos hu0 (-s - 1)
  exact hle.trans_eq hb
namespace Vhw
lemma aestronglyMeasurable (s : ℂ) (S : Set ℝ) (_ : MeasurableSet S) :
    AEStronglyMeasurable (fun u => Vq s u) (volume.restrict S) := by
  refine (measurable_fract.complex_ofReal.mul ?_).aestronglyMeasurable
  simpa using Complex.measurable_ofReal.pow_const (-s - 1)
lemma intervalIntegrable (s : ℂ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u => Vq s u) volume a b := by
  let μ := volume.restrict (Icc a b)
  set g : ℝ → ℝ := fun u => ‖(u : ℂ) ^ (-s - 1)‖
  have hmeas := aestronglyMeasurable s (Icc a b) measurableSet_Icc
  have hbound_ae : ∀ᵐ u ∂μ, ‖Vq s u‖ ≤ g u := by
    refine (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ ?_)
    intro u huIcc
    have hu0 : 0 < u := lt_of_lt_of_le one_pos (ha.trans huIcc.1)
    have hg_eq : g u = u ^ (-s.re - 1) := by
      simp [g, Complex.norm_cpow_eq_rpow_re_of_pos hu0, sub_eq_add_neg]
    exact (V8c u (ha.trans huIcc.1) s).trans (le_of_eq hg_eq.symm)
  have hg : Integrable g μ := by
    simpa [μ, g] using!
      (Complex.Vkv (ha := one_pos.trans_le ha)).norm.integrableOn_compact
        isCompact_Icc
  have hf0 : Integrable (fun _ : ℝ => (0 : ℂ)) μ := by simp [μ]
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 <|
    integrable_of_norm_sub_le hmeas hf0 hg
      (hbound_ae.mono fun u hu => by simpa [sub_eq_add_neg, μ, g] using hu)
end Vhw
end
end
section
namespace OAI
namespace V2
open Finset MeasureTheory
open scoped ComplexConjugate
local instance : Fact (0 < (1:ℝ)) := ⟨by norm_num⟩
noncomputable def Va (k : ℕ) : Measure (Fin k → AddCircle (1:ℝ)) :=
  Measure.pi (fun _ => AddCircle.haarAddCircle)
instance (k : ℕ) : IsProbabilityMeasure (Va k) := by
  unfold Va
  infer_instance
end V2
end OAI
end
section
namespace OAI
namespace Vah
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open Asymptotics
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
open scoped ComplexConjugate
open Filter Topology
open Complex Filter Topology
open Complex Filter Topology Set MeasureTheory Asymptotics
open Finset
open Complex Filter Topology Finset
open scoped ComplexOrder in
open scoped ComplexOrder in
open scoped ComplexOrder in
open Complex Filter Topology Finset Set MeasureTheory
open Complex Finset ArithmeticFunction
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
def V7b (p : ℕ) (f g : ArithmeticFunction ℂ) : Prop :=
  ∀ k : ℕ, f (p^k) = g (p^k)
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
lemma V7b.mul {p : ℕ} (hp : p.Prime) {f f' g g' : ArithmeticFunction ℂ}
    (hf : V7b p f f') (hg : V7b p g g') : V7b p (f*g) (f'*g') := by
  intro k
  simp only [ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨i,hi,hxi⟩ := (Nat.dvd_prime_pow hp).mp (Nat.mem_divisors.mp
    (Nat.fst_mem_divisors_of_mem_antidiagonal hx)).1
  obtain ⟨j,hj,hxj⟩ := (Nat.dvd_prime_pow hp).mp (Nat.mem_divisors.mp
    (Nat.snd_mem_divisors_of_mem_antidiagonal hx)).1
  rw [hxi,hxj,hf,hg]
end Vah
end OAI
end
section
section GoldbachDeepFourthPrimeDenominator
namespace V31
open Finset
noncomputable def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
theorem V13v (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring
noncomputable def Vb2 (k : ℕ) : ℝ := if k.Prime then Real.log (k : ℝ) else 0
noncomputable def Vi3 (n : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ range (n + 1), (Vb2 k : ℂ) * phase ((k : ℝ) * t)
end V31
end GoldbachDeepFourthPrimeDenominator
section GoldbachWideArcSeparation
open Filter
open scoped Topology
namespace V1si
theorem Vwx {n H B q r a b : ℕ} {t : ℝ}
    (hn : 2 * H * B < n) (hq : 1 ≤ q) (hr : 1 ≤ r) (hqB : q ≤ B) (hrB : r ≤ B)
    (hca : a.Coprime q) (hcb : b.Coprime r)
    (ha : |t - (a : ℝ)/q| ≤ (H : ℝ)/((q : ℝ)*n))
    (hb : |t - (b : ℝ)/r| ≤ (H : ℝ)/((r : ℝ)*n)) : q = r ∧ a = b := by
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq
  have hrr : 0 < (r : ℝ) := by exact_mod_cast hr
  have hnr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hsmall : H*r + H*q < n := by
    nlinarith only [hn, Nat.mul_le_mul_left H hrB, Nat.mul_le_mul_left H hqB]
  have hradii : (H : ℝ)/(q*n) + H/(r*n) < 1/(q*r) := calc
    _ = ((H : ℝ)*r+H*q)/(q*r*n) := by field_simp
    _ < (n : ℝ)/(q*r*n) := (div_lt_div_iff_of_pos_right (by positivity)).mpr (by exact_mod_cast hsmall)
    _ = _ := by field_simp
  have he : a*r = b*q := by
    by_contra hne
    have hsep : 1/((q : ℝ)*r) ≤ |(a : ℝ)/q - b/r| := by
      rw [show (a:ℝ)/q - b/r = (a*r-b*q)/(q*r) by field_simp, abs_div, abs_of_pos (mul_pos hqr hrr)]
      apply (div_le_div_iff_of_pos_right (mul_pos hqr hrr)).mpr
      rcases lt_or_gt_of_ne hne with hab | hba
      · have hgap : (a:ℝ)*r + 1 ≤ b*q := by exact_mod_cast Nat.succ_le_of_lt hab
        linarith [neg_le_abs ((a:ℝ)*r - b*q)]
      · have hgap : (b:ℝ)*q + 1 ≤ a*r := by exact_mod_cast Nat.succ_le_of_lt hba
        linarith [le_abs_self ((a:ℝ)*r - b*q)]
    have htriangle := abs_sub_le ((a:ℝ)/q) t ((b:ℝ)/r)
    rw [abs_sub_comm ((a:ℝ)/q) t] at htriangle
    linarith
  have hdiv₁ : q ∣ r := hca.symm.dvd_of_dvd_mul_left (he ▸ dvd_mul_left q b)
  have hdiv₂ : r ∣ q := hcb.symm.dvd_of_dvd_mul_left (he.symm ▸ dvd_mul_left r a)
  obtain rfl := Nat.dvd_antisymm hdiv₁ hdiv₂
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right hq he⟩
end V1si
end GoldbachWideArcSeparation
section GoldbachDeepFourthGeometry
open Filter
open scoped Topology
private theorem V1o8 :
    ∃ N : ℕ, ∀ n ≥ N,
      let Q := (Nat.log 2 (n+2))^2
      let Q₁ := ⌊(n : ℝ)^(1/3 : ℝ)⌋₊
      let H := 256 * Q₁ * Q
      2 * H * (4*Q₁) < n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let c : ℝ := Real.log 2 / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hlim : Tendsto (fun x : ℝ => Real.log x ^ (2 : ℕ) / x^(1/3 : ℝ)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (s := 1/3) 2 (by norm_num)).tendsto_div_nhds_zero
    have heq (x : ℝ) : Real.log x ^ (2 : ℝ) = Real.log x ^ (2 : ℕ) := by
      simpa only [Nat.cast_ofNat] using Real.rpow_natCast (Real.log x) 2
    simpa only [heq] using h
  have hseq := hlim.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hε : 0 < c^2/2048 := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hseq.eventually_lt_const hε)
  refine ⟨max N 2, ?_⟩
  intro n hn Q Q₁ H
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  let z := (n : ℝ)^(1/3 : ℝ)
  have hz : 0 < z := Real.rpow_pos_of_pos hnpos _
  have hpow : (2 : ℝ) ^ Nat.log 2 (n+2) ≤ ((n+2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n+2 ≠ 0)
  have hlogbase := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ Nat.log 2 (n+2)) hpow
  rw [Real.log_pow] at hlogbase
  have hlogplus : Real.log ((n+2 : ℕ) : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    have hcomp : ((n+2 : ℕ) : ℝ) ≤ (n : ℝ)^2 := by
      push_cast
      nlinarith only [hnR, sq_nonneg ((n : ℝ) - 2)]
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (by positivity : 0 < ((n+2 : ℕ) : ℝ)) hcomp
  have hnatlog : (Nat.log 2 (n+2) : ℝ) ≤ Real.log (n : ℝ) / c := by
    apply (le_div_iff₀ hc).2
    dsimp [c]
    linarith only [hlogbase, hlogplus]
  have hsmall : Real.log (n : ℝ)^2 / z < c^2/2048 := hN n hnN
  have hscaled : 2048 * (Real.log (n : ℝ) / c)^2 < z := by
    have h1 := (div_lt_iff₀ hz).1 hsmall
    have h2 := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2048)).1
      (show Real.log (n : ℝ)^2 < c^2*z/2048 by simpa only [div_mul_eq_mul_div] using h1)
    rw [div_pow, ← mul_div_assoc]
    apply (div_lt_iff₀ (sq_pos_of_pos hc)).2
    simpa only [mul_comm] using h2
  have hQ : (2048 : ℝ) * (Q : ℝ) < z := by
    have hsq : (Q : ℝ) ≤ (Real.log (n : ℝ) / c)^2 := by
      dsimp [Q]
      push_cast
      exact pow_le_pow_left₀ (by positivity) hnatlog _
    exact (mul_le_mul_of_nonneg_left hsq (by norm_num)).trans_lt hscaled
  have hB : (Q₁ : ℝ) ≤ z := Nat.floor_le hz.le
  have hz3 : z * z^2 = (n : ℝ) := by
    have heq : z^2 = (n : ℝ)^(2/3 : ℝ) := by
      dsimp [z]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
      norm_num
    rw [heq]
    dsimp [z]
    rw [← Real.rpow_add hnpos]
    norm_num
  have hr : (2048 : ℝ) * (Q : ℝ) * (Q₁ : ℝ)^2 < (n : ℝ) := calc
    _ ≤ 2048 * (Q : ℝ) * z^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hB _) (by positivity)
    _ < z * z^2 := mul_lt_mul_of_pos_right hQ (sq_pos_of_pos hz)
    _ = _ := hz3
  have hnat : 2048 * Q * Q₁^2 < n := by exact_mod_cast hr
  change 2 * (256 * Q₁ * Q) * (4*Q₁) < n
  rw [show 2 * (256 * Q₁ * Q) * (4*Q₁) = 2048 * Q * Q₁^2 by ring]
  exact hnat
open Set
namespace Vpg
noncomputable def wide (n R H : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤R ∧ a≤q ∧ Nat.Coprime a q ∧
    |t - (a:ℝ)/q| ≤ (H:ℝ)/((q:ℝ)*n)}
theorem V1pz :
    ∃ N : ℕ, ∀ n ≥ N,
      let R := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
      let H := 256 * R * (Nat.log 2 (n+2))^2
      2*H*(4*R) < n ∧ 4*R ≤ H ∧ 4*R ≤ n := by
  obtain ⟨N,hN⟩ := V1o8
  refine ⟨N, ?_⟩
  intro n hn R H
  have hbudget : 2*H*(4*R) < n := hN n hn
  have hlog : 1 ≤ Nat.log 2 (n+2) := Nat.log_pos (by decide) (by omega)
  have hH : 4*R ≤ H := calc
    _ ≤ 256*R := Nat.mul_le_mul_right _ (by decide)
    _ = 256*R*1 := by simp
    _ ≤ H := Nat.mul_le_mul_left _ (by
      have hx := Nat.pow_le_pow_left hlog 2
      simpa using hx)
  have hsize : 4*R ≤ n := by
    by_cases hzero : R=0
    · simp [hzero]
    · have hHp : 1 ≤ H := by omega
      exact (Nat.le_mul_of_pos_left _ (show 0<2*H by omega)).trans hbudget.le
  exact ⟨hbudget,hH,hsize⟩
end Vpg
end GoldbachDeepFourthGeometry
section GoldbachDiscreteWindowEstimate
open Finset MeasureTheory
open scoped ComplexConjugate Interval
namespace Vcr
open V31 (phase V13v)
noncomputable def poly (N : ℕ) (b : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ j ∈ range N, b j * phase ((j : ℝ) * t)
private theorem V23c : Continuous phase := by unfold phase; fun_prop
private theorem V22o (N : ℕ) (b : ℕ → ℂ) : Continuous (poly N b) := by
  unfold poly
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (V23c.comp (by fun_prop))
private theorem V23p (m : ℤ) : phase (m : ℝ) = 1 := by
  unfold phase
  have h : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) =
      (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]
private theorem V21m (m : ℤ) :
    (∫ t in (0 : ℝ)..1, phase ((m : ℝ) * t)) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    simp [phase]
  let c : ℂ := (m : ℂ) * (2 * Real.pi * Complex.I)
  have he (t : ℝ) : phase ((m : ℝ) * t) = Complex.exp (c * (t : ℂ)) := by
    unfold phase c
    congr 1
    push_cast
    ring
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (by exact_mod_cast hm)
      (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero))
        Complex.I_ne_zero)
  simp_rw [he]
  rw [integral_exp_mul_complex hc]
  simp [hm, c, Complex.exp_int_mul_two_pi_mul_I]
private theorem V23d (t : ℝ) : conj (phase t) = phase (-t) := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring
theorem V23f (N : ℕ) (b : ℕ → ℂ) :
    (∫ t in (0 : ℝ)..1, ‖poly N b t‖^2) = ∑ k ∈ range N, ‖b k‖^2 := by
  let term (k j : ℕ) (t : ℝ) :=
    (conj (b k) * b j) * phase ((((j : ℤ) - (k : ℤ)) : ℝ) * t)
  let cross (t : ℝ) := ∑ k ∈ range N, ∑ j ∈ range N, term k j t
  have hc (k j : ℕ) : Continuous (term k j) := by
    unfold term phase
    fun_prop
  have hcross : Continuous cross := continuous_finsetSum _ fun k _ =>
    continuous_finsetSum _ fun j _ => hc k j
  have hexpand (t : ℝ) : ((‖poly N b t‖^2 : ℝ) : ℂ) = cross t := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    simp only [poly, cross, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    dsimp [term]
    simp only [map_mul, V23d]
    simp only [Int.cast_natCast]
    rw [show ((j : ℝ) - (k : ℝ)) * t =
      -((k : ℝ) * t) + (j : ℝ) * t by ring, V13v]
    ring
  have hint : (∫ t in (0 : ℝ)..1, cross t) = (↑(∑ k ∈ range N, ‖b k‖^2) : ℂ) := by
    dsimp only [cross]
    rw [intervalIntegral.integral_finsetSum
      (fun k _ => (continuous_finsetSum _ fun j _ => hc k j).intervalIntegrable _ _),
      Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [intervalIntegral.integral_finsetSum fun j _ => (hc k j).intervalIntegrable _ _]
    have hmode (j : ℕ) : (∫ t in (0 : ℝ)..1, term k j t) =
        (conj (b k) * b j) * (if j = k then 1 else 0) := by
      have hm : (∫ t in (0 : ℝ)..1, phase (((j : ℝ) - (k : ℝ)) * t)) =
          if j = k then 1 else 0 := by
        simpa only [Int.cast_sub, Int.cast_natCast, sub_eq_zero, Int.ofNat_inj]
          using V21m ((j : ℤ) - (k : ℤ))
      unfold term
      rw [intervalIntegral.integral_const_mul]
      exact congrArg ((conj (b k) * b j) * ·) hm
    simp only [hmode]
    rw [Finset.sum_eq_single_of_mem k hk]
    · simp [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    · intro j _ hne
      simp [hne]
  have hre :
      (∫ t in (0 : ℝ)..1, (cross t).re) = (∫ t in (0 : ℝ)..1, cross t).re := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact integral_re (hcross.intervalIntegrable (0 : ℝ) 1).1
  calc
    _ = ∫ t in (0 : ℝ)..1, (cross t).re := by
      apply intervalIntegral.integral_congr
      intro t _
      simpa only [Complex.ofReal_re] using congrArg Complex.re (hexpand t)
    _ = _ := by rw [hre, hint, Complex.ofReal_re]
noncomputable def moving (N h : ℕ) (b : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ x ∈ ((range N) ×ˢ (range h)).filter (fun x => x.1 + x.2 = m), b x.1
theorem V21l (N h : ℕ) (b : ℕ → ℂ) (m : ℕ) :
    moving N h b m = ∑ k ∈ (range N).filter (fun k => m + 1 - h ≤ k ∧ k ≤ m), b k := by
  classical
  unfold moving
  refine Finset.sum_bij (fun x _ => x.1) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro x hx
    obtain ⟨⟨hk, hj⟩, heq⟩ := (Finset.mem_filter.mp hx).imp (fun hp => Finset.mem_product.mp hp) id
    have hj' := mem_range.mp hj
    exact Finset.mem_filter.mpr ⟨hk, by omega, by omega⟩
  · intro x hx y hy hxy
    have heqx := (Finset.mem_filter.mp hx).2
    have heqy := (Finset.mem_filter.mp hy).2
    exact Prod.ext hxy (by omega)
  · intro k hk
    obtain ⟨hk', hlo, hhi⟩ := Finset.mem_filter.mp hk
    refine ⟨(k, m - k), ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hk', mem_range.mpr (by omega)⟩, by omega⟩
theorem V20d (N h : ℕ) (b : ℕ → ℂ) (t : ℝ) :
    poly (N + h) (moving N h b) t = poly N b t * poly h (fun _ => 1) t := by
  unfold poly
  have hmaps (x : ℕ × ℕ) (hx : x ∈ (range N) ×ˢ (range h)) :
      x.1 + x.2 ∈ range (N + h) := by
    obtain ⟨hk, hj⟩ := Finset.mem_product.mp hx
    simp only [Finset.mem_range] at hk hj
    exact mem_range.mpr (by omega)
  calc
    _ = ∑ m ∈ range (N + h), ∑ x ∈ ((range N) ×ˢ (range h)).filter
        (fun x => x.1 + x.2 = m), b x.1 * phase ((x.1 : ℝ) * t + (x.2 : ℝ) * t) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [moving, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      have hsum := (Finset.mem_filter.mp hx).2
      have hsumR : (x.1 : ℝ) + x.2 = m := by exact_mod_cast hsum
      rw [← add_mul, hsumR]
    _ = ∑ x ∈ (range N) ×ˢ (range h), b x.1 * phase ((x.1 : ℝ) * t + (x.2 : ℝ) * t) :=
      Finset.sum_fiberwise_of_maps_to hmaps _
    _ = _ := by
      rw [Finset.sum_product, Finset.sum_mul_sum]
      simp only [one_mul, V13v, mul_assoc]
private theorem V23v {h : ℕ} {t : ℝ} (ht : 6 * (h : ℝ) * |t| ≤ 1) :
    (h : ℝ) / 2 ≤ ‖poly h (fun _ => 1) t‖ := by
  apply le_trans _ (Complex.re_le_norm _)
  unfold poly
  simp only [one_mul, Complex.re_sum, phase, Complex.exp_ofReal_mul_I_re]
  calc
    _ = ∑ _ ∈ range h, (1 / 2 : ℝ) := by rw [Finset.sum_const, card_range, nsmul_eq_mul]; ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      have hjh : (j : ℝ) ≤ h := by exact_mod_cast (mem_range.mp hj).le
      have hfac := mul_le_mul_of_nonneg_right hjh (abs_nonneg t)
      have hangle : |2 * Real.pi * ((j : ℝ) * t)| ≤ Real.pi / 3 := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi), abs_mul,
          abs_of_nonneg (Nat.cast_nonneg j : 0 ≤ (j : ℝ))]
        calc
          _ ≤ (2 * Real.pi) * ((h : ℝ) * |t|) := mul_le_mul_of_nonneg_left hfac (by positivity)
          _ ≤ _ := by
            have h' : (h : ℝ) * |t| ≤ 1 / 6 := by linarith only [ht]
            have h'' := mul_le_mul_of_nonneg_left h' (show 0 ≤ 2 * Real.pi by positivity)
            linarith only [h'']
      rw [← Real.cos_pi_div_three, ← Real.cos_abs (2 * Real.pi * ((j : ℝ) * t))]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hangle
set_option maxHeartbeats 600000 in
theorem V1zo (N h : ℕ) (b : ℕ → ℂ) (δ : ℝ)
    (hpos : 0 < h) (hδ : 0 ≤ δ) (hwidth : 6 * (h : ℝ) * δ ≤ 1) :
    (h : ℝ)^2 / 4 * (∫ t in (-δ)..δ, ‖poly N b t‖^2) ≤
      ∑ m ∈ range (N + h), ‖moving N h b m‖^2 := by
  have hδsmall : δ ≤ 1 / 2 := by
    have hh : (1 : ℝ) ≤ h := by exact_mod_cast hpos
    have hmul := mul_le_mul_of_nonneg_right hh hδ
    nlinarith only [hmul, hwidth]
  have hre : -δ ≤ δ := by linarith
  have hline (t : ℝ) (ht : t ∈ Set.Icc (-δ) δ) :
      (h : ℝ)^2 / 4 * ‖poly N b t‖^2 ≤ ‖poly (N + h) (moving N h b) t‖^2 := by
    have ht' : |t| ≤ δ := abs_le.mpr ht
    have hb := V23v ((mul_le_mul_of_nonneg_left ht'
      (by positivity : 0 ≤ 6 * (h : ℝ))).trans hwidth)
    rw [V20d, norm_mul, mul_pow]
    have hb' := pow_le_pow_left₀ (by positivity : 0 ≤ (h : ℝ) / 2) hb 2
    rw [show (h : ℝ)^2 / 4 = ((h : ℝ) / 2)^2 by ring, mul_comm]
    exact mul_le_mul_of_nonneg_left hb' (by positivity)
  let F (t : ℝ) := ‖poly (N + h) (moving N h b) t‖^2
  have hF : Continuous F := (V22o _ _).norm.pow 2
  have hpolyper : Function.Periodic (poly (N + h) (moving N h b)) 1 := by
    intro t
    unfold poly
    apply Finset.sum_congr rfl
    intro m _
    have hm : phase (m : ℝ) = 1 := by
      simpa only [Int.cast_natCast] using V23p (m : ℤ)
    rw [mul_add, V13v, mul_one, hm, mul_one]
  have hper : Function.Periodic F 1 := by
    intro t
    dsimp only [F]
    rw [hpolyper t]
  calc
    _ = ∫ t in (-δ)..δ, (h : ℝ)^2 / 4 * ‖poly N b t‖^2 :=
      (intervalIntegral.integral_const_mul _ (fun t : ℝ => ‖poly N b t‖^2)).symm
    _ ≤ ∫ t in (-δ)..δ, F t :=
      intervalIntegral.integral_mono_on hre
        ((continuous_const.mul ((V22o _ _).norm.pow 2)).intervalIntegrable _ _)
        (hF.intervalIntegrable _ _) hline
    _ ≤ ∫ t in (-(1/2):ℝ)..(-(1/2)+1), F t :=
      intervalIntegral.integral_mono_interval (by linarith) hre (by linarith)
        (Filter.Eventually.of_forall (fun _ => by dsimp [F]; positivity)) (hF.intervalIntegrable _ _)
    _ = ∫ t in (0 : ℝ)..1, F t := by
      simpa only [zero_add] using hper.intervalIntegral_add_eq (-(1/2)) 0
    _ = _ := V23f _ _
end Vcr
end GoldbachDiscreteWindowEstimate
section GoldbachMinorArcAbelTail
open scoped BigOperators
theorem Vh4 (θ : ℝ) (K : ℕ)
    (hθ : 0 < |θ - (round θ : ℝ)|) :
    ‖∑ j ∈ Finset.range K, Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I)‖ ≤
      1 / (2 * |θ - (round θ : ℝ)|) := by
  let k : ℤ := round θ
  let d : ℝ := θ - (k : ℝ)
  let z : ℂ := Complex.exp (((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I)
  have hpos : 0 < |d| := hθ
  have habs : |d| ≤ 1 / 2 := abs_sub_round θ
  have hphase : z = Complex.exp (Complex.I * ((2 * Real.pi * d : ℝ) : ℂ)) := by
    have hsplit :
        (((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I) =
          Complex.I * ((2 * Real.pi * d : ℝ) : ℂ) +
            (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      dsimp [d]
      push_cast
      ring
    dsimp only [z]
    rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have harg : |Real.pi * d| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos, show Real.pi / 2 = Real.pi * (1 / 2) by ring]
    exact mul_le_mul_of_nonneg_left habs Real.pi_pos.le
  have hsin : 2 * |d| ≤ |Real.sin (Real.pi * d)| := calc
    _ = 2 / Real.pi * |Real.pi * d| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      field_simp [Real.pi_pos.ne']
    _ ≤ _ := Real.mul_abs_le_abs_sin harg
  have hdenom : 4 * |d| ≤ ‖z - 1‖ := by
    rw [hphase, Complex.norm_exp_I_mul_ofReal_sub_one]
    rw [show (2 * Real.pi * d) / 2 = Real.pi * d by ring,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith only [hsin]
  have hunit : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hprod : ‖∑ j ∈ Finset.range K, z ^ j‖ * ‖z - 1‖ ≤ 2 := by
    rw [← norm_mul, geom_sum_mul]
    calc
      _ ≤ ‖z ^ K‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_pow, hunit]
  have hscaled : ‖∑ j ∈ Finset.range K, z ^ j‖ * (4 * |d|) ≤ 2 :=
    (mul_le_mul_of_nonneg_left hdenom (norm_nonneg _)).trans hprod
  have hterm (j : ℕ) :
      Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I) = z^j := by
    have he : (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I) =
      (j : ℂ) * ((((2 * Real.pi * θ : ℝ) : ℂ)) * Complex.I) := by
      push_cast
      ring
    simpa only [z, he] using Complex.exp_nat_mul
      ((((2 * Real.pi * θ : ℝ) : ℂ)) * Complex.I) j
  simp_rw [hterm]
  change ‖∑ j ∈ Finset.range K, z ^ j‖ ≤ 1 / (2 * |d|)
  apply (le_div_iff₀ (mul_pos (by norm_num) hpos)).2
  nlinarith only [hscaled]
open MeasureTheory
theorem Vxw
    (g : ℝ → ℝ) (hg : Function.Periodic g 1)
    (hi : IntervalIntegrable g volume 0 1) (m : ℕ) (hm : 0 < m) :
    (∫ t in (0 : ℝ)..1, g ((m : ℝ) * t)) = ∫ t in (0 : ℝ)..1, g t := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hperiod := hg.intervalIntegral_add_zsmul_eq (m : ℤ) 0
    (fun a b => hg.intervalIntegrable₀ (by norm_num) hi a b)
  have hscaled : (∫ t in (0 : ℝ)..(m : ℝ), g t) =
      (m : ℝ) * ∫ t in (0 : ℝ)..1, g t := by
    simpa only [zsmul_eq_mul, Int.cast_natCast, mul_one, zero_add] using hperiod
  rw [intervalIntegral.integral_comp_mul_left g hmR, mul_zero, mul_one, hscaled,
    smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hmR, one_mul]
open Set
noncomputable def V6z (δ x : ℝ) : ℝ :=
  if δ ≤ |x - (round x : ℝ)| then 1 / |x - (round x : ℝ)| ^ 2 else 0
theorem Voo (δ : ℝ) : Function.Periodic (V6z δ) 1 := by
  intro x
  simp only [V6z, round_add_one, Int.cast_add, Int.cast_one, add_sub_add_right_eq_sub]
theorem V1dk (δ : ℝ) (hδ : 0 < δ) (hd : δ ≤ 1 / 2) :
    IntervalIntegrable (V6z δ) volume 0 1 ∧
      (∫ x in (0 : ℝ)..1, V6z δ x) = 2 / δ - 4 := by
  let g := V6z δ
  let f : ℝ → ℝ := fun x => x ^ (-2 : ℤ)
  have hr {x : ℝ} (hx : x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) : round x = 0 :=
    round_eq_zero_iff.2 ⟨hx.1.le, hx.2⟩
  have hpow (x : ℝ) : f x = 1 / |x| ^ 2 := by
    simp [f, zpow_neg, sq_abs, one_div]
  have heL : (Ioo (-(1 / 2 : ℝ)) (-δ)).EqOn g f := by
    intro x hx
    have hxr : x < 1 / 2 := by linarith only [hx.2, hδ]
    have hx0 : x < 0 := by linarith only [hx.2, hδ]
    have hxd : δ ≤ |x| := by rw [abs_of_neg hx0]; linarith only [hx.2]
    rw [hpow]
    simp only [g, V6z, hr ⟨hx.1,hxr⟩, Int.cast_zero, sub_zero, ite_eq_left hxd]
  have heR : (Ioo δ (1 / 2 : ℝ)).EqOn g f := by
    intro x hx
    have hxl : -(1 / 2 : ℝ) < x := by linarith only [hx.1, hδ]
    have hx0 : 0 < x := by linarith only [hx.1, hδ]
    have hxd : δ ≤ |x| := by rw [abs_of_pos hx0]; exact hx.1.le
    rw [hpow]
    simp only [g, V6z, hr ⟨hxl,hx.2⟩, Int.cast_zero, sub_zero, ite_eq_left hxd]
  have heC : (Ioo (-δ) δ).EqOn g (fun _ : ℝ => (0 : ℝ)) := by
    intro x hx
    have hx₁ : -(1 / 2 : ℝ) < x := by linarith only [hd, hx.1]
    have hx₂ : x < (1 / 2 : ℝ) := hx.2.trans_le hd
    have hxd : |x| < δ := abs_lt.2 ⟨hx.1, hx.2⟩
    simp only [g, V6z, hr ⟨hx₁,hx₂⟩, Int.cast_zero, sub_zero,
      ite_eq_right hxd.not_ge]
  have hAway (l r : ℝ) (hab : l ≤ r) (h0 : (0 : ℝ) ∉ Icc l r) (he : (Ioo l r).EqOn g f) :
      IntervalIntegrable g volume l r ∧ (∫ x in l..r, g x) = l⁻¹ - r⁻¹ := by
    have hz : (0 : ℝ) ∉ uIcc l r := by simpa only [uIcc_of_le hab] using h0
    have hIf : IntervalIntegrable f volume l r :=
      intervalIntegral.intervalIntegrable_zpow (n := -2) (Or.inr hz)
    refine ⟨hIf.congr_uIoo (by simpa only [uIoo_of_le hab] using he.symm), ?_⟩
    rw [intervalIntegral.integral_congr_Ioo_of_le hab he]
    change (∫ x in l..r, x ^ (-2 : ℤ)) = _
    rw [integral_zpow (Or.inr ⟨by norm_num, hz⟩)]
    norm_num
    ring
  obtain ⟨hIL,hVL⟩ := hAway (-(1/2)) (-δ) (by linarith only [hd])
    (by intro hz; have hh := (mem_Icc.mp hz).2; linarith only [hh,hδ]) heL
  obtain ⟨hIR,hVR⟩ := hAway δ (1/2) hd
    (by intro hz; have hh := (mem_Icc.mp hz).1; linarith only [hh,hδ]) heR
  have hcent : -δ ≤ δ := by linarith only [hδ]
  have hIC : IntervalIntegrable g volume (-δ) δ :=
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume (-δ) δ).congr_uIoo
      (by simpa only [uIoo_of_le hcent] using heC.symm)
  have hVC : (∫ x in -δ..δ, g x) = 0 := by
    rw [intervalIntegral.integral_congr_Ioo_of_le hcent heC]
    exact intervalIntegral.integral_zero
  have hp := Voo δ
  have hiBase : IntervalIntegrable g volume (-(1/2)) (1/2) := hIL.trans (hIC.trans hIR)
  have hBaseEnd : -(1/2 : ℝ) + 1 = 1/2 := by norm_num
  have hInt : IntervalIntegrable g volume 0 1 :=
    hp.intervalIntegrable (by norm_num) (t := -(1/2 : ℝ)) (by simpa only [hBaseEnd] using hiBase) 0 1
  refine ⟨hInt, ?_⟩
  have hperiod := hp.intervalIntegral_add_eq (-(1/2 : ℝ)) 0
  change (∫ x in (0 : ℝ)..1, g x) = _
  rw [show (∫ x in (0 : ℝ)..1, g x) = ∫ x in (-(1/2 : ℝ))..(1/2), g x by
      simpa only [hBaseEnd, zero_add] using hperiod.symm,
      ← intervalIntegral.integral_add_adjacent_intervals hIL (hIC.trans hIR),
      ← intervalIntegral.integral_add_adjacent_intervals hIC hIR,
      hVL, hVC, hVR]
  norm_num [inv_neg, div_eq_mul_inv]
  ring
theorem Vu2 (F : ℝ → ℝ) (hF : Continuous F)
    (A : ℝ) (hA : 0 ≤ A) (m : ℕ) (hm : 0 < m) (δ : ℝ)
    (hδ : 0 < δ) (hd : δ ≤ 1 / 2) (s : Set ℝ) (hs : MeasurableSet s)
    (hcut : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ s →
      δ ≤ |(m : ℝ) * t - (round ((m : ℝ) * t) : ℝ)|)
    (hpoint : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ s →
      F t ≤ A * (1 / |(m : ℝ) * t - (round ((m : ℝ) * t) : ℝ)| ^ 2)) :
    (∫ t in (0 : ℝ)..1, s.indicator F t) ≤ A * (2/δ - 4) := by
  let g := V6z δ
  have hi : IntervalIntegrable F volume 0 1 := hF.intervalIntegrable 0 1
  have hiind : IntervalIntegrable (s.indicator F) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hi).indicator hs
  obtain ⟨hiUnit, hvalue⟩ := V1dk δ hδ hd
  have hp := Voo δ
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hiWide : IntervalIntegrable g volume 0 (m : ℝ) :=
    hp.intervalIntegrable₀ one_ne_zero hiUnit 0 (m : ℝ)
  have hiScaled : IntervalIntegrable (fun t => g ((m : ℝ) * t)) volume 0 1 := by
    simpa only [zero_div, div_self hmR] using hiWide.comp_mul_left (c := (m : ℝ))
  have hnonneg (t : ℝ) : 0 ≤ g t := by dsimp [g, V6z]; split <;> positivity
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, A * g ((m : ℝ)*t) := by
      apply intervalIntegral.integral_mono_on zero_le_one hiind (hiScaled.const_mul A)
      intro t ht
      by_cases hb : t ∈ s
      · rw [indicator_of_mem hb]
        dsimp [g]
        rw [V6z, ite_eq_left (hcut t ht hb)]
        exact hpoint t ht hb
      · rw [indicator_of_notMem hb]
        exact mul_nonneg hA (hnonneg _)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        Vxw g hp hiUnit m hm, hvalue]
theorem V1iv (K m : ℕ) (hm : 0 < m) (δ : ℝ)
    (hδ : 0 < δ) (hd : δ ≤ 1 / 2) (s : Set ℝ) (hs : MeasurableSet s)
    (hcut : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ s →
      δ ≤ |(m : ℝ) * t - (round ((m : ℝ) * t) : ℝ)|) :
    (∫ t in (0 : ℝ)..1, s.indicator (fun t =>
      ‖∑ j ∈ Finset.range K,
        Complex.exp (((2 * Real.pi * (j : ℝ) * ((m : ℝ) * t) : ℝ) : ℂ) * Complex.I)‖ ^ 2) t)
      ≤ 1 / (2 * δ) := by
  let F : ℝ → ℝ := fun t =>
    ‖∑ j ∈ Finset.range K,
      Complex.exp (((2 * Real.pi * (j : ℝ) * ((m : ℝ) * t) : ℝ) : ℂ) * Complex.I)‖ ^ 2
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hI : (∫ t in (0 : ℝ)..1, s.indicator F t) ≤ (1/4 : ℝ) * (2/δ - 4) := by
    apply Vu2 F hF (1/4) (by norm_num) m hm δ hδ hd s hs hcut
    intro t ht hb
    have hpos := hδ.trans_le (hcut t ht hb)
    have hgeo := Vh4 ((m : ℝ)*t) K hpos
    let d : ℝ := |(m : ℝ)*t - (round ((m : ℝ)*t) : ℝ)|
    have hn : 0 < d := hpos
    calc
      _ ≤ (1 / (2 * d)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hgeo 2
      _ = (1/4 : ℝ) * (1 / d^2) := by
        field_simp [hn.ne']
        ring
  change (∫ t in (0 : ℝ)..1, s.indicator F t) ≤ _
  have hEq : (1/4 : ℝ) * (2/δ - 4) = 1/(2*δ) - 1 := by
    field_simp [hδ.ne']
    ring
  rw [hEq] at hI
  linarith only [hI]
end GoldbachMinorArcAbelTail
section FrontierMedcoreModelHelpers
open scoped BigOperators ComplexConjugate
private noncomputable def V78 (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
theorem V159 (n : ℕ) (β : ℝ) :
    let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
    let K := ∑ k ∈ Finset.range (n+1), E ((k : ℝ) * β)
    K^2 * E (-(n : ℝ) * β) = (Complex.normSq K : ℂ) := by
  dsimp only
  let F : ℕ → ℂ := fun k => V78 ((k : ℝ) * β)
  change (∑ k ∈ Finset.range (n+1), F k)^2 * V78 (-(n : ℝ) * β) =
    (Complex.normSq (∑ k ∈ Finset.range (n+1), F k) : ℂ)
  have hPhaseAdd (x y : ℝ) : V78 (x + y) =
      V78 x * V78 y := by
    unfold V78
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hPhaseConj (x : ℝ) : conj (V78 x) = V78 (-x) := by
    unfold V78
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hConj : (∑ k ∈ Finset.range (n+1), F k) * V78 (-(n : ℝ) * β) =
      conj (∑ k ∈ Finset.range (n+1), F k) := by
    rw [Finset.sum_mul, map_sum, ← Finset.sum_range_reflect (fun k => F k * _)]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ n := by
      have := Finset.mem_range.mp hk
      omega
    have hIdx : n + 1 - 1 - k = n - k := by omega
    rw [hIdx]
    dsimp only [F]
    rw [← hPhaseAdd, hPhaseConj, Nat.cast_sub hk']
    congr 1
    ring
  rw [pow_two, mul_assoc, hConj, Complex.normSq_eq_conj_mul_self, mul_comm]
end FrontierMedcoreModelHelpers
section GoldbachGRHWindowParseval
open scoped BigOperators ComplexConjugate
open Finset
namespace V54
noncomputable section
private theorem V14k {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] (K : A → B → ℂ) (D : A → ℝ)
    (hK : ∀ r s : A, (∑ b : B, conj (K r b) * K s b) =
      if r = s then (D r : ℂ) else 0) (f : A → ℂ) :
    (∑ b : B, ‖∑ r : A, f r * K r b‖ ^ 2) =
      ∑ r : A, D r * ‖f r‖ ^ 2 := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.conj_mul']
  calc
    _ = ∑ b : B, ∑ r : A, ∑ s : A, conj (f r) * f s * (conj (K r b) * K s b) := by
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
      ring
    _ = ∑ r : A, ∑ s : A, conj (f r) * f s * (∑ b : B, conj (K r b) * K s b) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      refine Finset.sum_congr rfl fun r _ => ?_
      simp only [hK, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      ring
variable {q : ℕ} [NeZero q]
theorem V1u9 (f : ZMod q → ℂ) :
    (∑ a : ZMod q, ‖∑ r : ZMod q, f r * ZMod.stdAddChar (a * r)‖ ^ 2) =
      (q : ℝ) * ∑ r : ZMod q, ‖f r‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply V14k (fun r a => ZMod.stdAddChar (a * r)) (fun _ => (q : ℝ))
  intro r s
  have hc (z : ZMod q) : conj (ZMod.stdAddChar z) = ZMod.stdAddChar (-z) := by
    rw [AddChar.map_neg_eq_inv]
    exact (Complex.inv_eq_conj (by simp [ZMod.stdAddChar_apply])).symm
  simp only [hc, ← AddChar.map_add_eq_mul, ← mul_neg, ← mul_add]
  by_cases h : r = s
  · simp [h, ZMod.card]
  · rw [ite_eq_right h]
    have hne : -r + s ≠ 0 := by
      simpa only [sub_eq_add_neg, add_comm] using (sub_ne_zero.mpr (fun he : s = r => h he.symm) : s - r ≠ 0)
    calc
      _ = ∑ a : ZMod q, ZMod.stdAddChar ((-r + s) * a) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [mul_comm]
      _ = 0 := AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q hne)
omit [NeZero q] in
private theorem V1z4 (χ : DirichletCharacter ℂ q) {r : ZMod q}
    (hr : IsUnit r) : conj (χ r) = χ r⁻¹ := by
  have hχr : χ r ≠ 0 := (hr.map χ).ne_zero
  have hi : χ r⁻¹ = (χ r)⁻¹ := by
    calc
      _ = χ r⁻¹ * (χ r * (χ r)⁻¹) := by rw [mul_inv_cancel₀ hχr, mul_one]
      _ = _ := by rw [← mul_assoc, ← map_mul, ZMod.inv_mul_of_unit r hr, map_one, one_mul]
  exact (MulChar.star_apply' χ r).trans ((MulChar.inv_apply_eq_inv' χ r).trans hi.symm)
theorem Viq (f : ZMod q → ℂ) :
    (∑ χ : DirichletCharacter ℂ q, ‖∑ r : ZMod q, f r * χ r‖ ^ 2) =
      (q.totient : ℝ) * ∑ r ∈ (univ : Finset (ZMod q)).filter IsUnit, ‖f r‖ ^ 2 := by
  rw [Finset.sum_filter, Finset.mul_sum]
  have hParseval := V14k (fun r (χ : DirichletCharacter ℂ q) => χ r)
    (fun r : ZMod q => if IsUnit r then (q.totient : ℝ) else 0)
    (f := f) (by
      intro r s
      by_cases hr : IsUnit r
      · simp only [V1z4 _ hr, ite_eq_left hr, Complex.ofReal_natCast]
        exact DirichletCharacter.sum_char_inv_mul_char_eq ℂ hr s
      · simp [hr, MulChar.map_nonunit _ hr])
  rw [hParseval]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hr : IsUnit r <;> simp [hr]
noncomputable def V8a (q : ℕ) [NeZero q] (a : ZMod q) : ℂ :=
  (∑ u : (ZMod q)ˣ, ZMod.stdAddChar (a * (u : ZMod q))) / (q.totient : ℂ)
theorem V1gr (a k : ℕ) :
    ZMod.stdAddChar ((a : ZMod q) * (k : ZMod q)) =
      Complex.exp (((2 * Real.pi * ((a : ℝ) * (k : ℝ) / (q : ℝ)) : ℝ) : ℂ) *
        Complex.I) := by
  have h := ZMod.stdAddChar_coe (N := q) (a * k : ℕ)
  push_cast at h
  rw [h]
  congr 1
  push_cast
  ring
theorem V1el (a : ℕ) :
    V8a q (a : ZMod q) =
      (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
        Complex.exp (((2 * Real.pi * ((a : ℝ) * (r : ℝ) / (q : ℝ)) : ℝ) : ℂ) *
          Complex.I)) / (q.totient : ℂ) := by
  unfold V8a
  congr 1
  apply Finset.sum_bij (fun (u : (ZMod q)ˣ) _ => (u : ZMod q).val)
  · intro u _
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (ZMod.val_lt (u : ZMod q)), ZMod.val_coe_unit_coprime u⟩
  · intro u _ v _ huv
    apply Units.ext
    simpa only [ZMod.natCast_zmod_val] using congrArg (fun x : ℕ => (x : ZMod q)) huv
  · intro r hr
    obtain ⟨hrange, hcop⟩ := Finset.mem_filter.mp hr
    let hrunit : IsUnit (r : ZMod q) := (ZMod.isUnit_iff_coprime r q).mpr hcop
    exact ⟨hrunit.unit, Finset.mem_univ _, by
      rw [IsUnit.unit_spec, ZMod.val_natCast_of_lt (Finset.mem_range.mp hrange)]⟩
  · intro u _
    rw [← V1gr (q := q) a ((u : ZMod q).val), ZMod.natCast_zmod_val]
theorem V1tz (a : ZMod q) (ha : IsUnit a) :
    V8a q a = V8a q 1 := by
  unfold V8a
  apply congrArg (fun z : ℂ => z / (q.totient : ℂ))
  let e : (ZMod q)ˣ ≃ (ZMod q)ˣ := Equiv.mulLeft ha.unit
  refine Fintype.sum_equiv e (fun u => ZMod.stdAddChar (a * (u : ZMod q)))
    (fun u => ZMod.stdAddChar (1 * (u : ZMod q))) ?_
  intro u
  change ZMod.stdAddChar (a * (u : ZMod q)) =
    ZMod.stdAddChar (1 * (((ha.unit * u) : (ZMod q)ˣ) : ZMod q))
  rw [one_mul, Units.val_mul, IsUnit.unit_spec]
noncomputable def V76 (k : ℕ) : ℂ :=
  ((if Nat.Prime k then Real.log (k : ℝ) else 0 : ℝ) : ℂ)
theorem Vx9 (I : Finset ℕ) :
    (∑ k ∈ I.filter (fun k : ℕ => ¬ IsUnit (k : ZMod q)), ‖V76 k‖) ≤
      Real.log (q : ℝ) := by
  let J := I.filter (fun k : ℕ => ¬ IsUnit (k : ZMod q))
  change (∑ k ∈ J, ‖V76 k‖) ≤ _
  have hsub : J.filter Nat.Prime ⊆ q.primeFactors := by
    intro k hk
    obtain ⟨hkJ, hp⟩ := Finset.mem_filter.mp hk
    have hnu := (Finset.mem_filter.mp hkJ).2
    have hd : k ∣ q := by
      by_contra hnd
      exact hnu ((ZMod.isUnit_iff_coprime k q).mpr ((hp.coprime_iff_not_dvd).mpr hnd))
    exact Nat.mem_primeFactors.mpr ⟨hp, hd, NeZero.ne q⟩
  calc
    _ = ∑ k ∈ J.filter Nat.Prime, Real.log (k : ℝ) := by
      conv_rhs => rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hp : Nat.Prime k
      · have hk : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k from hp.pos)
        simp only [V76, ite_eq_left hp, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hk)]
      · simp [V76, hp]
    _ ≤ ∑ p ∈ q.primeFactors, Real.log (p : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => ?_
      exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
    _ = Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) := by
      symm
      exact Real.log_prod fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    _ ≤ _ := by
      apply Real.log_le_log (Finset.prod_pos fun p hp => by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
      rw [← Nat.cast_prod]
      exact_mod_cast Nat.le_of_dvd (NeZero.pos q) (Nat.prod_primeFactors_dvd q)
end
end V54
end GoldbachGRHWindowParseval
section GoldbachGRHBandBase
section
open Finset Filter MeasureTheory
namespace Vr
noncomputable section
def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
end
end Vr
namespace Vr.V200
private def Vo1 (m : ℕ) := (Finset.range m).filter (fun a => Nat.Coprime a m)
private theorem V1u4 (m : ℕ) : (Vo1 m).card = m.totient := by
  unfold Vo1
  rw [Nat.totient_eq_card_coprime]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range]
  exact and_congr_right (fun _ => Nat.coprime_comm)
private noncomputable def phase (m h a : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * ((h : ℝ) * a / m) : ℝ) : ℂ) * Complex.I)
private theorem V20e (m h a : ℕ) [NeZero m] :
    phase m h a = ZMod.stdAddChar ((h : ZMod m) * (a : ZMod m)) := by
  have ch := ZMod.stdAddChar_coe (N := m) ((h * a : ℕ) : ℤ)
  push_cast at ch
  rw [ch]
  unfold phase
  push_cast
  congr 1
  ring
private theorem V21j (m h a : ℕ) [NeZero m] :
    phase m h (a % m) = phase m h a := by
  simp only [V20e, ZMod.natCast_mod]
private theorem V23b (q r h a b : ℕ) (hq : 0 < q) (hr : 0 < r) :
    phase (q*r) h ((r*a + q*b) % (q*r)) = phase q h a * phase r h b := by
  have : NeZero (q*r) := ⟨Nat.ne_of_gt (Nat.mul_pos hq hr)⟩
  rw [V21j]
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  have qnz : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have rnz : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp
theorem crt :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let ram := fun (q h : ℕ) => Finset.sum ((Finset.range q).filter (fun a => Nat.Coprime a q)) (fun a => E ((h:ℝ)*(a:ℝ)/(q:ℝ))); ∀ q r h, 0<q → 0<r → Nat.Coprime q r → ram (q*r) h=ram q h*ram r h := by
  dsimp only
  intro q r h hq hr cop
  let combine (x : ℕ × ℕ) := (r*x.1 + q*x.2) % (q*r)
  let pairs := Vo1 q ×ˢ Vo1 r
  have member {m a : ℕ} : a ∈ Vo1 m ↔ a < m ∧ Nat.Coprime a m := by
    simp only [Vo1, Finset.mem_filter, Finset.mem_range]
  have maps : pairs.image combine ⊆ Vo1 (q*r) := by
    intro z hz
    obtain ⟨⟨a,b⟩, hab, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    apply member.mpr
    refine ⟨Nat.mod_lt _ (Nat.mul_pos hq hr), ?_⟩
    change Nat.gcd ((r*a + q*b) % (q*r)) (q*r) = 1
    rw [← Nat.gcd_rec]
    change Nat.Coprime (q*r) (r*a + q*b)
    apply Nat.coprime_mul_iff_left.mpr
    constructor
    · rw [Nat.coprime_add_mul_left_right]
      exact cop.mul_right (member.mp ha).2.symm
    · rw [add_comm, Nat.coprime_add_mul_left_right]
      exact cop.symm.mul_right (member.mp hb).2.symm
  have injective : Set.InjOn combine (↑pairs) := by
    rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd he
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    obtain ⟨hc,hd⟩ := Finset.mem_product.mp hcd
    have congruence : r*a + q*b ≡ r*c + q*d [MOD q*r] := he
    apply Prod.ext
    · have hmod := congruence.of_dvd (dvd_mul_right q r)
      have reduced : r*a ≡ r*c [MOD q] := by
        simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, add_zero, Nat.mod_mod] using hmod
      exact (Nat.ModEq.cancel_left_of_coprime cop reduced).eq_of_lt_of_lt
        (member.mp ha).1 (member.mp hc).1
    · have hmod := congruence.of_dvd (dvd_mul_left r q)
      have reduced : q*b ≡ q*d [MOD r] := by
        simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod] using hmod
      exact (Nat.ModEq.cancel_left_of_coprime cop.symm reduced).eq_of_lt_of_lt
        (member.mp hb).1 (member.mp hd).1
  have covers : pairs.image combine = Vo1 (q*r) := by
    apply Finset.eq_of_subset_of_card_le maps
    rw [Finset.card_image_of_injOn injective, V1u4, Nat.totient_mul cop]
    simp only [pairs, Finset.card_product, V1u4]
    exact le_rfl
  change (∑ z ∈ Vo1 (q*r), phase (q*r) h z) =
    (∑ a ∈ Vo1 q, phase q h a) * ∑ b ∈ Vo1 r, phase r h b
  rw [← covers, Finset.sum_image injective, Finset.sum_mul_sum]
  rw [← Finset.sum_product']
  exact Finset.sum_congr rfl (fun x _ => V23b q r h x.1 x.2 hq hr)
end Vr.V200
namespace Vr.V1xj
open Finset
theorem V23a :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let ram := fun (q h : ℕ) => Finset.sum ((Finset.range q).filter (fun a => Nat.Coprime a q)) (fun a => E ((h:ℝ)*(a:ℝ)/(q:ℝ))); ∀ p j h, Nat.Prime p → ram (p^(j+1)) h = (if p^(j+1) ∣ h then ((p^(j+1):ℕ):ℂ) else 0) - (if p^j ∣ h then ((p^j:ℕ):ℂ) else 0) := by
  intro E ram p j h hp
  have full (q : ℕ) (hq : 0 < q) :
      ∑ a ∈ range q, E ((h:ℝ) * a / q) = if q ∣ h then (q:ℂ) else 0 := by
    let : NeZero q := ⟨hq.ne'⟩
    calc
      _ = ∑ x : ZMod q, ZMod.stdAddChar ((h : ZMod q) * x) := by
        apply Finset.sum_bij (fun (a : ℕ) _ => (a : ZMod q))
        · intro a ha
          exact mem_univ _
        · intro a ha b hb hab
          simpa only [ZMod.val_natCast_of_lt (mem_range.mp ha),
            ZMod.val_natCast_of_lt (mem_range.mp hb)] using congrArg ZMod.val hab
        · intro x _
          exact ⟨x.val, mem_range.mpr x.val_lt, ZMod.natCast_zmod_val x⟩
        · intro a _
          have cast_eq : (h : ZMod q) * a = ((h * a : ℕ) : ℤ) := by push_cast; rfl
          rw [cast_eq, ZMod.stdAddChar_coe]
          dsimp [E]
          congr 1
          push_cast
          ring
      _ = _ := by
        by_cases hd : q ∣ h
        · have hz : (h : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff h q).mpr hd
          simp [hd, hz, ZMod.card]
        · have hz : (h : ZMod q) ≠ 0 := fun hz => hd ((ZMod.natCast_eq_zero_iff h q).mp hz)
          rw [ite_eq_right hd]
          exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q hz)
  let m := p ^ j
  have hm : 0 < m := pow_pos hp.pos _
  let mult := (range m).image (fun b => p * b)
  have hsub : mult ⊆ range (p^(j+1)) := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
    rw [mem_range, pow_succ']
    exact Nat.mul_lt_mul_of_pos_left (mem_range.mp hb) hp.pos
  have hfilter : (range (p^(j+1))).filter (fun a => Nat.Coprime a (p^(j+1))) =
      range (p^(j+1)) \ mult := by
    rw [sdiff_eq_filter]
    apply filter_congr
    intro a ha
    rw [Nat.coprime_pow_right_iff (Nat.succ_pos j), Nat.coprime_comm, hp.coprime_iff_not_dvd]
    apply not_congr
    constructor
    · rintro ⟨b, rfl⟩
      apply mem_image.mpr
      refine ⟨b, mem_range.mpr ?_, rfl⟩
      rw [mem_range, pow_succ'] at ha
      exact (Nat.mul_lt_mul_left hp.pos).mp ha
    · intro ha'
      obtain ⟨b, _, rfl⟩ := mem_image.mp ha'
      exact dvd_mul_right _ _
  have removed : ∑ a ∈ mult, E ((h:ℝ)*a/(p^(j+1):ℕ)) =
      ∑ b ∈ range m, E ((h:ℝ)*b/m) := by
    rw [show mult = (range m).image (fun b => p * b) from rfl,
      sum_image (mul_right_injective₀ hp.ne_zero).injOn]
    apply sum_congr rfl
    intro b _
    congr 1
    rw [pow_succ']
    push_cast
    dsimp [m]
    push_cast
    field_simp [show (p : ℝ) ≠ 0 by exact_mod_cast hp.ne_zero]
  change ∑ a ∈ (range (p^(j+1))).filter _, E ((h:ℝ)*a/(p^(j+1):ℕ)) = _
  rw [hfilter, ← full _ (pow_pos hp.pos (j+1)), ← full _ hm, ← removed]
  exact eq_sub_of_add_eq (sum_sdiff hsub)
end Vr.V1xj
namespace Vr
open Finset
open scoped ComplexConjugate
noncomputable section
def ram (q h : ℕ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a => a.Coprime q), phase ((h : ℝ) * a / q)
theorem ram_mul {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hc : q.Coprime r) (h : ℕ) :
    ram (q * r) h = ram q h * ram r h := V200.crt q r h hq hr hc
theorem V1n3 (p j h : ℕ) (hp : p.Prime) :
    ram (p ^ (j + 1)) h = (if p ^ (j + 1) ∣ h then ((p ^ (j + 1) : ℕ) : ℂ) else 0) -
      (if p ^ j ∣ h then ((p ^ j : ℕ) : ℂ) else 0) := V1xj.V23a p j h hp
theorem ram_one (h : ℕ) : ram 1 h = 1 := by simp [ram, phase]
theorem V22l {p : ℕ} (hp : p.Prime) (h : ℕ) :
    ram p h = (if p ∣ h then (p : ℂ) else 0) - 1 := by
  simpa using V1n3 p 0 h hp
private theorem V20x {p : ℕ} (hp : p.Prime) (j h : ℕ) (hc : h.Coprime p) :
    ram (p ^ (j + 1)) h = if j = 0 then -1 else 0 := by
  have hd := hp.coprime_iff_not_dvd.mp hc.symm
  have hpow (k : ℕ) : ¬ p ^ (k + 1) ∣ h :=
    fun hh => hd ((dvd_pow_self p (Nat.succ_ne_zero k)).trans hh)
  rw [V1n3 p j h hp, ite_eq_right (hpow j)]
  cases j with
  | zero => simp
  | succ k => simp [hpow k]
def Vj7 (p n : ℕ) : ℝ :=
  if p ∣ n then 1 / ((p : ℝ) - 1) else -(1 / ((p : ℝ) - 1) ^ 2)
def V3f (q n : ℕ) : ℂ := (ram q 1 / (q.totient : ℂ)) ^ 2 * conj (ram q n)
theorem V13x (n : ℕ) : V3f 1 n = 1 := by simp [V3f, ram_one]
theorem V1jn {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hc : q.Coprime r) (n : ℕ) :
    V3f (q * r) n = V3f q n * V3f r n := by
  unfold V3f
  rw [ram_mul hq hr hc, ram_mul hq hr hc, Nat.totient_mul hc, Nat.cast_mul, map_mul]
  ring
theorem V1p1 {p : ℕ} (hp : p.Prime) (n : ℕ) :
    V3f p n = (Vj7 p n : ℂ) := by
  have hone : ¬ p ∣ 1 := fun h => hp.ne_one (Nat.dvd_one.mp h)
  have hne : (p : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  rw [V3f, V22l hp, V22l hp, ite_eq_right hone, Nat.totient_prime hp,
    Nat.cast_sub hp.one_le, Nat.cast_one]
  by_cases hd : p ∣ n <;> simp [Vj7, hd] <;> field_simp
theorem Vyw {p : ℕ} (hp : p.Prime) (k n : ℕ) :
    V3f (p ^ (k + 2)) n = 0 := by
  have h := V20x hp (k + 1) 1 (by simp)
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false] at h
  simp [V3f, h]
end
end Vr
namespace Vr
open Finset
noncomputable section
theorem V1jm {q : ℕ} (n : ℕ) (hq : 0 < q)
    (hs : ¬ Squarefree q) : V3f q n = 0 := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => exact (hs squarefree_one).elim
  | prime_pow p k hp hk =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero => exact (hs (by simpa using hp.squarefree)).elim
      | succ j => exact Vyw hp j n
  | coprime a b ha hb hab ia ib =>
    rw [V1jn (by omega) (by omega) hab]
    by_cases h : Squarefree a
    · rw [ib (by omega) (fun h' => hs ((Nat.squarefree_mul hab).mpr ⟨h,h'⟩)), mul_zero]
    · rw [ia (by omega) h, zero_mul]
theorem V1m5 (n : ℕ) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    V3f (∏ p ∈ s, p) n = ((∏ p ∈ s, Vj7 p n : ℝ) : ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp [V13x]
  | @insert p s hp ih =>
    have hprime := hs p (mem_insert_self _ _)
    have hs' : ∀ r ∈ s, r.Prime := fun r hr => hs r (mem_insert_of_mem hr)
    have hcop : p.Coprime (∏ r ∈ s, r) := Nat.coprime_prod_right_iff.mpr fun r hr =>
      (Nat.coprime_primes hprime (hs' r hr)).mpr fun he => hp (he ▸ hr)
    rw [prod_insert hp, prod_insert hp, V1jn hprime.pos (prod_pos fun r hr => (hs' r hr).pos) hcop,
      V1p1 hprime, ih hs', Complex.ofReal_mul]
end
end Vr
end
section
namespace Vm
open Finset ArithmeticFunction Vr
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
noncomputable section
def smooth (n k : ℕ) : Prop := ∀ p ∈ k.primeFactors, p∣n
instance smoothDec (n k : ℕ) : Decidable (smooth n k) := by unfold smooth; infer_instance
def g (n : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun k => if k=0 then 0 else if smooth n k then 1 else 0,by simp⟩
@[simp] theorem g_one (n : ℕ) : g n 1=1 := by simp [g,smooth]
theorem g_mul (n a b : ℕ) : g n (a*b)=g n a*g n b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have hs : smooth n (a*b) ↔ smooth n a ∧ smooth n b := by
    simp only [smooth,Nat.primeFactors_mul ha hb,mem_union]
    constructor
    · intro h; exact ⟨fun p hp => h p (Or.inl hp),fun p hp => h p (Or.inr hp)⟩
    · rintro ⟨x,y⟩ p (h|h)
      · exact x p h
      · exact y p h
  simp only [g,coe_mk, mul_ne_zero ha hb,ha,hb,ite_false]
  by_cases h1 : smooth n a <;> by_cases h2 : smooth n b <;> simp [hs,h1,h2]
theorem g_mult (n : ℕ) : IsMultiplicative (g n) := ⟨g_one n, fun {_ _} _ => g_mul n _ _⟩
theorem g_prime (n p : ℕ) (hp : p.Prime) : g n p=if p∣n then 1 else 0 := by
  simp [g,smooth,hp.ne_zero,hp.primeFactors]
def F (n : ℕ) : ArithmeticFunction ℝ := ⟨fun q => (q:ℝ)*(V3f q n).re,by simp⟩
theorem V23j {q : ℕ} (hq : 0<q) (n : ℕ) : V3f q n = (((V3f q n).re:ℝ):ℂ) := by
  by_cases hsf : Squarefree q
  · have he := V1m5 n q.primeFactors (fun _ hp => Nat.prime_of_mem_primeFactors hp)
    rw [Nat.prod_primeFactors_of_squarefree hsf] at he
    rw [he]; rfl
  · rw [V1jm n hq hsf]; simp
theorem F_mult (n : ℕ) : IsMultiplicative (F n) := by
  refine ⟨by simp [F,V13x],fun {a b} hab => ?_⟩
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have hzero : (V3f a n).im=0 := by rw [V23j ha.bot_lt n]; rfl
  simp [F,V1jn ha.bot_lt hb.bot_lt hab,Complex.mul_re,hzero]
  ring
theorem F_prime (n p : ℕ) (hp : p.Prime) : F n p=(p:ℝ)*Vj7 p n := by simp [F,V1p1 hp]
theorem V22j (n p j : ℕ) (hp : p.Prime) : F n (p^(j+2))=0 := by simp [F,Vyw hp j n]
def invG (n : ℕ) : ArithmeticFunction ℝ := pmul (μ : ArithmeticFunction ℝ) (g n)
def h (n : ℕ) : ArithmeticFunction ℝ := invG n * F n
theorem h_mult (n : ℕ) : IsMultiplicative (h n) :=
  (isMultiplicative_moebius.intCast.pmul (g_mult n)).mul (F_mult n)
theorem inverse_id (n : ℕ) : g n * invG n = 1 := by
  ext k
  have heq : (g n*invG n) k = g n k * (((ζ : ArithmeticFunction ℝ)*μ) k) := by
    simp only [ArithmeticFunction.mul_apply,Finset.mul_sum,invG,pmul_apply]
    apply Finset.sum_congr rfl
    intro ab hab
    have h0 : 0<ab.1 := Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hab)
    have hG : g n k=g n ab.1*g n ab.2 := (Nat.mem_divisorsAntidiagonal.mp hab).1 ▸ g_mul n ab.1 ab.2
    rw [hG]
    simp [zeta_apply,h0.ne']; ring
  rw [heq,coe_zeta_mul_coe_moebius]
  by_cases hk : k=1 <;> simp [ArithmeticFunction.one_apply,hk]
theorem convolution (n : ℕ) : F n = g n*h n := by rw [h,←mul_assoc,inverse_id,one_mul]
theorem V12x (n p j : ℕ) (hp : p.Prime) :
    h n (p^(j+1))=F n (p^(j+1))-g n p*F n (p^j) := by
  let q := p^(j+1)
  have hq : q≠0 := pow_ne_zero _ hp.ne_zero
  let v := fun d : ℕ => invG n d * F n (q/d)
  have hv : h n q = ∑ d ∈ q.divisors, v d := by
    rw [h,ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal (fun a b : ℕ => invG n a * F n b)]
  have h1 : ({1,p}:Finset ℕ) ⊆ q.divisors := by
    intro a ha
    simp only [mem_insert,mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact Nat.mem_divisors.mpr ⟨one_dvd _,hq⟩
    · exact Nat.mem_divisors.mpr ⟨dvd_pow_self _ (by omega),hq⟩
  have hsum : ∑ d ∈ q.divisors,v d = ∑ d ∈ ({1,p}:Finset ℕ),v d := by
    symm; apply sum_subset h1
    intro d hd hn
    obtain ⟨i,hi,he⟩ := (Nat.dvd_prime_pow hp).mp (Nat.dvd_of_mem_divisors hd)
    by_cases hi0 : i=0
    · exfalso; apply hn; simp [he,hi0]
    by_cases hi1 : i=1
    · exfalso; apply hn; simp [he,hi1]
    have hm : μ d=0 := by rw [he, moebius_apply_prime_pow hp hi0,if_neg hi1]
    simp [v,invG,pmul_apply,intCoe_apply,hm]
  have hdiv : q/p=p^j := by dsimp [q]; rw [pow_succ,Nat.mul_div_cancel _ hp.pos]
  change h n q = _
  rw [hv,hsum,Finset.sum_insert (by simpa using hp.ne_one.symm : (1:ℕ)∉({p}:Finset ℕ)),Finset.sum_singleton]
  simp [v,invG,pmul_apply,intCoe_apply,moebius_apply_prime hp,hdiv,q]
  ring
theorem h_prime (n p : ℕ) (hp : p.Prime) : h n p =
    if p∣n then 1/((p:ℝ)-1) else -(p:ℝ)/((p:ℝ)-1)^2 := by
  have he := V12x n p 0 hp
  have he1 : F n 1=1 := (F_mult n).map_one
  simp only [Nat.zero_add,pow_one,pow_zero,he1,F_prime n p hp,g_prime n p hp,mul_one] at he
  rw [he]; dsimp [Vj7]
  have hr1 : (p:ℝ)-1≠0 := by
    have ht : (2:ℝ)≤p := by exact_mod_cast hp.two_le
    linarith
  split_ifs <;> field_simp <;> ring
theorem V22c (n p : ℕ) (hp : p.Prime) : h n (p^2) =
    if p∣n then -(p:ℝ)/((p:ℝ)-1) else 0 := by
  have he := V12x n p 1 hp
  rw [V22j n p 0 hp,pow_one,g_prime n p hp,F_prime n p hp] at he
  rw [he]; dsimp [Vj7]; split_ifs <;> ring
theorem h_cube (n p j : ℕ) (hp : p.Prime) : h n (p^(j+3))=0 := by
  have he := V12x n p (j+2) hp
  rw [V22j n p j hp,show j+2+1=(j+1)+2 by omega,V22j n p (j+1) hp] at he
  simpa [show j+2+1=j+3 by omega] using he
end
end Vm
end
section
namespace Vm
open Finset Vr MeasureTheory Filter Topology
noncomputable section
theorem V1ss (A B : ℕ) (f w : ℕ → ℝ) (k : ℝ)
    (hab : A ≤ B) (hk : 0 ≤ k) (hw : ∀ i ≥ A,0 ≤ w i) (hm : ∀ i ≥ A,w (i+1) ≤ w i)
    (hp : ∀ i ≥ A,i ≤ B → -k ≤ ∑ j ∈ Ioc A i,f j) :
    -(k*w A) ≤ ∑ j ∈ Ioc A B,f j*w j := by
  have strong (i : ℕ) (hi : A ≤ i) (hiB : i ≤ B) :
      w i*((∑ j ∈ Ioc A i,f j)+k) ≤ (∑ j ∈ Ioc A i,f j*w j)+k*w A := by
    induction i,hi using Nat.le_induction with
    | base => simp [mul_comm]
    | succ i hi ih =>
      have h := ih (by omega)
      have hmono := hm i hi
      have hx := hp i hi (by omega)
      rw [sum_Ioc_succ_top hi,sum_Ioc_succ_top hi]
      nlinarith only [h,mul_nonneg (sub_nonneg.mpr hmono) (show 0 ≤ (∑ j ∈ Ioc A i,f j)+k by linarith)]
  have h := strong B hab le_rfl
  have v := hp B hab le_rfl
  nlinarith only [h,mul_nonneg (hw B hab) (show 0 ≤ (∑ j ∈ Ioc A B, f j)+k by linarith)]
end
end Vm
end
section
namespace Vm
open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta
noncomputable section
def w (n : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => |h n d|/(d:ℝ)^(3/4:ℝ),by simp⟩
def z (n : ℕ) : ArithmeticFunction ℝ := ⟨fun d => h n d/(d:ℝ),by simp⟩
theorem w_mult (n : ℕ) : IsMultiplicative (w n) := by
  refine ⟨by simp [w,(h_mult n).map_one],fun {a b} hab => ?_⟩
  simp only [w,coe_mk,(h_mult n).map_mul_of_coprime hab,Nat.cast_mul,abs_mul,Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
  ring
theorem z_mult (n : ℕ) : IsMultiplicative (z n) := by
  refine ⟨by simp [z,(h_mult n).map_one],fun {a b} hab => ?_⟩
  simp [z,(h_mult n).map_mul_of_coprime hab]; ring
theorem w_nonneg (n d : ℕ) : 0≤w n d := by dsimp [w]; positivity
theorem V1y7 (f : ℕ → ℝ) (hf : ∀ j, f (j+3)=0) (k : ℕ) :
    (∑ i ∈ range (k+1), f i)=f 0 + (if k≥1 then f 1 else 0) + (if k≥2 then f 2 else 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ,ih]
    rcases k with _ | _ | j
    · simp
    · simp
    · simp [hf,show 2≤j+1+1 by omega,show 2≤j+1+1+1 by omega]
theorem wLocal (p n k : ℕ) (hp : p.Prime) :
    (∑ d ∈ (p^k).divisors, w n d) ≤ 1+6/((p:ℝ)^(3/2:ℝ)) := by
  have hp2 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have hp1 : 0<(p:ℝ)-1 := by linarith
  have hpr : 0<(p:ℝ) := by linarith
  have hW1 : w n p ≤ 4/((p:ℝ)^(3/2:ℝ)) := by
    have h₁ : |h n p| ≤ 4/(p:ℝ) := by
      rw [h_prime n p hp]
      split_ifs
      · rw [abs_of_nonneg (by positivity)]; field_simp; linarith
      · rw [abs_div,abs_neg,abs_of_nonneg hpr.le,abs_of_nonneg (sq_nonneg _)]
        field_simp
        nlinarith [mul_nonneg (show 0≤(p:ℝ)-2 by linarith) (show 0≤3*(p:ℝ)-2 by linarith)]
    dsimp [w]
    calc
      _ ≤ (4/(p:ℝ))/((p:ℝ)^(3/4:ℝ)) := div_le_div_of_nonneg_right h₁ (by positivity)
      _ = 4/(p:ℝ)^(1+(3/4):ℝ) := by rw [Real.rpow_add hpr,Real.rpow_one,div_div]
      _ ≤ _ := by apply div_le_div_of_nonneg_left (by norm_num) (by positivity); exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hW2 : w n (p^2) ≤ 2/(p:ℝ)^(3/2:ℝ) := by
    have he : |h n (p^2)| ≤ 2 := by
      rw [V22c n p hp]; split_ifs
      · rw [abs_div,abs_neg,abs_of_nonneg hpr.le,abs_of_nonneg hp1.le]; apply (div_le_iff₀ hp1).mpr; linarith
      · norm_num
    change |h n (p^2)| / ((p^2:ℕ):ℝ)^(3/4:ℝ) ≤ _
    rw [Nat.cast_pow,←Real.rpow_natCast_mul hpr.le,show (↑(2:ℕ):ℝ)*(3/4)=3/2 by norm_num]
    exact div_le_div_of_nonneg_right he (by positivity)
  rw [Nat.sum_divisors_prime_pow hp,V1y7 (fun j => w n (p^j)) (fun j => by simp [w,h_cube n p j hp])]
  simp only [pow_zero,pow_one,(w_mult n).map_one]
  simp only [div_eq_mul_inv] at hW1 hW2 ⊢
  split_ifs <;> linarith [w_nonneg n p,w_nonneg n (p^2)]
theorem zLocal (p n k : ℕ) (hp : p.Prime) : 0≤∑ d ∈ (p^k).divisors,z n d := by
  rw [Nat.sum_divisors_prime_pow hp,V1y7 (fun j => z n (p^j)) (fun j => by simp [z,h_cube n p j hp])]
  simp only [pow_zero,pow_one,(z_mult n).map_one]
  have h2 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have hp1 : 0<(p:ℝ)-1 := by linarith
  have hpr : 0<(p:ℝ) := by linarith
  have hsq : 1≤((p:ℝ)-1)^2 := by nlinarith [mul_nonneg (show 0≤(p:ℝ)-2 by linarith) (show 0≤(p:ℝ) by linarith)]
  simp only [z,coe_mk,h_prime n p hp,V22c n p hp,Nat.cast_pow]
  by_cases hpn : p∣n
  · simp only [hpn,ite_true]
    split_ifs with hk hk2
    · field_simp; nlinarith [mul_pos hpr hp1]
    · positivity
    · omega
    · norm_num
  · simp only [hpn,ite_false,zero_div,ite_self,add_zero]
    split_ifs
    · field_simp; nlinarith [mul_le_mul_of_nonneg_right hsq hpr.le]
    · norm_num
def V2i : ℝ := Real.exp (6*∑' j : ℕ, ((j:ℝ)^(3/2:ℝ))⁻¹)
theorem V205 (n M : ℕ) (hM : 0<M) :
    (∑ d ∈ M.divisors, w n d) ≤ V2i := by
  let A : ArithmeticFunction ℝ := w n * (ζ : ArithmeticFunction ℝ)
  have hA : IsMultiplicative A := (w_mult n).mul isMultiplicative_zeta.natCast
  have he (m : ℕ) : A m = ∑ d ∈ m.divisors,w n d := coe_mul_zeta_apply
  have hprod := hA.multiplicative_factorization A hM.ne'
  rw [he] at hprod
  rw [hprod,Finsupp.prod]
  calc
    _ ≤ ∏ p ∈ M.factorization.support, Real.exp (6/((p:ℝ)^(3/2:ℝ))) := by
      refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
      · rw [he]; exact sum_nonneg fun d _ => w_nonneg n d
      · rw [he]
        have hh : p ∈ M.primeFactors := M.support_factorization ▸ hp
        exact (wLocal p n _ (Nat.prime_of_mem_primeFactors hh)).trans (by linarith [Real.add_one_le_exp (6/((p:ℝ)^(3/2:ℝ)))])
    _ ≤ V2i := by
      rw [←Real.exp_sum,V2i]
      apply Real.exp_le_exp.mpr
      simp_rw [div_eq_mul_inv,←mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤6)
      exact (Real.summable_nat_rpow_inv.mpr (by norm_num : (1:ℝ)<3/2)).sum_le_tsum _ (by intro _ _; positivity)
theorem V20v (n M : ℕ) (hM : 0<M) :
    0 ≤ ∑ d ∈ M.divisors, z n d := by
  let A : ArithmeticFunction ℝ := z n * (ζ : ArithmeticFunction ℝ)
  have hA : IsMultiplicative A := (z_mult n).mul isMultiplicative_zeta.natCast
  have he (m : ℕ) : A m = ∑ d ∈ m.divisors,z n d := coe_mul_zeta_apply
  have hh := hA.multiplicative_factorization A hM.ne'
  rw [he] at hh
  rw [hh,Finsupp.prod]
  apply Finset.prod_nonneg
  intro p hp
  rw [he]
  exact zLocal p n _ (Nat.prime_of_mem_primeFactors (M.support_factorization ▸ hp))
theorem V20y (J : ℕ) : Icc 1 J ⊆ J.factorial.divisors := by
  intro d hd
  obtain ⟨hd1, hdJ⟩ := mem_Icc.mp hd
  exact Nat.mem_divisors.mpr ⟨Nat.dvd_factorial hd1 hdJ,J.factorial_pos.ne'⟩
theorem V1yh (n J : ℕ) : (∑ d ∈ Icc 1 J, w n d)≤V2i :=
  (sum_le_sum_of_subset_of_nonneg (V20y J) (fun d _ _ => w_nonneg n d)).trans
    (V205 n _ J.factorial_pos)
theorem V239 (n J d : ℕ) (hJ : 0<J) (hJd : J≤d) :
    |z n d| ≤ w n d / ((J:ℝ)^(1/4:ℝ)) := by
  have hd : 0<(d:ℝ) := by exact_mod_cast hJ.trans_le hJd
  have hJr : 0<(J:ℝ) := by exact_mod_cast hJ
  have he : (d:ℝ)^(3/4:ℝ)*(d:ℝ)^(1/4:ℝ)=d := by
    rw [←Real.rpow_add hd,show (3/4:ℝ)+1/4=1 by norm_num,Real.rpow_one]
  change |h n d / (d:ℝ)| ≤ |h n d| / _ / _
  rw [abs_div,abs_of_pos hd,div_div]
  apply div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos (Real.rpow_pos_of_pos hd _) (Real.rpow_pos_of_pos hJr _))
  apply le_trans _ he.le
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hJd) (by norm_num)) (by positivity)
theorem V1bh (n J : ℕ) (s : Finset ℕ) (hJ : 0<J) (hs : ∀ d ∈ s,J≤d) :
    (∑ d ∈ s, |z n d|) ≤ V2i / (J:ℝ)^(1/4:ℝ) := by
  have hb : s⊆Icc 1 (s.sup id) := by
    intro d hd
    exact mem_Icc.mpr ⟨by have := hs d hd; omega, le_sup (f:=id) hd⟩
  calc
    _ ≤ ∑ d ∈ s, w n d / (J:ℝ)^(1/4:ℝ) := sum_le_sum fun d hd => V239 n J d hJ (hs d hd)
    _ = _ := (sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right ((sum_le_sum_of_subset_of_nonneg hb (fun d _ _ => w_nonneg n d)).trans (V1yh n _)) (by positivity)
theorem V222 (n J : ℕ) (hJ : 0<J) :
    -(V2i / (J:ℝ)^(1/4:ℝ)) ≤ ∑ d ∈ Icc 1 J, z n d := by
  have hu := V1bh n J (J.factorial.divisors \ Icc 1 J) hJ (by
    intro d hd
    obtain ⟨hd,hd'⟩ := mem_sdiff.mp hd
    have hpos := Nat.pos_of_mem_divisors hd
    simp only [mem_Icc,not_and] at hd'
    omega)
  have hh := V20v n J.factorial J.factorial_pos
  rw [←sum_sdiff (s₁:=Icc 1 J) (s₂:=J.factorial.divisors) (V20y J)] at hh
  have ht := sum_le_sum (s:=J.factorial.divisors \ Icc 1 J) (fun d _ => le_abs_self (z n d))
  linarith
end
end Vm
end
section
namespace Vm
open Finset ArithmeticFunction
noncomputable section
def gSum (n X : ℕ) : ℝ := ∑ k ∈ Icc 1 X, g n k
def gAvg (n X : ℕ) : ℝ := gSum n X / X
def fSum (n X : ℕ) : ℝ := ∑ k ∈ Icc 1 X, F n k
theorem V22d (n X : ℕ) : 0≤gSum n X ∧ gSum n X≤X := by
  constructor
  · apply sum_nonneg
    intro k hk
    simp [g]; split_ifs <;> norm_num
  · calc
      _ ≤ ∑ k ∈ Icc 1 X,(1:ℝ) := by
        apply sum_le_sum
        intro k hk
        simp [g]; split_ifs <;> norm_num
      _ = _ := by simp
theorem V1vn (n X : ℕ) : 0≤gAvg n X ∧ gAvg n X≤1 := by
  have hb := V22d n X
  exact ⟨div_nonneg hb.1 (Nat.cast_nonneg _),div_le_one_of_le₀ hb.2 (Nat.cast_nonneg _)⟩
theorem V1zt (n X : ℕ) :
    fSum n X = ∑ d ∈ Icc 1 X,h n d * gSum n (X/d) := by
  classical
  let S := Icc 1 X
  let f := fun v : ℕ × ℕ => h n v.1 * g n v.2
  have hf (q : ℕ) (hq : q ∈ S) :
      q.divisorsAntidiagonal = (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q) := by
    obtain ⟨hq0,hqQ⟩ := mem_Icc.mp hq
    ext ab
    constructor
    · intro hab
      have hm (a : ℕ) (ha : a ∈ q.divisors) : a ∈ S :=
        mem_Icc.mpr ⟨Nat.pos_of_mem_divisors ha,(Nat.le_of_dvd hq0 (Nat.dvd_of_mem_divisors ha)).trans hqQ⟩
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hm _ (Nat.fst_mem_divisors_of_mem_antidiagonal hab),
        hm _ (Nat.snd_mem_divisors_of_mem_antidiagonal hab)⟩,(Nat.mem_divisorsAntidiagonal.mp hab).1⟩
    · intro hh; exact Nat.mem_divisorsAntidiagonal.mpr ⟨(mem_filter.mp hh).2,by omega⟩
  calc
    _ = ∑ q ∈ S,∑ v ∈ q.divisorsAntidiagonal,f v := by
      simp [fSum,S,convolution n,mul_comm (g n) (h n),ArithmeticFunction.mul_apply,f]
    _ = ∑ q ∈ S, ∑ v ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q), f v :=
      sum_congr rfl (fun q hq => by rw [hf q hq])
    _ = ∑ v ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2 ∈ S), f v :=
      sum_fiberwise_eq_sum_filter _ _ _ _
    _ = _ := by
      rw [sum_filter,sum_product]
      apply sum_congr rfl
      intro d hd
      have hd0 := (mem_Icc.mp hd).1
      have hkd : (S.filter fun k => d*k∈S)=Icc 1 (X/d) := by
        ext k
        simp only [S,mem_filter,mem_Icc]
        constructor
        · rintro ⟨⟨hk,_⟩,_,hdk⟩
          exact ⟨hk,(Nat.le_div_iff_mul_le hd0).mpr (by simpa [mul_comm] using hdk)⟩
        · rintro ⟨hk,hkx⟩
          exact ⟨⟨hk,hkx.trans (Nat.div_le_self _ _)⟩,Nat.mul_pos hd0 hk, by simpa [mul_comm] using (Nat.le_div_iff_mul_le hd0).mp hkx⟩
      simp only [f,gSum,mul_sum]
      rw [←sum_filter,hkd]
theorem Vki (f : ℕ→ℝ) {J X : ℕ} (hJX : J≤X) :
    (∑ d ∈ Icc 1 X,f d)=(∑ d ∈ Icc 1 J,f d)+(∑ d ∈ Ioc J X,f d) := by
  have he : Icc 1 X=Icc 1 J ∪ Ioc J X := by ext k; simp only [mem_union,mem_Icc,mem_Ioc]; omega
  rw [he,sum_union (by rw [Finset.disjoint_left]; intro k hk hj; have := (mem_Icc.mp hk).2; have := (mem_Ioc.mp hj).1; omega)]
def Vpk (X d : ℕ) : ℝ := (d:ℝ)*(X/d:ℕ)/X
theorem V1zj (X d : ℕ) (hX : 0<X) (hd : 0<d) :
    0≤ Vpk X d ∧ Vpk X d ≤ 1 ∧ 1-Vpk X d ≤ (d:ℝ)/X := by
  have hx : 0<(X:ℝ) := by exact_mod_cast hX
  have hx0 : (d:ℝ)*(X/d:ℕ) ≤ X := by exact_mod_cast Nat.mul_div_le X d
  have hx1 : (X:ℝ) < (d:ℝ)*((X/d:ℕ)+1:ℝ) := by exact_mod_cast Nat.lt_mul_div_succ X hd
  unfold Vpk
  refine ⟨by positivity,(div_le_iff₀ hx).mpr (by linarith),?_⟩
  rw [sub_div' hx.ne',div_le_div_iff_of_pos_right hx]
  linarith
theorem V1zi (n X d : ℕ) (hd : 0<d) :
    h n d * gSum n (X/d) / X = z n d * (Vpk X d * gAvg n (X/d)) := by
  have hdr : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
  by_cases hy : X/d=0
  · simp [gSum,gAvg,Vpk,hy]
  · have hyr : ((X/d:ℕ):ℝ)≠0 := by exact_mod_cast hy
    simp only [z,coe_mk,Vpk,gAvg]
    field_simp
theorem V228 (n X d : ℕ) (hX : 0<X) (hd : 0<d) (t e : ℝ)
    (he : |gAvg n (X/d)-t|≤e) (hdX : (d:ℝ)/X≤e) :
    |h n d * gSum n (X/d) / X - z n d * t| ≤ |z n d| *(2*e) := by
  obtain ⟨_,hs,hs'⟩ := V1zj X d hX hd
  have hg := V1vn n (X/d)
  have hc : |Vpk X d * gAvg n (X/d)-gAvg n (X/d)| ≤ e := by
    rw [←sub_one_mul,abs_mul,abs_of_nonpos (sub_nonpos.mpr hs),abs_of_nonneg hg.1]
    calc
      _ ≤ -(Vpk X d-1)*1 := mul_le_mul_of_nonneg_left hg.2 (by linarith)
      _ ≤ e := by linarith
  rw [V1zi n X d hd,←mul_sub,abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact (abs_sub_le _ (gAvg n (X/d)) _).trans (by linarith)
theorem V21t (n X J : ℕ) (hX : 0<X) (hJ : 0<J) (hJX : J≤X) (t e : ℝ) (he : 0≤e)
    (hne : ∀ d ∈ Icc 1 J,|gAvg n (X/d)-t|≤e) (hJr : (J:ℝ)/X ≤ e) :
    |fSum n X / X - (∑ d ∈ Icc 1 J,z n d)*t| ≤
      V2i*(2*e)+V2i/(J:ℝ)^(1/4:ℝ) := by
  let a := fun d => h n d * gSum n (X/d) / X
  have hsmall : |∑ d ∈ Icc 1 J,(a d-z n d*t)|≤V2i*(2*e) := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ d ∈ Icc 1 J, |z n d| *(2*e) := by
        refine sum_le_sum fun d hd => V228 n X d hX (mem_Icc.mp hd).1 t e (hne _ hd) ?_
        exact (div_le_div_of_nonneg_right (by exact_mod_cast (mem_Icc.mp hd).2) (Nat.cast_nonneg _)).trans hJr
      _ = _ := (sum_mul _ _ _).symm
      _ ≤ _ := by
        have hu := V1bh n 1 (Icc 1 J) (by decide) (fun d hd => (mem_Icc.mp hd).1)
        norm_num at hu
        exact mul_le_mul_of_nonneg_right hu (by positivity)
  have hlarge : |∑ d ∈ Ioc J X,a d| ≤ V2i/(J:ℝ)^(1/4:ℝ) := by
    apply (abs_sum_le_sum_abs _ _).trans
    apply le_trans _ (V1bh n J (Ioc J X) hJ (fun d hd => (mem_Ioc.mp hd).1.le))
    apply sum_le_sum
    intro d hd
    have hd0 : 0<d := hJ.trans (mem_Ioc.mp hd).1
    obtain ⟨hs,hs',_⟩ := V1zj X d hX hd0
    have hg := V1vn n (X/d)
    dsimp only [a]; rw [V1zi n X d hd0,abs_mul,abs_of_nonneg (mul_nonneg hs hg.1)]
    exact mul_le_of_le_one_right (abs_nonneg _) (mul_le_one₀ hs' hg.1 hg.2)
  have htotal : fSum n X / X = (∑ d ∈ Icc 1 J,a d)+(∑ d ∈ Ioc J X,a d) := by
    rw [V1zt,sum_div]
    exact Vki a hJX
  rw [htotal,sum_mul]
  rw [show (∑ d ∈ Icc 1 J,a d)+(∑ d ∈ Ioc J X,a d)-(∑ d ∈ Icc 1 J,z n d*t)=
      (∑ d ∈ Icc 1 J,(a d-z n d*t))+(∑ d ∈ Ioc J X,a d) by rw [sum_sub_distrib]; ring]
  exact (abs_add_le _ _).trans (add_le_add hsmall hlarge)
end
end Vm
end
section
namespace V4f
open Finset Filter Topology
private def modProd (s : Finset Nat.Primes) : ℕ := ∏ p ∈ s, (p:ℕ)
private theorem V1y2 (s : Finset Nat.Primes) : 0 < modProd s :=
  Finset.prod_pos (fun p _ => p.property.pos)
private theorem V22w (s : Finset Nat.Primes) :
    ((modProd s).totient:ℝ)*(1+∑ p ∈ s, 1/(p:ℝ)) ≤ modProd s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [modProd]
  | @insert p s hps ih =>
    have hcop : (p:ℕ).Coprime (modProd s) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      apply (Nat.coprime_primes p.property q.property).mpr
      intro h
      exact hps ((Subtype.ext h : p=q) ▸ hq)
    have heq : modProd (insert p s) = (p:ℕ)*modProd s := Finset.prod_insert hps
    have hp : (1:ℕ)≤p.val := p.property.one_lt.le
    have hp' : (0:ℝ)<p := by exact_mod_cast p.property.pos
    have hsum : 0 ≤ ∑ q ∈ s, (1:ℝ)/(q:ℝ) := sum_nonneg fun q _ => by positivity
    rw [heq,Nat.totient_mul hcop,Nat.totient_prime p.property,Finset.sum_insert hps]
    push_cast [Nat.cast_sub hp]
    calc
      _ ≤ (p:ℝ)*(((modProd s).totient:ℝ)*(1+∑ q ∈ s, 1/(q:ℝ))) := by
        have : ((p:ℝ)-1)*(1+(1/(p:ℝ)+∑ q ∈ s, 1/(q:ℝ))) ≤ (p:ℝ)*(1+∑ q ∈ s, 1/(q:ℝ)) := by
          field_simp
          nlinarith [mul_nonneg hp'.le hsum]
        nlinarith only [mul_le_mul_of_nonneg_right this (Nat.cast_nonneg (modProd s).totient (α:=ℝ))]
      _ ≤ _ := mul_le_mul_of_nonneg_left ih hp'.le
theorem V1x9 (e : ℝ) (he : 0<e) :
    ∃ D : ℕ, 0<D ∧ (D.totient:ℝ)/(D:ℝ)<e := by
  classical
  have hs : ∃ s : Finset Nat.Primes, (1/e:ℝ) < ∑ p ∈ s, 1/(p:ℝ) := by
    by_contra! h
    exact Nat.Primes.not_summable_one_div (summable_of_sum_le (fun p => by positivity) h)
  obtain ⟨s,hs⟩ := hs
  refine ⟨modProd s,V1y2 s,(div_lt_iff₀ (by exact_mod_cast V1y2 s)).mpr ?_⟩
  have h := V22w s
  have ht : (0:ℝ) < (modProd s).totient := by exact_mod_cast Nat.totient_pos.mpr (V1y2 s)
  have h1 := (div_lt_iff₀ he).mp hs
  nlinarith only [mul_le_mul_of_nonneg_right h he.le,
    mul_lt_mul_of_pos_right h1 ht,mul_pos he ht]
def Vb7 (k X : ℕ) : Finset ℕ :=
  (range X).filter fun n => 0 < n ∧ n.primeFactorsList.length ≤ k
private theorem V241 (k X D : ℕ) (hD : 0<D) :
    (Vb7 (k+1) X).card ≤ D.totient*(X/D+1)+(D+1)*(Vb7 k X).card := by
  classical
  let R := (range X).filter fun n => D.Coprime n
  let cover := (range (D+1)).biUnion fun p => (Vb7 k X).image fun y => p*y
  have hsub : Vb7 (k+1) X ⊆ R ∪ cover := by
    intro x hx
    obtain ⟨hxX,hxp,hxk⟩ := mem_filter.mp hx
    by_cases hc : D.Coprime x
    · exact mem_union_left _ (mem_filter.mpr ⟨hxX,hc⟩)
    obtain ⟨p,hp,hpd,hpx⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    obtain ⟨y,rfl⟩ := hpx
    have hy : y ≠ 0 := by intro hz; simp [hz] at hxp
    have hlen := (Nat.perm_primeFactorsList_mul hp.ne_zero hy).length_eq
    simp [Nat.primeFactorsList_prime hp] at hlen
    have hyX : y < X := lt_of_le_of_lt (by simpa [Nat.mul_comm] using Nat.le_mul_of_pos_left y hp.pos) (mem_range.mp hxX)
    exact mem_union_right _ (mem_biUnion.mpr ⟨p,mem_range.mpr (by have := Nat.le_of_dvd hD hpd; omega),
      mem_image.mpr ⟨y,mem_filter.mpr ⟨mem_range.mpr hyX,by omega,by omega⟩,rfl⟩⟩)
  have hR : R.card ≤ D.totient*(X/D+1) := by
    simpa only [R,zero_add,← range_eq_Ico] using Nat.Ico_filter_coprime_le 0 X hD.ne'
  have hc : cover.card ≤ (D+1)*(Vb7 k X).card := calc
    _ ≤ ∑ p ∈ range (D+1), ((Vb7 k X).image fun y => p*y).card := card_biUnion_le
    _ ≤ ∑ _ ∈ range (D+1), (Vb7 k X).card := by exact Finset.sum_le_sum (fun p _ => card_image_le)
    _ = _ := by simp
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add hR hc))
theorem V1tn (k : ℕ) (e : ℝ) (he : 0<e) :
    ∀ᶠ X : ℕ in atTop, ((Vb7 k X).card:ℝ) ≤ e*X := by
  induction k generalizing e with
  | zero =>
    filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (1/e)] with X hX
    have hsub : Vb7 0 X ⊆ {1} := by
      intro x hx
      obtain ⟨_,hp,hl⟩ := mem_filter.mp hx
      have hn := (Nat.primeFactorsList_eq_nil x).mp (List.length_eq_zero_iff.mp (by omega))
      simp only [mem_singleton]
      omega
    have hc : (Vb7 0 X).card ≤ 1 := by simpa using card_le_card hsub
    change 1/e ≤ (X:ℝ) at hX
    have hh := (div_le_iff₀ he).mp hX
    exact (by exact_mod_cast hc : ((Vb7 0 X).card:ℝ) ≤ 1) |>.trans (by linarith)
  | succ k ih =>
    obtain ⟨D,hD,hphi⟩ := V1x9 (e/4) (by positivity)
    have hD' : (0:ℝ)<D := by exact_mod_cast hD
    filter_upwards [ih (e/(4*(D+1))) (by positivity),
      (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (4*(D.totient:ℝ)/e)] with X hprev hlarge
    change 4*(D.totient:ℝ)/e ≤ X at hlarge
    have hr := (div_le_iff₀ he).mp hlarge
    have hp := (div_lt_iff₀ hD').mp hphi
    have hquot : ((X/D:ℕ):ℝ) ≤ (X:ℝ)/D := by
      apply (le_div_iff₀ hD').mpr
      exact_mod_cast Nat.div_mul_le_self X D
    have h := V241 k X D hD
    have h' : ((Vb7 (k+1) X).card:ℝ) ≤ D.totient*(((X/D:ℕ):ℝ)+1)+((D:ℝ)+1)*(Vb7 k X).card := by exact_mod_cast h
    have hf : ((D:ℝ)+1)*((Vb7 k X).card:ℝ) ≤ (e/4)*X := by
      calc
        _ ≤ ((D:ℝ)+1)*(e/(4*(D+1))*X) := mul_le_mul_of_nonneg_left hprev (by positivity)
        _ = _ := by field_simp
    have hg : (D.totient:ℝ)*((X/D:ℕ):ℝ) ≤ (e/4)*X := calc
      _ ≤ (D.totient:ℝ)*((X:ℝ)/D) := mul_le_mul_of_nonneg_left hquot (by positivity)
      _ = ((D.totient:ℝ)/D)*X := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hphi.le (by positivity)
    nlinarith only [h',hf,hg,hr,mul_nonneg he.le (Nat.cast_nonneg X (α:=ℝ))]
end V4f
end
section
noncomputable section
namespace V4f.Brun
open Finset Filter
def product (s : Finset ℕ) := ∏ p ∈ s, p
def hits (P : Finset ℕ) (m : ℕ) := P.filter (fun p => p ∣ m)
def count (P : Finset ℕ) (X : ℕ) : ℝ := ∑ m ∈ Ioc 0 X, if (hits P m).card=0 then 1 else 0
def harmonic (P : Finset ℕ) : ℝ := ∑ p ∈ P, 1/(p:ℝ)
def Vot (P : Finset ℕ) (j X : ℕ) : ℝ :=
  ∑ s ∈ P.powersetCard j, ((X / product s : ℕ):ℝ)
def trunc (P : Finset ℕ) (r X : ℕ) : ℝ :=
  ∑ j ∈ range (r+1), (-1:ℝ)^j*Vot P j X
lemma prodPos (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime) : 0<product s :=
  prod_pos (fun p h => (hp p h).pos)
lemma prodDvd (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime) (m : ℕ) :
    product s ∣ m ↔ ∀ p ∈ s, p ∣ m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [product]
  | @insert p s hps ih =>
    have hp' := hp p (mem_insert_self _ _)
    have hs := fun q (hq : q∈s) => hp q (mem_insert_of_mem hq)
    have hc : p.Coprime (product s) := Nat.coprime_prod_right_iff.mpr (fun q hq =>
      (Nat.coprime_primes hp' (hs q hq)).mpr fun he => hps (he ▸ hq))
    rw [product,prod_insert hps,forall_mem_insert]
    change p*product s ∣ m ↔ _
    exact ⟨fun h => ⟨(dvd_mul_right p _).trans h,(ih hs).mp ((dvd_mul_left (product s) p).trans h)⟩,
      fun h => hc.mul_dvd_of_dvd_of_dvd h.1 ((ih hs).mpr h.2)⟩
lemma V23q (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime) : (product s).primeFactorsList.length=s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [product]
  | @insert p s hps ih =>
    have hp' := hp p (mem_insert_self _ _)
    have hs := fun q (hq : q∈s) => hp q (mem_insert_of_mem hq)
    have he := (Nat.perm_primeFactorsList_mul hp'.ne_zero (prodPos s hs).ne').length_eq
    change (∏ q ∈ insert p s,q).primeFactorsList.length=_
    rw [prod_insert hps,card_insert_of_notMem hps]
    change (p*product s).primeFactorsList.length=_
    simpa [Nat.primeFactorsList_prime hp',ih hs,Nat.add_comm] using he
theorem V21u (P : Finset ℕ) (hp : ∀ p∈P, p.Prime) (j X : ℕ) :
    Vot P j X = ∑ m ∈ Ioc 0 X, (((hits P m).card.choose j:ℕ):ℝ) := by
  classical
  have hs (m : ℕ) :
      (P.powersetCard j).filter (fun s => product s ∣ m) = (hits P m).powersetCard j := by
    ext s
    simp only [mem_filter,mem_powersetCard]
    constructor
    · rintro ⟨⟨hsub,hj⟩,hd⟩
      exact ⟨fun q hq => mem_filter.mpr ⟨hsub hq,(prodDvd s (fun p h => hp p (hsub h)) m).mp hd q hq⟩,hj⟩
    · rintro ⟨hsub,hj⟩
      have hP (q) (hq:q∈s) := (mem_filter.mp (hsub hq)).1
      exact ⟨⟨fun q hq => hP q hq,hj⟩,(prodDvd s (fun p h => hp p (hP p h)) m).mpr
        (fun q hq => (mem_filter.mp (hsub hq)).2)⟩
  unfold Vot
  simp_rw [←Nat.Ioc_filter_dvd_card_eq_div, ←Finset.sum_boole]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro m _
  rw [Finset.sum_boole,hs,card_powersetCard]
private theorem V23h (k r : ℕ) :
    |(if k=0 then (1:ℝ) else 0) - ∑ j ∈ range (r+1), (-1:ℝ)^j*(k.choose j:ℕ)| ≤ k.choose r := by
  cases k with
  | zero =>
    have hy : (∑ j ∈ range (r+1), (-1:ℝ)^j*(((0:ℕ).choose j):ℕ))=1 := by
      rw [sum_eq_single 0]
      · simp
      · intro j _ hj
        have hh : (0:ℕ).choose j=0 := Nat.choose_eq_zero_of_lt (by omega)
        rw [hh];simp
      · simp
    simp [hy]
  | succ k =>
    have hi := @Int.alternating_sum_range_choose_eq_choose k r
    have hr : (∑ j ∈ range (r+1), (-1:ℝ)^j*(((k+1).choose j):ℕ))=(-1:ℝ)^r*(k.choose r:ℕ) := by exact_mod_cast hi
    rw [if_neg (by omega),zero_sub,abs_neg,hr,abs_mul,abs_pow]
    simpa using (show ((k.choose r:ℕ):ℝ) ≤ ((k+1).choose r:ℕ) by exact_mod_cast Nat.choose_le_succ k r)
theorem V21e (P : Finset ℕ) (hp : ∀ p∈P, p.Prime) (r X : ℕ) :
    |count P X-trunc P r X| ≤ Vot P r X := by
  unfold count trunc
  simp_rw [V21u P hp,Finset.mul_sum]
  rw [Finset.sum_comm (s:=range (r+1)),←sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun m _ => V23h (hits P m).card r))
theorem V20a (P : Finset ℕ) (hp : ∀ p∈P, p.Prime) (r : ℕ) :
    (∑ s ∈ P.powersetCard r, 1/(product s:ℝ)) ≤ Real.exp (2*harmonic P)/(2:ℝ)^r := by
  apply (le_div_iff₀ (by positivity)).mpr
  rw [Finset.sum_mul]
  calc
    _ = ∑ s ∈ P.powersetCard r, ∏ p ∈ s, (2/(p:ℝ)) := by
      apply sum_congr rfl
      intro s hs
      rw [prod_div_distrib,prod_const,(mem_powersetCard.mp hs).2]
      simp [product,div_eq_mul_inv,mul_comm]
    _ ≤ ∑ s ∈ P.powerset, ∏ p ∈ s, (2/(p:ℝ)) :=
      sum_le_sum_of_subset_of_nonneg (fun s hs => mem_powerset.mpr (mem_powersetCard.mp hs).1)
        (fun s _ _ => prod_nonneg (fun _ _ => by positivity))
    _ = ∏ p ∈ P, (1+2/(p:ℝ)) := (prod_one_add ..).symm
    _ ≤ ∏ p ∈ P, Real.exp (2/(p:ℝ)) := by
      apply Finset.prod_le_prod₀ (fun p _ => by positivity)
      intro p hp
      simpa [add_comm] using (Real.add_one_le_exp (2/(p:ℝ)))
    _ = _ := by rw [←Real.exp_sum]; congr 1;unfold harmonic;rw [mul_sum];apply sum_congr rfl;intros;ring
theorem V21q (P : Finset ℕ) (hp : ∀ p∈P, p.Prime) (r X : ℕ) :
    |count P X-trunc P r X| ≤ (X:ℝ)*Real.exp (2*harmonic P)/(2:ℝ)^r := by
  apply (V21e P hp r X).trans
  calc
    Vot P r X ≤ (X:ℝ)*(∑ s ∈ P.powersetCard r, 1/(product s:ℝ)) := by
      unfold Vot
      rw [mul_sum]
      apply sum_le_sum
      intro s _
      simpa only [mul_one_div] using (Nat.cast_div_le (m:=X) (n:=product s) : ((X/product s:ℕ):ℝ)≤X/(product s:ℝ))
    _ ≤ (X:ℝ)*(Real.exp (2*harmonic P)/(2:ℝ)^r) :=
      mul_le_mul_of_nonneg_left (V20a P hp r) (Nat.cast_nonneg _)
    _ = _ := by ring
end V4f.Brun
end
section
noncomputable section
namespace V4f.Brun
open Finset Filter
private lemma V22v (m d : ℕ) (hd : 0<d) :
    (m:ℝ)/d-1 ≤ ((m/d:ℕ):ℝ) ∧ ((m/d:ℕ):ℝ) ≤ m/(d:ℝ) := by
  refine ⟨?_,Nat.cast_div_le⟩
  have h : (m:ℝ) < d * (((m/d:ℕ):ℝ)+1) := by exact_mod_cast Nat.lt_mul_div_succ m hd
  have hh : (m:ℝ)/d < ((m/d:ℕ):ℝ)+1 := (div_lt_iff₀ (by exact_mod_cast hd)).mpr (by linarith)
  linarith
private lemma V23u (X Y d : ℕ) (hd : 0<d) (hY : 0<Y) :
    |((X/d:ℕ):ℝ)-(X:ℝ)/Y*((Y/d:ℕ):ℝ)| ≤ 1+(X:ℝ)/Y := by
  have hY' : (0:ℝ)<Y := by exact_mod_cast hY
  have hpos : 0≤(X:ℝ)/Y := by positivity
  obtain ⟨a,b⟩ := V22v X d hd
  obtain ⟨c,e⟩ := V22v Y d hd
  have h : (X:ℝ)/Y*(Y/(d:ℝ))=X/(d:ℝ) := by field_simp
  have h1 := mul_le_mul_of_nonneg_left c hpos
  have h2 := mul_le_mul_of_nonneg_left e hpos
  rw [h] at h2
  rw [mul_sub,h,mul_one] at h1
  rw [abs_le]
  constructor <;> linarith
private lemma V23t (P : Finset ℕ) (hp : ∀ p∈P,p.Prime) (r j X : ℕ) (hj : j≤r) :
    ((P.powersetCard j).filter (fun s => product s ≤ X)).card ≤
      (V4f.Vb7 r (X+1)).card := by
  apply Finset.card_le_card_of_injOn product
  · intro s hs
    obtain ⟨hP,hX⟩ := mem_filter.mp hs
    obtain ⟨hsub,hcard⟩ := mem_powersetCard.mp hP
    have hPrime (q) (hq:q∈s) := hp q (hsub hq)
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),prodPos s hPrime,(V23q s hPrime).trans_le (hcard.trans_le hj)⟩
  · intro s hs t ht e
    have h1 := (mem_powersetCard.mp (mem_filter.mp hs).1).1
    have h2 := (mem_powersetCard.mp (mem_filter.mp ht).1).1
    have hs' : (product s).primeFactors=s := Nat.primeFactors_prod (fun q hq => hp q (h1 hq))
    have ht' : (product t).primeFactors=t := Nat.primeFactors_prod (fun q hq => hp q (h2 hq))
    rw [←hs',e,ht']
private lemma V23s (P : Finset ℕ) (hp : ∀ p∈P,p.Prime) (r j X Y : ℕ)
    (hj : j≤r) (hY : 0<Y) (hYX : Y≤X) :
    |Vot P j X-(X:ℝ)/Y*Vot P j Y| ≤
      ((V4f.Vb7 r (X+1)).card:ℝ)*(1+(X:ℝ)/Y) := by
  classical
  unfold Vot
  rw [mul_sum,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ s ∈ P.powersetCard j, if product s≤X then 1+(X:ℝ)/Y else 0 := by
      apply sum_le_sum
      intro s hs
      split_ifs with h
      · exact V23u X Y (product s) (prodPos s (fun q hq => hp q ((mem_powersetCard.mp hs).1 hq))) hY
      · have hx : X<product s := by omega
        simp [Nat.div_eq_of_lt hx,Nat.div_eq_of_lt (hYX.trans_lt hx)]
    _ = (((P.powersetCard j).filter (fun s => product s ≤ X)).card:ℝ)*(1+(X:ℝ)/Y) := by
      rw [←sum_filter];simp;ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast V23t P hp r j X hj) (by positivity)
theorem V23n (P : Finset ℕ) (hp : ∀ p∈P,p.Prime) (r X Y : ℕ)
    (hY : 0<Y) (hYX : Y≤X) :
    |trunc P r X-(X:ℝ)/Y*trunc P r Y| ≤
      ((r:ℝ)+1)*((V4f.Vb7 r (X+1)).card:ℝ)*(1+(X:ℝ)/Y) := by
  unfold trunc
  rw [mul_sum,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ j ∈ range (r+1), ((V4f.Vb7 r (X+1)).card:ℝ)*(1+(X:ℝ)/Y) := by
      apply sum_le_sum
      intro j hj
      have hh := V23s P hp r j X Y (by have := mem_range.mp hj;omega) hY hYX
      rw [show (X:ℝ)/Y*((-1:ℝ)^j*Vot P j Y)=(-1:ℝ)^j*((X:ℝ)/Y*Vot P j Y) by ring,
        ←mul_sub,abs_mul,abs_pow]
      simpa using hh
    _ = _ := by simp [mul_assoc]
end V4f.Brun
end
section
noncomputable section
namespace V4f.Brun
open Finset Filter
theorem V221 (H C e : ℝ) (hC : 1≤C) (he : 0<e) :
    ∀ᶠ X : ℕ in atTop, ∀ Y : ℕ, 0<Y → Y≤X → (X:ℝ)≤C*Y →
    ∀ P : Finset ℕ, (∀ p∈P,p.Prime) → harmonic P≤H →
    |count P X/X - count P Y/Y| ≤ e := by
  obtain ⟨r,hr⟩ := pow_unbounded_of_one_lt (4*Real.exp (2*H)/e) (show (1:ℝ)<2 by norm_num)
  let A : ℝ := ((r:ℝ)+1)*(1+C)
  have hA : 0<A := by dsimp [A];positivity
  have heps : 0<e/(4*A) := by positivity
  obtain ⟨x₀,hx⟩ := eventually_atTop.mp (V4f.V1tn r (e/(4*A)) heps)
  filter_upwards [eventually_ge_atTop x₀,eventually_ge_atTop 1] with X hX hX1
  intro Y hY hYX hscale P hp hH
  have hY' : (0:ℝ)<Y := by exact_mod_cast hY
  have hX' : (0:ℝ)<X := by exact_mod_cast hX1
  have hx1 : (1:ℝ)≤X := by exact_mod_cast hX1
  have hRatio : (X:ℝ)/Y≤C := (div_le_iff₀ hY').mpr hscale
  have hR : 0≤(X:ℝ)/Y := by positivity
  have hExp := Real.exp_le_exp.mpr (show 2*harmonic P≤2*H by linarith)
  have hcoeff : Real.exp (2*harmonic P)/(2:ℝ)^r ≤ e/4 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have := (div_lt_iff₀ he).mp hr
    nlinarith
  have err (W : ℕ) : |count P W-trunc P r W| ≤ (W:ℝ)*(e/4) := by
    refine (V21q P hp r W).trans ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hcoeff (Nat.cast_nonneg _)
  have hf := hx (X+1) (by omega)
  push_cast at hf
  have hL : ((r:ℝ)+1)*((V4f.Vb7 r (X+1)).card:ℝ)*(1+(X:ℝ)/Y) ≤ (X:ℝ)*(e/2) := by
    calc
      _ ≤ ((r:ℝ)+1)*((V4f.Vb7 r (X+1)).card:ℝ)*(1+C) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = A*((V4f.Vb7 r (X+1)).card:ℝ) := by dsimp [A];ring
      _ ≤ A*(e/(4*A)*((X:ℝ)+1)) := mul_le_mul_of_nonneg_left hf hA.le
      _ = e/4*((X:ℝ)+1) := by field_simp
      _ ≤ _ := by nlinarith [mul_nonneg he.le (sub_nonneg.mpr hx1)]
  have ht := (V23n P hp r X Y hY hYX).trans hL
  have hE : |(X:ℝ)/Y*trunc P r Y-(X:ℝ)/Y*count P Y| ≤ (X:ℝ)*(e/4) := by
    rw [←mul_sub,abs_mul,abs_of_nonneg hR,abs_sub_comm]
    calc
      _ ≤ ((X:ℝ)/Y)*(Y*(e/4)) := mul_le_mul_of_nonneg_left (err _) hR
      _ = _ := by field_simp
  have hT := abs_sub_le (count P X) (trunc P r X) ((X:ℝ)/Y*count P Y)
  have hU := abs_sub_le (trunc P r X) ((X:ℝ)/Y*trunc P r Y) ((X:ℝ)/Y*count P Y)
  have hab : |count P X-(X:ℝ)/Y*count P Y|≤e*X := by linarith [err X]
  rw [show count P X/(X:ℝ)-count P Y/Y=(count P X-(X:ℝ)/Y*count P Y)/X by field_simp,
    abs_div,abs_of_pos hX']
  exact (div_le_iff₀ hX').mpr hab
end V4f.Brun
end
section
noncomputable section
namespace Vm
open Finset Filter V4f.Brun
def Vtf (n X : ℕ) : Finset ℕ := (Icc 1 X).filter (fun p => p.Prime ∧ ¬p∣n)
def meanG (n X : ℕ) : ℝ := (∑ k ∈ Icc 1 X,g n k)/X
theorem V21w (n X T : ℕ) (hT : T≤X) :
    count (Vtf n X) T = ∑ k ∈ Icc 1 T,g n k := by
  unfold count
  have hset : Ioc 0 T=Icc 1 T := by ext k;simp;omega
  rw [hset]
  apply sum_congr rfl
  intro k hk
  obtain ⟨hk1,hkT⟩ := mem_Icc.mp hk
  have h0 : k≠0 := by omega
  have he : (hits (Vtf n X) k).card=0 ↔ smooth n k := by
    rw [Finset.card_eq_zero]
    constructor
    · intro h p hp
      by_contra hn
      obtain ⟨hp',hpk,_⟩ := Nat.mem_primeFactors.mp hp
      have hpX := (Nat.le_of_dvd (by omega : 0<k) hpk).trans (hkT.trans hT)
      have hmem : p ∈ hits (Vtf n X) k := mem_filter.mpr
        ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hp'.one_lt.le,hpX⟩,hp',hn⟩,hpk⟩
      simp [h] at hmem
    · intro hs
      apply eq_empty_iff_forall_notMem.mpr
      intro p hpm
      obtain ⟨hP,hpk⟩ := mem_filter.mp hpm
      obtain ⟨_,hp,hn⟩ := mem_filter.mp hP
      exact hn (hs p (Nat.mem_primeFactors.mpr ⟨hp,hpk,h0⟩))
  simp [g,h0,he]
theorem V1v6 (n X : ℕ) : 0≤ meanG n X := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply sum_nonneg
  intro k _
  simp only [g,ArithmeticFunction.coe_mk];split_ifs <;> norm_num
end Vm
end
section
namespace Vm
open Finset
noncomputable section
def frequency (P : Finset ℕ) : ℝ := ∑ p ∈ P, (p:ℝ)⁻¹
def hit (p k : ℕ) : ℝ := if p ∣ k then 1 else 0
def V1nk (P : Finset ℕ) (k : ℕ) : ℝ := ∑ p ∈ P, hit p k
theorem hit_sum (p X : ℕ) : (∑ k ∈ Icc 1 X, hit p k) = (X/p : ℕ) := by
  have he : Icc 1 X=Ioc 0 X := by ext k; simp only [mem_Icc,mem_Ioc]; omega
  unfold hit
  rw [he,Finset.sum_boole,Nat.Ioc_filter_dvd_card_eq_div]
theorem V234 (P : Finset ℕ) (X : ℕ) (hP : ∀ p ∈ P, 0<p) :
    (X:ℝ)*frequency P-P.card ≤ ∑ k ∈ Icc 1 X,V1nk P k := by
  simp only [V1nk,Finset.sum_comm (s:=Icc 1 X) (t:=P),hit_sum]
  calc
    _ = ∑ p ∈ P, ((X:ℝ)*(p:ℝ)⁻¹-1) := by simp [frequency,mul_sum,sum_sub_distrib]
    _ ≤ _ := by
      apply sum_le_sum
      intro p hp
      have hpr : 0<(p:ℝ) := by exact_mod_cast hP p hp
      have hc : (X:ℝ) < (p:ℝ)*((X/p:ℕ)+1:ℝ) := by exact_mod_cast Nat.lt_mul_div_succ X (hP p hp)
      have hh : (X:ℝ)/(p:ℝ) ≤ ((X/p:ℕ):ℝ)+1 := (div_le_iff₀ hpr).mpr (by linarith)
      linarith [show (X:ℝ)*(p:ℝ)⁻¹ = X/p by rw [div_eq_mul_inv]]
theorem hitPair (X p r : ℕ) (hp : p.Prime) (hr : r.Prime) :
    (∑ k ∈ Icc 1 X,hit p k * hit r k) ≤
      (X:ℝ)*((p:ℝ)⁻¹*(r:ℝ)⁻¹) + (if p=r then (X:ℝ)*(p:ℝ)⁻¹ else 0) := by
  by_cases he : p=r
  · subst r
    have hh (k : ℕ) : hit p k*hit p k=hit p k := by by_cases hk : p∣k <;> simp [hit,hk]
    simp only [hh,hit_sum,ite_true]
    exact (Nat.cast_div_le (α:=ℝ)).trans (by rw [div_eq_mul_inv]; exact le_add_of_nonneg_left (by positivity))
  · have hh (k : ℕ) : hit p k*hit r k=hit (p*r) k := by
      have hc := (Nat.coprime_primes hp hr).mpr he
      have eqv : p*r∣k ↔ p∣k ∧ r∣k := ⟨fun hk => ⟨(dvd_mul_right p r).trans hk,(dvd_mul_left r p).trans hk⟩,fun hk => hc.mul_dvd_of_dvd_of_dvd hk.1 hk.2⟩
      by_cases ha : p∣k <;> by_cases hb : r∣k <;> simp [hit,eqv,ha,hb]
    simp only [hh,hit_sum,if_neg he,add_zero]
    exact (Nat.cast_div_le (α:=ℝ)).trans_eq (by simp [div_eq_mul_inv,mul_comm])
theorem V223 (P : Finset ℕ) (X : ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∑ k ∈ Icc 1 X,(V1nk P k)^2) ≤ (X:ℝ)*(frequency P)^2+X*frequency P := by
  have hswap (f : ℕ → ℕ → ℕ → ℝ) :
      (∑ k ∈ Icc 1 X,∑ p ∈ P,∑ r ∈ P,f k p r)=∑ p ∈ P,∑ r ∈ P,∑ k ∈ Icc 1 X,f k p r := by
    rw [sum_comm]
    exact sum_congr rfl fun _ _ => sum_comm
  simp only [V1nk,sq,sum_mul_sum,hswap]
  calc
    _ ≤ ∑ p ∈ P,∑ r ∈ P, ((X:ℝ)*((p:ℝ)⁻¹*(r:ℝ)⁻¹)+(if p=r then (X:ℝ)*(p:ℝ)⁻¹ else 0)) :=
      sum_le_sum fun p hp => sum_le_sum fun r hr => hitPair X p r (hP p hp) (hP r hr)
    _ = _ := by
      simp only [sum_add_distrib,←mul_sum,sum_ite_eq]
      unfold frequency
      congr 1
      · rw [←Finset.sum_mul]
      · rw [mul_sum]
        exact sum_congr rfl fun p hp => by simp [hp]
theorem highH (n X : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ ¬p∣n) :
    frequency P * (∑ k ∈ Icc 1 X, g n k) ≤ (X:ℝ) + 2*P.card := by
  let H := frequency P
  have hH : 0≤H := sum_nonneg fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p)
  rcases hH.eq_or_lt with hz | hpos
  · change H*_ ≤ _
    rw [←hz,zero_mul]; positivity
  have h1 := V234 P X (fun p hp => (hP p hp).1.pos)
  have h2 := V223 P X (fun p hp => (hP p hp).1)
  have hdom : (∑ k ∈ Icc 1 X, g n k * H^2) ≤ ∑ k ∈ Icc 1 X, (V1nk P k-H)^2 := by
    apply sum_le_sum
    intro k hk
    have hk0 : k≠0 := by have := (mem_Icc.mp hk).1; omega
    by_cases hsm : smooth n k
    · have h0 : V1nk P k=0 := by
        apply sum_eq_zero
        intro p hp
        have hn := (hP p hp).2
        have hpk : ¬p∣k := fun hpk => hn (hsm p (Nat.mem_primeFactors.mpr ⟨(hP p hp).1,hpk,hk0⟩))
        simp [hit,hpk]
      simp [g,hk0,hsm,h0]
    · simp [g,hk0,hsm,sq_nonneg]
  have he (k : ℕ) : (V1nk P k-H)^2=(V1nk P k)^2 - V1nk P k*(2*H)+ H^2 := by ring
  simp only [he,sum_add_distrib,sum_sub_distrib,←sum_mul,sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel] at hdom
  change (X:ℝ)*H-_≤_ at h1
  change _≤(X:ℝ)*H^2+X*H at h2
  have h3 := mul_le_mul_of_nonneg_right h1 (mul_nonneg (by norm_num : (0:ℝ)≤2) hpos.le)
  apply le_of_mul_le_mul_right (a:=H) _ hpos
  nlinarith only [hdom,h3,h2]
end
end Vm
end
section
noncomputable section
namespace Vm
open Finset Filter V4f.Brun
theorem V22r (C e : ℝ) (hC : 1≤C) (he : 0<e) :
    ∀ᶠ X : ℕ in atTop, ∀ Y : ℕ, 0<Y → Y≤X → (X:ℝ)≤C*Y →
    ∀ n, |meanG n X-meanG n Y|≤e := by
  let H : ℝ := (1+2*C)/e
  have hHpos : 0<H := by dsimp [H];positivity
  filter_upwards [V221 H C e hC he] with X hlow
  intro Y hY hYX hscale n
  let P := Vtf n X
  have hprime (p) (hp : p∈P) : p.Prime ∧ ¬p∣n := (mem_filter.mp hp).2
  have hh : harmonic P=frequency P := by simp [V4f.Brun.harmonic,frequency,one_div]
  by_cases hc : harmonic P≤H
  · have hh := hlow Y hY hYX hscale P (fun p h => (hprime p h).1) hc
    rwa [V21w n X X le_rfl,V21w n X Y hYX] at hh
  · have hPH := lt_of_not_ge hc
    rw [hh] at hPH
    have hPcard : P.card≤X := (card_filter_le ..).trans_eq (by simp)
    have hX' : (0:ℝ)<X := by exact_mod_cast hY.trans_le hYX
    have hyp : (0:ℝ)<Y := by exact_mod_cast hY
    have hscaleX : (X:ℝ)≤C*X := by simpa using (mul_le_mul_of_nonneg_right hC hX'.le)
    have hb (T : ℕ) (ht : (0:ℝ)<T) (hscaleT : (X:ℝ)≤C*T) : meanG n T≤e := by
      have hcard' : (P.card:ℝ) ≤ C*T := (show (P.card:ℝ)≤X by exact_mod_cast hPcard).trans hscaleT
      have hbound := highH n T P hprime
      have hp : 0≤∑ k ∈ Icc 1 T,g n k := by
        have hh := V1v6 n T
        unfold meanG at hh
        simpa [ht.ne'] using mul_nonneg hh ht.le
      have hlo := mul_le_mul_of_nonneg_right hPH.le hp
      have hHS : H*(∑ k ∈ Icc 1 T,g n k) ≤ (1+2*C)*T := by linarith
      have hid : (1+2*C)*T=H*(e*T) := by dsimp [H];field_simp
      rw [hid] at hHS
      exact (div_le_iff₀ ht).mpr ((mul_le_mul_iff_right₀ hHpos).mp hHS)
    have hx := hb X hX' hscaleX
    have hy := hb Y hyp hscale
    rw [abs_le]
    constructor <;> linarith [V1v6 n X, V1v6 n Y]
end Vm
end
section
namespace Vm
open Finset Filter
noncomputable section
theorem V1uk (R : ℕ) (hR : 1 ≤ R) (δ : ℝ) (hδ : 0<δ) :
    ∃ A₀ : ℕ, ∀ A ≥ A₀, ∀ n i : ℕ, A ≤ i → i ≤ R*A →
      -(δ*(A:ℝ))  ≤  ∑ q ∈ Finset.Ioc A i,F n q := by
  have hr : (1:ℝ) ≤ R := by exact_mod_cast hR
  have hu : 0<V2i := Real.exp_pos _
  let τ : ℝ := δ/(8*((R:ℝ)+1))
  have hτ : 0<τ := by dsimp [τ]; positivity
  let e : ℝ := τ/(V2i+1)
  have he : 0<e := by dsimp [e]; positivity
  have heu : V2i*e  ≤  τ := by
    have heq : e*(V2i+1)=τ := by dsimp [e]; field_simp
    nlinarith
  obtain ⟨N,hN⟩ := exists_nat_ge (V2i/τ)
  let J := (N+1)^4
  have hJ : 0<J := by dsimp [J]; positivity
  have hj : (J:ℝ)^(1/4:ℝ)=(N:ℝ)+1 := by
    dsimp [J]; push_cast
    rw [←Real.rpow_natCast_mul (by positivity),show (↑(4:ℕ):ℝ)*(1/4)=1 by norm_num,Real.rpow_one]
  have ht : V2i/(J:ℝ)^(1/4:ℝ)  ≤  τ := by
    rw [hj]
    apply (div_le_iff₀ (by positivity)).mpr
    have := (div_le_iff₀ hτ).mp hN
    nlinarith
  let C : ℝ := 2*(R:ℝ)*J
  have hjr : (1:ℝ) ≤ J := by exact_mod_cast hJ
  have hC : 1 ≤ C := by dsimp [C]; nlinarith [mul_le_mul hr hjr (by norm_num) (by positivity)]
  obtain ⟨M,hM⟩ := eventually_atTop.mp (V22r C e hC he)
  obtain ⟨L,hL⟩ := exists_nat_ge ((J:ℝ)/e)
  refine ⟨max J (max M L),?_⟩
  intro A hA n i hAi hiA
  have hJA : J ≤ A := by omega
  have hA0 : 0<A := hJ.trans_le hJA
  have hAr : (0:ℝ)<A := by exact_mod_cast hA0
  have hi0 : 0 < i := hA0.trans_le hAi
  have hir : (0:ℝ) < i := by exact_mod_cast hi0
  have hscale : (i:ℝ) ≤ R*(A:ℝ) := by exact_mod_cast hiA
  let t := gAvg n i
  let Z := ∑ d ∈ Icc 1 J,z n d
  have ht01 : 0 ≤ t ∧ t ≤ 1 := V1vn n i
  have hz : -τ ≤ Z := by have hz' := V222 n J hJ; dsimp [Z]; linarith
  have hlin (X : ℕ) (hAX : A ≤ X) (hXi : X ≤ i) :
      |fSum n X-(X:ℝ)*(Z*t)|  ≤  X*(3*τ) := by
    have hX : 0<X := hA0.trans_le hAX
    have hxr : (0:ℝ)<X := by exact_mod_cast hX
    have hjx : (J:ℝ)/X ≤ e := by
      apply (div_le_iff₀ hxr).mpr
      have hLX : (L:ℝ) ≤ X := by exact_mod_cast (show L ≤ X by omega)
      have := (div_le_iff₀ he).mp (hL.trans hLX)
      linarith
    have hnear (d : ℕ) (hd : d∈Icc 1 J) : |gAvg n (X/d)-t| ≤ e := by
      obtain ⟨hd0,hdJ⟩ := mem_Icc.mp hd
      have hdX : d ≤ X := by omega
      have hy : 0<X/d := Nat.div_pos hdX hd0
      have hii : i ≤ R*X := hiA.trans (Nat.mul_le_mul_left R hAX)
      have hratio : X ≤ (2*J)*(X/d) := by
        calc
          X  ≤  d*(X/d+1) := (Nat.lt_mul_div_succ X hd0).le
          _  ≤  J*(2*(X/d)) := Nat.mul_le_mul hdJ (by omega)
          _ = _ := by ring
      have hcxy : (i:ℝ) ≤ C*(X/d:ℕ) := by
        dsimp [C]
        exact_mod_cast (show i ≤ 2*R*J*(X/d) from hii.trans (by calc
          R*X  ≤  R*((2*J)*(X/d)) := Nat.mul_le_mul_left R hratio
          _ = _ := by ring))
      rw [abs_sub_comm]
      exact hM i (by omega) (X/d) hy ((Nat.div_le_self X d).trans hXi) hcxy n
    have h := V21t n X J hX hJ (by omega) t e he.le hnear hjx
    have ha : |fSum n X / X - Z*t| ≤ 3*τ := h.trans (by linarith)
    have eqv : fSum n X-(X:ℝ)*(Z*t)=(X:ℝ)*(fSum n X/X-Z*t) := by field_simp
    rw [eqv,abs_mul,abs_of_pos hxr]
    exact mul_le_mul_of_nonneg_left ha hxr.le
  have ha := abs_le.mp (hlin A le_rfl hAi)
  have hb := abs_le.mp (hlin i hAi le_rfl)
  have htZ : -τ  ≤  Z*t := by
    calc
      -τ  ≤  -τ*t := by nlinarith [mul_nonneg hτ.le (sub_nonneg.mpr ht01.2)]
      _  ≤  _ := mul_le_mul_of_nonneg_right hz ht01.1
  have hia : (A:ℝ) ≤ i := by exact_mod_cast hAi
  have hdiff := mul_le_mul_of_nonneg_left htZ (sub_nonneg.mpr hia)
  have heqτ : (8*((R:ℝ)+1))*τ=δ := by dsimp [τ]; field_simp
  have htot : (i:ℝ)*τ  ≤  R*A*τ := mul_le_mul_of_nonneg_right hscale hτ.le
  have hgood : -(δ*(A:ℝ)) ≤ fSum n i-fSum n A := by
    have δeq : δ*(A:ℝ)=(8*((R:ℝ)+1))*τ*A := by rw [heqτ]
    nlinarith only [ha.1,ha.2,hb.1,hb.2,hdiff,htot,δeq,
      mul_nonneg (Nat.cast_nonneg R) (mul_nonneg hAr.le hτ.le),mul_nonneg hAr.le hτ.le]
  have hsplit := Vki (fun q => F n q) hAi
  change fSum n i=fSum n A+_ at hsplit
  linarith
end
end Vm
end
end
end
end
end
end
end GoldbachGRHBandBase
section GoldbachGRHRamanujanMobius
open scoped BigOperators
namespace Vr
theorem V127 (q : ℕ) :
    ram q 1 = (ArithmeticFunction.moebius q : ℂ) := by
  induction q using Nat.recOnPrimeCoprime with
  | zero => simp [ram]
  | prime_pow p j hp =>
    cases j with
    | zero => simp [ram_one]
    | succ k =>
      have hd (a : ℕ) : ¬ p ^ (a + 1) ∣ 1 := by
        intro ha
        exact (Nat.one_lt_pow (Nat.succ_ne_zero a) hp.one_lt).ne' (Nat.dvd_one.mp ha)
      rw [V1n3 p k 1 hp,
        ArithmeticFunction.moebius_apply_prime_pow hp (Nat.succ_ne_zero k), ite_eq_right (hd k)]
      cases k with
      | zero => norm_num
      | succ k => simp [hd k]
  | coprime q r hq hr hqr iq ir =>
    rw [ram_mul (by omega) (by omega) hqr, iq, ir,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hqr, Int.cast_mul]
end Vr
namespace V54
theorem V1ol {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a) :
    V8a q a = (ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) := by
  rw [V1tz a ha]
  have h := V1el (q := q) 1
  have hr : V8a q 1 =
      Vr.ram q 1 / (q.totient : ℂ) := by
    simpa only [Nat.cast_one, Vr.ram,
      Vr.phase] using h
  rw [hr, Vr.V127]
end V54
end GoldbachGRHRamanujanMobius
section V24
open MeasureTheory Set Finset
open scoped Interval
namespace V24
open V31 (phase V13v)
noncomputable def kernel (n : ℕ) : ℝ → ℂ :=
  Vcr.poly (n + 1) fun _ => 1
noncomputable def mass (n : ℕ) (r : ℝ) : ℝ :=
  ∫ t in (-r)..r, ‖kernel n t‖ ^ 2
theorem V1h5 (n : ℕ) (t : ℝ) :
    kernel n t = ∑ k ∈ range (n + 1), phase ((k : ℝ) * t) := by
  simp [kernel, Vcr.poly]
theorem V22q (k : ℕ) : phase (k : ℝ) = 1 := by
  unfold phase
  have h : (((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) =
      (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h]
  exact_mod_cast Complex.exp_int_mul_two_pi_mul_I (k : ℤ)
theorem V20j (n : ℕ) : Function.Periodic (kernel n) 1 := by
  intro t
  simp only [V1h5, mul_add, mul_one, V13v, V22q, mul_one]
theorem Vhc (n : ℕ) : Continuous (kernel n) := by
  rw [show kernel n = fun t => ∑ k ∈ range (n + 1), phase ((k : ℝ) * t) from
    funext (V1h5 n)]
  unfold phase
  fun_prop
theorem reflect (n : ℕ) (t : ℝ) :
    kernel n t ^ 2 * phase (-(n : ℝ) * t) = (↑(‖kernel n t‖ ^ 2) : ℂ) := by
  simp only [V1h5, ← Complex.normSq_eq_norm_sq]
  exact V159 n t
theorem V21o (n : ℕ) :
    (∫ t in (0 : ℝ)..1, ‖kernel n t‖ ^ 2) = (n : ℝ) + 1 := by
  simpa [kernel] using Vcr.V23f (n + 1) (fun _ => (1 : ℂ))
theorem V20p (n : ℕ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ mass n r :=
  intervalIntegral.integral_nonneg_of_forall (by linarith) fun _ => sq_nonneg _
theorem V22s (n : ℕ) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    mass n r ≤ mass n s := by
  apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) hrs
  · exact Filter.Eventually.of_forall fun _ => sq_nonneg _
  · exact ((Vhc n).norm.pow 2).intervalIntegrable _ _
theorem V23r (n : ℕ) {r : ℝ} (hr : 0 < r) (hh : r ≤ 1 / 2) :
    0 ≤ (n : ℝ) + 1 - mass n r ∧
      (n : ℝ) + 1 - mass n r ≤ 1 / (2 * r) := by
  let F : ℝ → ℝ := fun t => ‖kernel n t‖ ^ 2
  have hF : Continuous F := (Vhc n).norm.pow 2
  have hp : Function.Periodic F 1 := by
    intro t
    simp only [F, V20j n t]
  have hfull : (∫ t in (-r)..(1 - r), F t) = (n : ℝ) + 1 := by
    have h := hp.intervalIntegral_add_eq (-r) 0
    rw [show -r + 1 = 1 - r by ring, zero_add] at h
    exact h.trans (V21o n)
  have hsplit :
      mass n r + (∫ t in r..(1 - r), F t) = (n : ℝ) + 1 := by
    have h := intervalIntegral.integral_add_adjacent_intervals
      (hF.intervalIntegrable (μ := volume) (-r) r) (hF.intervalIntegrable r (1 - r))
    exact h.trans hfull
  have htail : (n : ℝ) + 1 - mass n r = ∫ t in r..(1 - r), F t := by
    linarith only [hsplit]
  have hordered : r ≤ 1 - r := by linarith only [hh]
  have hrepr : (∫ t in (0 : ℝ)..1, (Ioc r (1 - r)).indicator F t) =
      ∫ t in r..(1 - r), F t := by
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le hordered,
      MeasureTheory.integral_indicator measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc]
    rw [inter_eq_left.mpr (Ioc_subset_Ioc hr.le (by linarith only [hr]))]
  have hcut : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ Ioc r (1 - r) →
      r ≤ |(1 : ℝ) * t - (round ((1 : ℝ) * t) : ℝ)| := by
    intro t ht hz
    rw [one_mul]
    by_cases hhalf : t < 1 / 2
    · have hround : round t = 0 :=
        round_eq_zero_iff.mpr ⟨by linarith only [ht.1], hhalf⟩
      simp only [hround, Int.cast_zero, sub_zero, abs_of_nonneg ht.1]
      exact hz.1.le
    · have hround : round t = 1 := round_eq_iff.mpr (by
        change ((1 : ℤ) : ℝ) - 1 / 2 ≤ t ∧ t < ((1 : ℤ) : ℝ) + 1 / 2
        push_cast
        constructor <;> linarith only [hhalf, ht.2])
      simp only [hround, Int.cast_one, abs_of_nonpos (sub_nonpos.mpr ht.2)]
      linarith only [hz.2]
  have hbound := V1iv (n + 1) 1 Nat.one_pos r hr hh
    (Ioc r (1 - r)) measurableSet_Ioc hcut
  simp only [Nat.cast_one, one_mul] at hbound
  have hboundF : (∫ t in (0 : ℝ)..1, (Ioc r (1 - r)).indicator F t) ≤ 1 / (2 * r) := by
    simpa only [F, V1h5, phase, mul_assoc] using hbound
  rw [hrepr] at hboundF
  rw [htail]
  exact ⟨intervalIntegral.integral_nonneg_of_forall hordered (fun _ => sq_nonneg _), hboundF⟩
end V24
end V24
section V19
open Finset MeasureTheory Set
open scoped Interval
namespace V19
noncomputable abbrev cap := Vpg.wide
def centers (U : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 U) ×ˢ (Finset.range (U+1))).filter
    (fun i => i.2 ≤ i.1 ∧ Nat.Coprime i.2 i.1)
theorem Vcx {U : ℕ} {i : ℕ × ℕ} :
    i ∈ centers U ↔ 1 ≤ i.1 ∧ i.1 ≤ U ∧ i.2 ≤ i.1 ∧ Nat.Coprime i.2 i.1 := by
  simp only [centers, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨⟨⟨h₁, h₂⟩, _⟩, h₃, h₄⟩
    exact ⟨h₁,h₂,h₃,h₄⟩
  · rintro ⟨h₁,h₂,h₃,h₄⟩
    exact ⟨⟨⟨h₁,h₂⟩, by omega⟩,h₃,h₄⟩
theorem V1w1 {Q U : ℕ} (h : Q ≤ U) : centers Q ⊆ centers U := by
  intro i hi
  obtain ⟨h₁,h₂,h₃,h₄⟩ := Vcx.mp hi
  exact Vcx.mpr ⟨h₁,h₂.trans h,h₃,h₄⟩
noncomputable def radius (n H q : ℕ) : ℝ := (H : ℝ) / ((q : ℝ) * (n : ℝ))
noncomputable def center (i : ℕ × ℕ) : ℝ := (i.2 : ℝ) / (i.1 : ℝ)
noncomputable def arc (n H : ℕ) (i : ℕ × ℕ) : Set ℝ :=
  {t | |t - center i| ≤ radius n H i.1}
theorem Vkk (n H : ℕ) (i : ℕ × ℕ) : MeasurableSet (arc n H i) := by
  unfold arc
  exact measurableSet_le (show Continuous (fun t : ℝ => |t - center i|) by fun_prop).measurable
    measurable_const
theorem V1sc (n H : ℕ) (i : ℕ × ℕ) :
    arc n H i = Set.Icc (center i - radius n H i.1) (center i + radius n H i.1) := by
  ext t
  change |t - center i| ≤ radius n H i.1 ↔ _
  rw [abs_le, Set.mem_Icc]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
theorem mem_cap {n U H : ℕ} {t : ℝ} :
    t ∈ cap n U H ↔ ∃ i ∈ centers U, t ∈ arc n H i := by
  constructor
  · rintro ⟨q,a,h₁,h₂,h₃,h₄,h₅⟩
    exact ⟨(q,a),Vcx.mpr ⟨h₁,h₂,h₃,h₄⟩,h₅⟩
  · rintro ⟨⟨q,a⟩,hi,ht⟩
    obtain ⟨h₁,h₂,h₃,h₄⟩ := Vcx.mp hi
    exact ⟨q,a,h₁,h₂,h₃,h₄,ht⟩
theorem Vpr (n U H : ℕ) : MeasurableSet (cap n U H) := by
  have h : cap n U H = ⋃ i ∈ centers U, arc n H i := by
    ext t
    rw [mem_cap]
    simp only [Set.mem_iUnion]
    constructor <;> rintro ⟨i,hi,ht⟩ <;> exact ⟨i,hi,ht⟩
  rw [h]
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => Vkk n H i
theorem V1zw {n R H : ℕ} (h : R ≤ H) (i : ℕ × ℕ) : arc n R i ⊆ arc n H i := by
  intro t ht
  change |t - center i| ≤ radius n R i.1 at ht
  change |t - center i| ≤ radius n H i.1
  exact ht.trans (div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity))
theorem Vtg {n U H : ℕ} (hbudget : 2 * H * U < n)
    {i j : ℕ × ℕ} (hi : i ∈ centers U) (hj : j ∈ centers U) {t : ℝ}
    (hti : t ∈ arc n H i) (htj : t ∈ arc n H j) : i = j := by
  obtain ⟨hi₁,hi₂,_,hi₄⟩ := Vcx.mp hi
  obtain ⟨hj₁,hj₂,_,hj₄⟩ := Vcx.mp hj
  obtain ⟨h₁,h₂⟩ := V1si.Vwx
    hbudget hi₁ hj₁ hi₂ hj₂ hi₄ hj₄ hti htj
  exact Prod.ext h₁ h₂
noncomputable def cell (n Q H : ℕ) (i : ℕ × ℕ) : Set ℝ :=
  (arc n H i \ (if i.1 ≤ Q then arc n Q i else ∅)) ∩ Set.Ioc 0 1
theorem V20h (n Q H : ℕ) (i : ℕ × ℕ) : MeasurableSet (cell n Q H i) := by
  unfold cell
  apply MeasurableSet.inter _ measurableSet_Ioc
  apply (Vkk n H i).diff
  split
  · exact Vkk n Q i
  · exact MeasurableSet.empty
theorem V1yk {n Q U H : ℕ} (hbudget : 2 * H * U < n) :
    (↑(centers U) : Set (ℕ × ℕ)).PairwiseDisjoint (cell n Q H) := by
  intro i hi j hj hij
  apply Set.disjoint_left.mpr
  intro t hti htj
  exact hij (Vtg hbudget hi hj hti.1.1 htj.1.1)
theorem V242 {n Q U H : ℕ} (hQ : Q ≤ U) (hH : Q ≤ H) (hbudget : 2 * H * U < n) :
    (⋃ i ∈ centers U, cell n Q H i) = (cap n U H \ cap n Q Q) ∩ Set.Ioc 0 1 := by
  ext t
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_sdiff]
  constructor
  · rintro ⟨i,hi,ht⟩
    refine ⟨⟨mem_cap.mpr ⟨i,hi,ht.1.1⟩,?_⟩, ht.2⟩
    intro hN
    obtain ⟨j,hj,htj⟩ := mem_cap.mp hN
    have he := Vtg hbudget hi (V1w1 hQ hj) ht.1.1 (V1zw hH j htj)
    subst j
    apply ht.1.2
    rw [ite_eq_left (Vcx.mp hj).2.1]
    exact htj
  · rintro ⟨⟨ht,hnot⟩,hunit⟩
    obtain ⟨i,hi,hti⟩ := mem_cap.mp ht
    refine ⟨i,hi,⟨⟨hti,?_⟩,hunit⟩⟩
    by_cases hic : i.1 ≤ Q
    · rw [ite_eq_left hic]
      intro hnarrow
      apply hnot
      obtain ⟨h₁,_,h₃,h₄⟩ := Vcx.mp hi
      exact mem_cap.mpr ⟨i,Vcx.mpr ⟨h₁,hic,h₃,h₄⟩,hnarrow⟩
    · simp [hic]
theorem V1ff {n Q U H : ℕ}
    (hQ : Q ≤ U) (hH : Q ≤ H) (hbudget : 2 * H * U < n) (F : ℝ → ℂ) (hF : Continuous F) :
    (∫ t in (0 : ℝ)..1, (cap n U H \ cap n Q Q).indicator F t) =
      ∑ i ∈ centers U, ∫ t in cell n Q H i, F t := by
  have hm := (Vpr n U H).diff (Vpr n Q Q)
  have hint : IntegrableOn F (Set.Ioc (0 : ℝ) 1) volume :=
    (hF.intervalIntegrable (0 : ℝ) 1).1
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), setIntegral_indicator hm,
    inter_comm, ← V242 hQ hH hbudget]
  exact integral_biUnion_finset (centers U) (fun i _ => V20h n Q H i)
    (V1yk hbudget) (fun i _ => hint.mono_set inter_subset_right)
end V19
end V19
section GoldbachGRHCenterSums
open scoped BigOperators
namespace V19
theorem V1mo (U : ℕ) {A : Type*} [AddCommMonoid A] (F : ℕ × ℕ → A) :
    (∑ i ∈ centers U, F i) =
      ∑ q ∈ Finset.Icc 1 U, ∑ a ∈ (Finset.range (q + 1)).filter (fun a => a.Coprime q),
        F (q, a) := by
  rw [centers, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun q hq => ?_
  change (∑ a ∈ Finset.range (U + 1), if a ≤ q ∧ a.Coprime q then F (q, a) else 0) = _
  rw [← Finset.sum_filter]
  have hqU := (Finset.mem_Icc.mp hq).2
  have hs : (Finset.range (U + 1)).filter (fun a => a ≤ q ∧ a.Coprime q) =
      (Finset.range (q + 1)).filter (fun a => a.Coprime q) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_, ha, hcop⟩
      exact ⟨Nat.lt_succ_of_le ha, hcop⟩
    · rintro ⟨ha, hcop⟩
      exact ⟨by omega, by omega, hcop⟩
  rw [hs]
theorem V1qo (q : ℕ) [NeZero q] {A : Type*} [AddCommMonoid A]
    (f : ZMod q → A) :
    (∑ a ∈ Finset.range q, f (a : ZMod q)) = ∑ a : ZMod q, f a := by
  apply Finset.sum_bij (fun (a : ℕ) _ => (a : ZMod q))
  · intro a _
    exact Finset.mem_univ _
  · intro a ha b hb hab
    simpa only [ZMod.val_natCast_of_lt (Finset.mem_range.mp ha),
      ZMod.val_natCast_of_lt (Finset.mem_range.mp hb)] using congrArg ZMod.val hab
  · intro a _
    exact ⟨a.val, Finset.mem_range.mpr a.val_lt, ZMod.natCast_zmod_val a⟩
  · intro a _
    rfl
theorem V1qp (q : ℕ) [NeZero q] (f : ZMod q → ℝ)
    (hf : ∀ a, 0 ≤ f a) :
    (∑ a ∈ (Finset.range (q + 1)).filter (fun a => a.Coprime q), f (a : ZMod q)) ≤
      2 * (∑ a : ZMod q, f a) := by
  calc
    _ ≤ ∑ a ∈ Finset.range (q + 1), f (a : ZMod q) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun a _ _ => hf a)
    _ = (∑ a ∈ Finset.range q, f (a : ZMod q)) + f (q : ZMod q) :=
      Finset.sum_range_succ _ _
    _ = (∑ a : ZMod q, f a) + f 0 := by
      rw [V1qo, ZMod.natCast_self]
    _ ≤ _ := by
      have hzero : f 0 ≤ ∑ a : ZMod q, f a :=
        Finset.single_le_sum (fun a _ => hf a) (Finset.mem_univ 0)
      linarith
end V19
end GoldbachGRHCenterSums
section V4g
open MeasureTheory
open Set hiding center
open scoped Interval
namespace V4g
open V19
private theorem V128 (n H q : ℕ) : 0 ≤ radius n H q := by
  unfold radius
  positivity
private theorem V1ec {E : Type*} [TopologicalSpace E]
    {G : ℝ → E} (hG : Continuous G) (c : ℝ) : Continuous (fun t => G (t - c)) :=
  hG.comp (continuous_id.sub continuous_const)
section Integral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem V1zx (n H : ℕ) (i : ℕ × ℕ) (G : ℝ → E) :
    (∫ t in arc n H i, G (t - center i)) =
      ∫ t in (-(radius n H i.1))..(radius n H i.1), G t := by
  have hr := V128 n H i.1
  rw [V1sc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith only [hr] :
      center i - radius n H i.1 ≤ center i + radius n H i.1),
    intervalIntegral.integral_comp_sub_right]
  congr 2 <;> ring
private theorem Vh8 (n H : ℕ) (i : ℕ × ℕ) (G : ℝ → E) :
    (∫ t in arc n H i ∩ Ioc 0 1, G (t - center i)) =
      ∫ t in arc n H i ∩ Icc 0 1, G (t - center i) := by
  apply setIntegral_congr_set
  have h : Ioc (0 : ℝ) 1 =ᵐ[volume] Icc (0 : ℝ) 1 := Ioc_ae_eq_Icc
  filter_upwards [h] with t ht
  simp only [mem_inter_iff, ht]
theorem Vaf (n H : ℕ) (i : ℕ × ℕ) (G : ℝ → E)
    (hleft : radius n H i.1 ≤ center i) (hright : center i + radius n H i.1 ≤ 1) :
    (∫ t in arc n H i ∩ Ioc 0 1, G (t - center i)) =
      ∫ t in (-(radius n H i.1))..(radius n H i.1), G t := by
  rw [Vh8, inter_eq_left.mpr, V1zx]
  rw [V1sc]
  exact Icc_subset_Icc (sub_nonneg.mpr hleft) hright
theorem Vv5 (n H : ℕ) (G : ℝ → E)
    (hr : radius n H 1 ≤ 1) :
    (∫ t in arc n H (1, 0) ∩ Ioc 0 1, G (t - center (1, 0))) =
      ∫ t in (0 : ℝ)..(radius n H 1), G t := by
  have hnonneg := V128 n H 1
  rw [Vh8, V1sc]
  simp only [show center (1, 0) = 0 by norm_num [center], zero_sub, zero_add, sub_zero]
  rw [Icc_inter_Icc, sup_eq_right.mpr (neg_nonpos.mpr hnonneg), inf_eq_left.mpr hr,
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hnonneg]
theorem Vyx (n H : ℕ) (G : ℝ → E)
    (hr : radius n H 1 ≤ 1) :
    (∫ t in arc n H (1, 1) ∩ Ioc 0 1, G (t - center (1, 1))) =
      ∫ t in (-(radius n H 1))..(0 : ℝ), G t := by
  have hnonneg := V128 n H 1
  rw [Vh8, V1sc]
  simp only [show center (1, 1) = 1 by norm_num [center] ]
  rw [Icc_inter_Icc, sup_eq_left.mpr (sub_nonneg.mpr hr),
    inf_eq_right.mpr (by linarith only [hnonneg] : (1 : ℝ) ≤ 1 + radius n H 1),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith only [hnonneg] :
      1 - radius n H 1 ≤ 1), intervalIntegral.integral_comp_sub_right]
  congr 2 <;> ring
theorem Vp5 {n Q H : ℕ} (hQH : Q ≤ H) (i : ℕ × ℕ)
    (G : ℝ → E) (hG : Continuous G) :
    (∫ t in cell n Q H i, G (t - center i)) =
      (∫ t in arc n H i ∩ Ioc 0 1, G (t - center i)) -
        if i.1 ≤ Q then (∫ t in arc n Q i ∩ Ioc 0 1, G (t - center i)) else 0 := by
  by_cases hq : i.1 ≤ Q
  · simp only [cell, ite_eq_left hq]
    rw [show (arc n H i \ arc n Q i) ∩ Ioc (0 : ℝ) 1 =
        (arc n H i ∩ Ioc 0 1) \ (arc n Q i ∩ Ioc 0 1) by
      ext t
      simp only [mem_inter_iff, mem_sdiff]
      tauto]
    apply setIntegral_sdiff ((Vkk n Q i).inter measurableSet_Ioc)
    · exact ((V1ec hG (center i)).intervalIntegrable 0 1).1.mono_set inter_subset_right
    · exact inter_subset_inter_left _ (V1zw hQH i)
  · simp [cell, hq]
end Integral
theorem V23k (n Q H : ℕ) (i : ℕ × ℕ) (G : ℝ → ℝ) (hG : Continuous G)
    (hG0 : ∀ t, 0 ≤ G t) :
    (∫ t in cell n Q H i, G (t - center i)) ≤
      ∫ t in (-(radius n H i.1))..(radius n H i.1), G t := by
  rw [← V1zx]
  apply setIntegral_mono_set
  · rw [V1sc, integrableOn_Icc_iff_integrableOn_Ioc]
    exact ((V1ec hG (center i)).intervalIntegrable _ _).1
  · exact Filter.Eventually.of_forall fun t => hG0 (t - center i)
  · exact (show cell n Q H i ⊆ arc n H i from fun _ ht => ht.1.1).eventuallySubset
theorem Vnj {n H q a : ℕ} (hH : H ≤ n) (hq : 2 ≤ q) (ha : a ≤ q)
    (hcop : Nat.Coprime a q) :
    radius n H q ≤ center (q, a) ∧ center (q, a) + radius n H q ≤ 1 := by
  have ha0 : 1 ≤ a := by
    by_contra! hn
    have ha' : a = 0 := by omega
    subst a
    have h := (Nat.coprime_zero_left q).mp hcop
    omega
  have haq : a + 1 ≤ q := by
    by_contra! hn
    have ha' : a = q := by omega
    subst a
    have h : q = 1 := by simpa [Nat.Coprime] using hcop
    omega
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hr : radius n H q ≤ 1 / (q : ℝ) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [radius]
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hHn : (H : ℝ) ≤ (n : ℝ) := by exact_mod_cast hH
    unfold radius
    apply (div_le_iff₀ (mul_pos hqR hnR)).mpr
    rw [← mul_assoc, one_div_mul_cancel hqR.ne', one_mul]
    exact hHn
  refine ⟨hr.trans ?_, (add_le_add_right hr (center (q, a))).trans ?_⟩
  · unfold center
    exact div_le_div_of_nonneg_right (by exact_mod_cast ha0) hqR.le
  · unfold center
    rw [← add_div]
    apply (div_le_iff₀ hqR).mpr
    simpa only [one_mul, Nat.cast_add, Nat.cast_one] using (show ((a + 1 : ℕ) : ℝ) ≤ q by
      exact_mod_cast haq)
theorem V1gw {n H : ℕ} (hH : H ≤ n) : radius n H 1 ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [radius]
  · simpa [radius] using (div_le_one (by exact_mod_cast hn : (0:ℝ) < n)).mpr
      (show (H : ℝ) ≤ n by exact_mod_cast hH)
theorem V1s8 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n Q H q a : ℕ} (hQH : Q ≤ H) (hHn : H ≤ n) (hq : 2 ≤ q) (ha : a ≤ q)
    (hcop : Nat.Coprime a q) (G : ℝ → E) (hG : Continuous G) :
    (∫ t in cell n Q H (q, a), G (t - center (q, a))) =
      (∫ t in (-(radius n H q))..(radius n H q), G t) -
        if q ≤ Q then (∫ t in (-(radius n Q q))..(radius n Q q), G t) else 0 := by
  obtain ⟨hHl, hHr⟩ := Vnj hHn hq ha hcop
  obtain ⟨hQl, hQr⟩ := Vnj (hQH.trans hHn) hq ha hcop
  rw [Vp5 hQH (q, a) G hG,
    Vaf n H (q, a) G hHl hHr,
    Vaf n Q (q, a) G hQl hQr]
theorem V1qg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n Q H : ℕ} (hQH : Q ≤ H) (hHn : H ≤ n) (G : ℝ → E) (hG : Continuous G) :
    (∫ t in cell n Q H (1, 0), G (t - center (1, 0))) +
      (∫ t in cell n Q H (1, 1), G (t - center (1, 1))) =
      (∫ t in (-(radius n H 1))..(radius n H 1), G t) -
        if 1 ≤ Q then (∫ t in (-(radius n Q 1))..(radius n Q 1), G t) else 0 := by
  have hQn := hQH.trans hHn
  have hfull (R : ℕ) :
      (∫ t in (0 : ℝ)..(radius n R 1), G t) +
        (∫ t in (-(radius n R 1))..(0 : ℝ), G t) =
          ∫ t in (-(radius n R 1))..(radius n R 1), G t := by
    rw [add_comm]
    exact intervalIntegral.integral_add_adjacent_intervals (hG.intervalIntegrable _ _)
      (hG.intervalIntegrable _ _)
  simp only [Vp5 hQH _ G hG,
    Vv5 n H G (V1gw hHn),
    Vv5 n Q G (V1gw hQn),
    Vyx n H G (V1gw hHn),
    Vyx n Q G (V1gw hQn)]
  by_cases h : 1 ≤ Q
  · simp only [ite_eq_left h]
    rw [← hfull H, ← hfull Q]
    abel
  · simpa only [ite_eq_right h, sub_zero] using hfull H
theorem V1ei {n Q H q a : ℕ} (hQH : Q ≤ H) (hHn : H ≤ n)
    (hq : 2 ≤ q) (ha : a ≤ q) (hcop : Nat.Coprime a q) :
    (∫ t in cell n Q H (q, a), ‖V24.kernel n (t - center (q, a))‖ ^ 2) =
      V24.mass n (radius n H q) -
        if q ≤ Q then V24.mass n (radius n Q q) else 0 :=
  V1s8 hQH hHn hq ha hcop _
    ((V24.Vhc n).norm.pow 2)
theorem V198 {n Q H : ℕ} (hQH : Q ≤ H) (hHn : H ≤ n) :
    (∫ t in cell n Q H (1, 0), ‖V24.kernel n (t - center (1, 0))‖ ^ 2) +
      (∫ t in cell n Q H (1, 1), ‖V24.kernel n (t - center (1, 1))‖ ^ 2) =
      V24.mass n (radius n H 1) -
        if 1 ≤ Q then V24.mass n (radius n Q 1) else 0 :=
  V1qg hQH hHn _ ((V24.Vhc n).norm.pow 2)
end V4g
end V4g
section GoldbachGRHModelDef
namespace Va2
noncomputable def model (n : ℕ) (i : ℕ × ℕ) (t : ℝ) : ℂ :=
  ((ArithmeticFunction.moebius i.1 : ℂ) / (i.1.totient : ℂ)) *
    V24.kernel n (t - V19.center i)
theorem Ve5 (n : ℕ) (i : ℕ × ℕ) : Continuous (model n i) :=
  continuous_const.mul ((V24.Vhc n).comp
    (continuous_id.sub continuous_const))
end Va2
end GoldbachGRHModelDef
section V4o
open Finset MeasureTheory
open scoped ComplexConjugate
namespace V4o
open V19 (cell centers center radius)
open V24 (kernel mass)
open V31 (phase V13v)
open Va2 (model)
open Vr (V3f ram V127)
noncomputable def Vba (n Q H q : ℕ) : ℝ :=
  mass n (radius n H q) - if q ≤ Q then mass n (radius n Q q) else 0
noncomputable def Vc5 (n q a : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) ^ 2 *
    phase (-(n : ℝ) * center (q, a))
private theorem V22p (x : ℝ) : phase (-x) = conj (phase x) := by
  symm
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring
private theorem V1yp (n : ℕ) : Vc5 n 1 0 = 1 := by
  simp [Vc5, center, phase]
private theorem V1zf (n : ℕ) : Vc5 n 1 1 = 1 := by
  simp [Vc5, center, V22p, V24.V22q]
theorem V1u8 (n q a : ℕ) (t : ℝ) :
    model n (q, a) t ^ 2 * phase (-(n : ℝ) * t) =
      Vc5 n q a * (↑(‖kernel n (t - center (q, a))‖ ^ 2) : ℂ) := by
  have hphase : -(n : ℝ) * t =
      -(n : ℝ) * center (q, a) + -(n : ℝ) * (t - center (q, a)) := by ring
  rw [← V24.reflect n (t - center (q, a)), model, hphase, V13v]
  unfold Vc5
  ring
theorem V1he (n Q H q a : ℕ) :
    (∫ t in cell n Q H (q, a), model n (q, a) t ^ 2 * phase (-(n : ℝ) * t)) =
      Vc5 n q a *
        (↑(∫ t in cell n Q H (q, a), ‖kernel n (t - center (q, a))‖ ^ 2) : ℂ) := by
  simp_rw [V1u8]
  rw [MeasureTheory.integral_const_mul, integral_complex_ofReal]
theorem V1bq (n q : ℕ) :
    (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), Vc5 n q a) =
      V3f q n := by
  rw [V3f, V127, ram, map_sum, Finset.mul_sum]
  refine sum_congr rfl fun a _ => ?_
  unfold Vc5
  congr 1
  have h : -(n : ℝ) * center (q, a) = -((n : ℝ) * a / q) := by
    simp only [center, ← mul_div_assoc, neg_mul, neg_div]
  rw [h, V22p]
  rfl
theorem V20t {n Q H U : ℕ} (_hU : 1 ≤ U) (hQH : Q ≤ H) (hHn : H ≤ n) :
    (∑ i ∈ centers U, ∫ t in cell n Q H i, model n i t ^ 2 * phase (-(n : ℝ) * t)) =
      ∑ q ∈ Icc 1 U, V3f q n * (Vba n Q H q : ℂ) := by
  classical
  rw [V19.V1mo]
  refine sum_congr rfl fun q hq => ?_
  have hq1 := (mem_Icc.mp hq).1
  by_cases hqOne : q = 1
  · subst q
    have hf : ((range (1 + 1)).filter (fun a : ℕ => Nat.Coprime a 1)) =
        ({0, 1} : Finset ℕ) := by
      ext a
      simp only [mem_filter, mem_range, Nat.coprime_one_right_iff, and_true,
        mem_insert, mem_singleton]
      omega
    rw [hf, sum_pair (by decide : (0 : ℕ) ≠ 1)]
    simp only [V1he, V1yp, V1zf, one_mul,
      ← Complex.ofReal_add, V4g.V198 hQH hHn,
      Vr.V13x, Vba]
  · have hq2 : 2 ≤ q := by omega
    have hf : ((range (q + 1)).filter (fun a => Nat.Coprime a q)) =
        (range q).filter (fun a => Nat.Coprime a q) := by
      ext a
      simp only [mem_filter, mem_range]
      constructor
      · rintro ⟨haq, hcop⟩
        have hne : a ≠ q := by
          intro heq
          subst a
          have h : q = 1 := by simpa [Nat.Coprime] using hcop
          exact hqOne h
        exact ⟨lt_of_le_of_ne (Nat.lt_succ_iff.mp haq) hne, hcop⟩
      · rintro ⟨haq, hcop⟩
        exact ⟨haq.trans (Nat.lt_succ_self q), hcop⟩
    rw [hf, ← V1bq, Finset.sum_mul]
    refine sum_congr rfl fun a ha => ?_
    obtain ⟨haq, hcop⟩ := mem_filter.mp ha
    rw [V1he, V4g.V1ei hQH hHn hq2
      (mem_range.mp haq).le hcop, Vba]
theorem V1yo {n Q H U : ℕ} (hU : 1 ≤ U) (hQH : Q ≤ H) (hHn : H ≤ n) :
    (∑ i ∈ centers U, ∫ t in cell n Q H i, model n i t ^ 2 * phase (-(n : ℝ) * t)).re =
      ∑ q ∈ Icc 1 U, (V3f q n).re * Vba n Q H q := by
  rw [V20t hU hQH hHn, Complex.re_sum]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
end V4o
end V4o
section Vf0
open Finset
open scoped Interval Classical
namespace Vf0
open V31 (phase V13v Vi3 Vb2)
open Vcr (poly moving)
open V54 (V8a V76)
open V24 (kernel)
noncomputable def Vll {q : ℕ} [NeZero q] (a : ZMod q) (k : ℕ) : ℂ :=
  V76 k * ZMod.stdAddChar (a * (k : ZMod q)) - V8a q a
theorem V1bv {q : ℕ} [NeZero q] (n a : ℕ) (β : ℝ) :
    poly (n+1) (Vll (a : ZMod q)) β =
      Vi3 n ((a : ℝ) / (q:ℝ) + β) -
        V8a q (a : ZMod q) * kernel n β := by
  unfold kernel poly Vll Vi3
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [sub_mul, one_mul, V54.V1gr]
  change (Vb2 k : ℂ) * phase ((a:ℝ)*(k:ℝ)/(q:ℝ)) * phase ((k:ℝ)*β) -
    V8a q (a : ZMod q) * phase ((k:ℝ)*β) =
      (Vb2 k : ℂ) * phase ((k:ℝ)*((a:ℝ)/(q:ℝ)+β)) -
        V8a q (a : ZMod q) * phase ((k:ℝ)*β)
  rw [mul_assoc, ← V13v]
  congr 3
  ring
end Vf0
end Vf0
section V20
open Filter Finset
open scoped Topology
namespace V20
def narrow (n : ℕ) : ℕ := (Nat.log 2 (n+2))^2
noncomputable def cutoff (n : ℕ) : ℕ := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
noncomputable def width (n : ℕ) : ℕ := 256 * cutoff n * narrow n
private theorem V1wx (n : ℕ) (hn : 2 ≤ n) : (Nat.log 2 (n+2) : ℝ) ≤ 4 * Real.log (n:ℝ) := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hnon : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by linarith)
  have hpow : (2:ℝ)^(Nat.log 2 (n+2)) ≤ ((n+2 : ℕ):ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n+2 ≠ 0)
  have hraw := Real.log_le_log (by positivity) hpow
  have hin : ((n+2 : ℕ) : ℝ) ≤ (n:ℝ)^2 := by
    push_cast
    nlinarith only [hnR, sq_nonneg ((n:ℝ)-2)]
  have hlog := Real.log_le_log (by positivity) hin
  rw [Real.log_pow] at hraw hlog
  have hl2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg (Nat.log 2 (n+2)) : 0≤(_ : ℝ))
  push_cast at hlog hraw
  linarith only [hm, hraw, hlog]
theorem V90 (k : ℕ) (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, (Real.log (n:ℝ))^k ≤ c * (n:ℝ)^a := by
  have h := (isLittleO_log_rpow_rpow_atTop (s:=a) k ha).def hc
  filter_upwards [h.natCast_atTop] with n hn
  simpa only [Real.rpow_natCast, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) a)]
    using (le_abs_self ((Real.log (n:ℝ))^(k:ℝ))).trans hn
theorem Vhd :
    ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ 1 ≤ narrow n ∧ narrow n ≤ cutoff n ∧ cutoff n ≤ n ∧
      24 * width n ≤ n ∧ 2 * width n * cutoff n < n := by
  obtain ⟨N,hN⟩ := Vpg.V1pz
  have hroot : ∀ᶠ n : ℕ in atTop, (3:ℝ) ≤ (n:ℝ)^(1/3:ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/3)).comp
      (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually (eventually_ge_atTop (3:ℝ))
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop (2:ℕ), hroot,
    V90 2 (1/3) (1/32) (by norm_num) (by norm_num)] with n hnN hn h3 hlog
  obtain ⟨hU,hH,hNn⟩ := hN n hnN
  change 2 * width n * (4 * cutoff n) < n at hU
  have hQ₀ : 1 ≤ narrow n := by
    unfold narrow
    exact Nat.pow_pos (Nat.log_pos (by decide) (by omega))
  have hQ : narrow n ≤ cutoff n := by
    apply Nat.le_floor
    calc
      (narrow n : ℝ) ≤ (4 * Real.log (n:ℝ))^2 := by
        unfold narrow
        push_cast
        exact pow_le_pow_left₀ (by positivity) (V1wx n hn) _
      _ = 16 * Real.log (n:ℝ)^2 := by ring
      _ ≤ (n:ℝ)^(1/3:ℝ) := by
        have ht := mul_le_mul_of_nonneg_left hlog (show (0:ℝ)≤16 by norm_num)
        nlinarith only [ht, Real.rpow_nonneg (Nat.cast_nonneg n) (1/3:ℝ)]
  have hU3 : 3 ≤ cutoff n := Nat.le_floor (by exact h3)
  have hW : 24 * width n ≤ n := by
    have ht := Nat.mul_le_mul_left (2*width n) (show 12 ≤ 4*cutoff n by omega)
    omega
  have hBudget : 2 * width n * cutoff n < n := by
    have ht := Nat.mul_le_mul_left (2*width n) (show cutoff n ≤ 4*cutoff n by omega)
    exact ht.trans_lt hU
  exact ⟨hn,hQ₀,hQ,(by change 4 * cutoff n ≤ n at hNn; omega),hW,hBudget⟩
theorem Vrx (n : ℕ) (h : 1 ≤ narrow n) : cutoff n ≤ width n := by
  unfold width
  have hh := Nat.mul_le_mul_left (256 * cutoff n) h
  omega
theorem V233 (U : ℕ) : (∑ q ∈ Icc 1 U, 1 / (q : ℝ)) ≤ 1 + Real.log U := by
  have hh := harmonic_le_one_add_log U
  apply le_trans _ hh
  unfold harmonic
  rw [Rat.cast_sum]
  have he : Icc 1 U = (range U).map ⟨Nat.succ, Nat.succ_injective⟩ := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_map, Function.Embedding.coeFn_mk, Finset.mem_range]
    constructor
    · rintro ⟨hj,hU⟩
      exact ⟨j-1,by omega,by omega⟩
    · rintro ⟨k,hk,rfl⟩
      omega
  rw [he, Finset.sum_map]
  simp [one_div, Nat.succ_eq_add_one, Nat.cast_add]
theorem V1rw (C : ℝ) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, C * (width n : ℝ)^2 * (Real.log (n:ℝ))^5 ≤ (n:ℝ)^(5/6:ℝ) := by
  have hC' : 0 < 1 / (C * (4096:ℝ)^2) := by positivity
  filter_upwards [eventually_ge_atTop (2:ℕ), V90 9 (1/6)
    (1/(C*(4096:ℝ)^2)) (by norm_num) hC'] with n hn hlog
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  let x := (n:ℝ)^(1/3:ℝ)
  have hU : (cutoff n:ℝ) ≤ x := Nat.floor_le (Real.rpow_nonneg hnR.le _)
  have hN : (narrow n:ℝ) ≤ (4*Real.log (n:ℝ))^2 := by
    unfold narrow
    push_cast
    exact pow_le_pow_left₀ (by positivity) (V1wx n hn) _
  have hw : (width n:ℝ) ≤ 4096 * x * (Real.log (n:ℝ))^2 := by
    unfold width
    push_cast
    calc
      _ ≤ 256 * x * (4*Real.log (n:ℝ))^2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hU (by norm_num)) hN (by positivity) (by positivity)
      _ = _ := by ring
  have hlog₀ : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤n by omega))
  have hx : x^2 = (n:ℝ)^(2/3:ℝ) := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
    norm_num
  calc
    _ ≤ C * (4096*x*(Real.log (n:ℝ))^2)^2*(Real.log (n:ℝ))^5 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hw _) hC.le)
        (pow_nonneg hlog₀ _)
    _ = x^2*(C*4096^2*(Real.log (n:ℝ))^9) := by ring
    _ ≤ x^2*(n:ℝ)^(1/6:ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have ht := mul_le_mul_of_nonneg_left hlog (show 0≤C*(4096:ℝ)^2 by positivity)
      convert ht using 1
      field_simp
    _ = _ := by rw [hx, ← Real.rpow_add hnR]; norm_num
end V20
end V20
section Vi0
open Filter Asymptotics
open scoped Topology
namespace Vi0
theorem V1py (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      let η := (n : ℝ) ^ (-1 / 12 : ℝ)
      0 < η ∧ (1 + 1 / η) * (n : ℝ) ^ (5 / 6 : ℝ) +
        η * ((n : ℝ) + 1) * (Real.log (n : ℝ)) ^ 2 ≤ ε * (n : ℝ) := by
  have hlogLimit : Tendsto (fun n : ℕ => Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ (1 / 24 : ℝ))
      atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop ((2 : ℕ) : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 24)).tendsto_div_nhds_zero
    simpa only [Function.comp_def, Real.rpow_natCast] using
      h.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpowerLimit : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 24 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 24)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop 1, hlogLimit.eventually_lt_const zero_lt_one,
    (tendsto_atTop.1 hpowerLimit) (4 / ε)] with n hn hlog hlarge
  let x : ℝ := n
  let η := x ^ (-1 / 12 : ℝ)
  change 0 < η ∧ (1 + 1 / η) * x ^ (5 / 6 : ℝ) + η * (x + 1) * (Real.log x) ^ 2 ≤ ε * x
  have hx1 : 1 ≤ x := by
    change (1 : ℝ) ≤ (n : ℝ)
    exact_mod_cast hn
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hη : 0 < η := Real.rpow_pos_of_pos hx _
  have hlog' : Real.log x ^ 2 ≤ x ^ (1 / 24 : ℝ) := by
    change Real.log x ^ 2 / x ^ (1 / 24 : ℝ) < 1 at hlog
    simpa using (div_le_iff₀ (Real.rpow_pos_of_pos hx (1 / 24 : ℝ))).mp hlog.le
  have hinv : 1 / η = x ^ (1 / 12 : ℝ) := by
    dsimp [η]
    rw [show (-1 / 12 : ℝ) = -(1 / 12 : ℝ) by norm_num, Real.rpow_neg hx.le, one_div, inv_inv]
  have hfirst : (1 + 1 / η) * x ^ (5 / 6 : ℝ) ≤ 2 * x ^ (23 / 24 : ℝ) := by
    calc
      _ = x ^ (5 / 6 : ℝ) + x ^ (11 / 12 : ℝ) := by
        rw [hinv, add_mul, one_mul, ← Real.rpow_add hx]
        norm_num
      _ ≤ 2 * x ^ (23 / 24 : ℝ) := by
        have ha := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (5 / 6 : ℝ) ≤ 23 / 24)
        have hb := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (11 / 12 : ℝ) ≤ 23 / 24)
        linarith
  have hsecond : η * (x + 1) * (Real.log x) ^ 2 ≤ 2 * x ^ (23 / 24 : ℝ) := by
    have hsize : x + 1 ≤ 2 * x := by linarith
    calc
      _ ≤ η * (2 * x) * x ^ (1 / 24 : ℝ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsize hη.le) hlog' (sq_nonneg _) (by positivity)
      _ = 2 * (η * x ^ (1 : ℝ) * x ^ (1 / 24 : ℝ)) := by rw [Real.rpow_one]; ring
      _ = _ := by
        dsimp [η]
        rw [← Real.rpow_add hx, ← Real.rpow_add hx]
        norm_num
  refine ⟨hη, ?_⟩
  have hlarge' : 4 ≤ ε * x ^ (1 / 24 : ℝ) := by
    change 4 / ε ≤ x ^ (1 / 24 : ℝ) at hlarge
    simpa only [mul_comm] using (div_le_iff₀ hε).mp hlarge
  calc
    _ ≤ 4 * x ^ (23 / 24 : ℝ) := by linarith
    _ ≤ (ε * x ^ (1 / 24 : ℝ)) * x ^ (23 / 24 : ℝ) :=
      mul_le_mul_of_nonneg_right hlarge' (Real.rpow_nonneg hx.le _)
    _ = ε * x := by rw [mul_assoc, ← Real.rpow_add hx]; norm_num
end Vi0
end Vi0
section V1s
open Filter
open scoped Topology BigOperators ComplexConjugate
namespace V1s
open Finset
theorem V18p (f : ℕ → ℝ) (ε : ℝ) (hε : 0 ≤ ε) :
    ∀ (m A : ℕ) (w : ℕ → ℝ), Monotone w → (∀ q ≥ A, 0 ≤ w q) →
      (∀ k, A ≤ k → k ≤ A+m → -ε ≤ ∑ q ∈ Ioc k (A+m), f q) →
      -(ε * w (A+m)) ≤ ∑ q ∈ Ioc A (A+m), f q * w q := by
  intro m
  induction m with
  | zero =>
    intro A w _ hw _
    simpa using neg_nonpos.mpr (mul_nonneg hε (hw A le_rfl))
  | succ m ih =>
    intro A w hw hw₀ hfloor
    let B := A + (m+1)
    let v : ℕ → ℝ := fun q => w q-w (A+1)
    have hB : A+1+m=B := by dsimp [B]; omega
    have hv : Monotone v := by
      intro i j hij
      exact sub_le_sub_right (hw hij) _
    have hv₀ (q : ℕ) (hq : A+1 ≤ q) : 0 ≤ v q := sub_nonneg.mpr (hw hq)
    have hsub : -(ε * v B) ≤ ∑ q ∈ Ioc (A+1) B, f q * v q := by
      rw [← hB]
      apply ih (A+1) v hv hv₀
      intro k hk hkB
      simpa only [hB] using hfloor k (by omega) (show k ≤ B from hB ▸ hkB)
    have hs : Ioc A B = insert (A+1) (Ioc (A+1) B) := by
      ext k
      have hAB : A+1 ≤ B := by dsimp [B]; omega
      simp only [mem_Ioc, mem_insert]
      omega
    have hnin : A+1 ∉ Ioc (A+1) B := by simp
    have hsum :
        (∑ q ∈ Ioc A B, f q * w q) =
          w (A+1) * (∑ q ∈ Ioc A B, f q) +
            ∑ q ∈ Ioc (A+1) B, f q * v q := by
      rw [hs]
      simp only [sum_insert hnin, v, mul_sub, sum_sub_distrib, ← sum_mul]
      ring
    have hf := hfloor A le_rfl (by omega)
    have hfirst : -(ε * w (A+1)) ≤ w (A+1) * (∑ q ∈ Ioc A B, f q) := by
      simpa [B, mul_comm] using mul_le_mul_of_nonneg_left hf (hw₀ (A+1) (by omega))
    change -(ε * w B) ≤ ∑ q ∈ Ioc A B, f q * w q
    rw [hsum]
    dsimp [v] at hsub
    calc
      _ = -(ε*w (A+1)) + -(ε*(w B-w (A+1))) := by ring
      _ ≤ _ := add_le_add hfirst hsub
end V1s
namespace V1s
open Finset Filter ArithmeticFunction
open scoped Topology ArithmeticFunction.zeta
private theorem V1l0 (X : ℕ) :
    (∑ j ∈ Icc 2 X, ((j : ℝ)^2)⁻¹) ≤ 3/4 := by
  by_cases hX : 2 ≤ X
  · rw [← sum_Ioc_add_eq_sum_Icc hX]
    have hh := sum_Ioc_inv_sq_le_sub (α := ℝ) (by decide : (2 : ℕ) ≠ 0) hX
    norm_num at hh ⊢
    linarith [show 0 ≤ ((X : ℝ))⁻¹ by positivity]
  · norm_num [Icc_eq_empty_of_lt (lt_of_not_ge hX)]
private theorem V1xu {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1) :
    1 - (∑ i ∈ s, f i) ≤ ∏ i ∈ s, (1-f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have haF := hf a (mem_insert_self _ _)
    have hs : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1 := fun i hi => hf i (mem_insert_of_mem hi)
    rw [sum_insert ha, prod_insert ha]
    have hsum : 0 ≤ ∑ i ∈ s, f i := sum_nonneg fun i hi => (hs i hi).1
    have hh := mul_le_mul_of_nonneg_left (ih hs) (sub_nonneg.mpr haF.2)
    nlinarith only [hh, mul_nonneg haF.1 hsum]
private noncomputable def Vfx (n p : ℕ) : ℝ :=
  if p ∣ n then 0 else (((p : ℝ)-1)^2)⁻¹
private theorem V1kp {n p : ℕ} (hn : Even n) (hp : p.Prime)
    (hpn : ¬ p ∣ n) : 3 ≤ p := by
  have hp2 := hp.two_le
  by_contra! hh
  have hp₂ : p = 2 := by omega
  apply hpn
  rw [hp₂]
  obtain ⟨k, hk⟩ := hn
  exact ⟨k, by omega⟩
private theorem V196 {n p : ℕ} (hn : Even n) (hp : p.Prime) :
    0 ≤ Vfx n p ∧ Vfx n p ≤ 1 := by
  unfold Vfx
  by_cases hpN : p ∣ n
  · simp [hpN]
  · have h3 : (3 : ℝ) ≤ p := by exact_mod_cast V1kp hn hp hpN
    rw [ite_eq_right hpN]
    exact ⟨by positivity, inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg ((p:ℝ)-2)])⟩
private theorem V1rb (n p k : ℕ) (hp : p.Prime) :
    1 - Vfx n p ≤ ∑ d ∈ (p^k).divisors, Vm.z n d := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  rw [Nat.sum_divisors_prime_pow hp,
    Vm.V1y7 (fun j => Vm.z n (p^j))
      (fun j => by simp [Vm.z,Vm.h_cube n p j hp])]
  simp only [pow_zero,pow_one,(Vm.z_mult n).map_one]
  simp only [Vfx,Vm.z,ArithmeticFunction.coe_mk,
    Vm.h_prime n p hp,Vm.V22c n p hp,Nat.cast_pow]
  by_cases hpn : p ∣ n
  · simp only [hpn, ite_true, sub_zero]
    have hpos : 0 ≤ (1 / ((p : ℝ)-1)) / (p : ℝ) := by positivity
    have hcancel : (1 / ((p : ℝ)-1)) / (p : ℝ) +
        (-(p : ℝ) / ((p : ℝ)-1)) / (p : ℝ)^2 = 0 := by
      field_simp; ring
    split_ifs <;> first | omega | linarith only [hpos,hcancel]
  · simp only [hpn, ite_false, zero_div, ite_self, add_zero]
    have hneg : (-(p : ℝ) / ((p : ℝ)-1)^2) / (p : ℝ) = -(((p : ℝ)-1)^2)⁻¹ := by
      field_simp
    rw [hneg]
    split_ifs <;> linarith [show 0 ≤ (((p : ℝ)-1)^2)⁻¹ by positivity]
theorem V1pb (n M : ℕ) (hn : Even n) (hM : 0 < M) :
    (1/4 : ℝ) ≤ ∑ d ∈ M.divisors, Vm.z n d := by
  classical
  let s := M.factorization.support
  let P := s.filter (fun p => ¬ p ∣ n)
  have hprime (p : ℕ) (hp : p ∈ s) : p.Prime :=
    Nat.prime_of_mem_primeFactors (M.support_factorization ▸
      (show p ∈ M.factorization.support from hp))
  have hle (p : ℕ) (hp : p ∈ s) : p ≤ M :=
    Nat.le_of_dvd hM (Nat.dvd_of_mem_primeFactors (M.support_factorization ▸
      (show p ∈ M.factorization.support from hp)))
  have hM' (p : ℕ) (hp : p ∈ P) : 3 ≤ p :=
    V1kp hn (hprime p (mem_filter.mp hp).1) (mem_filter.mp hp).2
  have hinj : Set.InjOn (fun p : ℕ => p-1) (↑P : Set ℕ) := by
    intro p hp q hq he
    have h1 := hM' p hp
    have h2 := hM' q hq
    change p - 1 = q - 1 at he
    omega
  have himage : P.image (fun p => p-1) ⊆ Icc 2 M := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hj
    have h1 := hM' p hp
    have h2 := hle p (mem_filter.mp hp).1
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hsum : (∑ p ∈ s, Vfx n p) ≤ 3/4 := by
    calc
      _ = ∑ p ∈ P, (((p : ℝ)-1)^2)⁻¹ := by
        rw [sum_filter]
        apply sum_congr rfl
        intro p hp
        by_cases hpN : p ∣ n <;> simp [Vfx,hpN]
      _ = ∑ p ∈ P, ((((p-1 : ℕ) : ℝ)^2))⁻¹ := by
        apply sum_congr rfl
        intro p hp
        rw [Nat.cast_sub (by have := hM' p hp; omega)]
        norm_cast
      _ = ∑ j ∈ P.image (fun p : ℕ => p-1), ((j : ℝ)^2)⁻¹ := by rw [sum_image hinj]
      _ ≤ ∑ j ∈ Icc 2 M, ((j : ℝ)^2)⁻¹ :=
        sum_le_sum_of_subset_of_nonneg himage (fun _ _ _ => by positivity)
      _ ≤ _ := V1l0 M
  let A : ArithmeticFunction ℝ := Vm.z n * (ζ : ArithmeticFunction ℝ)
  have hA : IsMultiplicative A := (Vm.z_mult n).mul isMultiplicative_zeta.natCast
  have he (m : ℕ) : A m = ∑ d ∈ m.divisors,Vm.z n d := coe_mul_zeta_apply
  have hprod := hA.multiplicative_factorization A hM.ne'
  rw [he] at hprod
  rw [hprod,Finsupp.prod]
  change _ ≤ ∏ p ∈ s, A (p^M.factorization p)
  calc
    _ ≤ 1 - ∑ p ∈ s, Vfx n p := by linarith
    _ ≤ ∏ p ∈ s, (1 - Vfx n p) :=
      V1xu s _ (fun p hp => V196 hn (hprime p hp))
    _ ≤ _ := by
      apply prod_le_prod₀
      · exact fun p hp => sub_nonneg.mpr (V196 hn (hprime p hp)).2
      · intro p hp
        rw [he]
        exact V1rb n p _ (hprime p hp)
theorem V1od :
    ∀ᶠ J : ℕ in atTop, 0 < J ∧ ∀ n : ℕ, Even n →
      (1/8 : ℝ) ≤ ∑ d ∈ Icc 1 J, Vm.z n d := by
  have ht := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/4)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop (1 : ℕ), ht.eventually_ge_atTop (8 * Vm.V2i)]
    with J hJ hlarge
  refine ⟨hJ, ?_⟩
  intro n hn
  have hJ' : 0 < J := hJ
  have hu := Vm.V1bh n J (J.factorial.divisors \ Icc 1 J) hJ' (by
    intro d hd
    obtain ⟨hd, hd'⟩ := mem_sdiff.mp hd
    have hpos := Nat.pos_of_mem_divisors hd
    simp only [mem_Icc, not_and] at hd'
    omega)
  have hh := V1pb n J.factorial hn J.factorial_pos
  rw [← sum_sdiff (s₁ := Icc 1 J) (s₂ := J.factorial.divisors) (Vm.V20y J)] at hh
  have ht := sum_le_sum (s := J.factorial.divisors \ Icc 1 J) (fun d _ => le_abs_self (Vm.z n d))
  have hsmall : Vm.V2i / (J : ℝ)^(1/4 : ℝ) ≤ 1/8 := by
    apply (div_le_iff₀ (by positivity)).mpr
    change 8 * Vm.V2i ≤ (J : ℝ)^(1/4 : ℝ) at hlarge
    linarith
  linarith
end V1s
namespace V1s
open Finset Filter ArithmeticFunction
open scoped Topology
noncomputable def V3w (n X : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 X, Vm.g n k / (k : ℝ)
noncomputable def V1za (n X : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 X, Vm.F n q / (q : ℝ)
theorem Vg7 (n k : ℕ) : 0 ≤ Vm.g n k ∧ Vm.g n k ≤ 1 := by
  simp [Vm.g]
  split_ifs <;> norm_num
private theorem V1h8 (n : ℕ) {A B : ℕ} (hAB : A ≤ B) :
    V3w n B - V3w n A =
      ∑ k ∈ Ioc A B, Vm.g n k / (k : ℝ) := by
  have h := Vm.Vki (fun k => Vm.g n k / (k : ℝ)) hAB
  unfold V3w
  linarith
theorem Vxj (n : ℕ) : Monotone (V3w n) := by
  intro A B hAB
  have h := V1h8 n hAB
  have hn : 0 ≤ ∑ k ∈ Ioc A B, Vm.g n k / (k : ℝ) :=
    sum_nonneg fun k _ => div_nonneg (Vg7 n k).1 (Nat.cast_nonneg _)
  linarith
theorem V1lm (n X d : ℕ) (hX : 0 < X) (hd : 0 < d) :
    V3w n X - V3w n (X/d) ≤ (d : ℝ) * Vm.gAvg n X := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hsub : Ioc (X/d) X ⊆ Icc 1 X := by
    intro k hk
    exact mem_Icc.mpr ⟨Nat.succ_le_of_lt ((Nat.zero_le (X/d)).trans_lt (mem_Ioc.mp hk).1), (mem_Ioc.mp hk).2⟩
  rw [V1h8 n (Nat.div_le_self X d)]
  calc
    _ ≤ ∑ k ∈ Ioc (X/d) X, Vm.g n k * ((d : ℝ)/X) := by
      apply sum_le_sum
      intro k hk
      have hkR : (0 : ℝ) < k := by exact_mod_cast Nat.zero_lt_of_lt (mem_Ioc.mp hk).1
      have hxk := (Nat.div_lt_iff_lt_mul hd).mp (mem_Ioc.mp hk).1
      have hxkR : (X : ℝ) ≤ k * d := by exact_mod_cast hxk.le
      have hcoeff : (1 : ℝ)/(k : ℝ) ≤ (d : ℝ)/X :=
        (div_le_div_iff₀ hkR hXR).mpr (by nlinarith)
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left hcoeff (Vg7 n k).1
    _ ≤ ∑ k ∈ Icc 1 X, Vm.g n k * ((d : ℝ)/X) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => mul_nonneg (Vg7 n k).1 (by positivity))
    _ = _ := by
      rw [← sum_mul]
      unfold Vm.gAvg Vm.gSum
      ring
theorem V1oz (n X d : ℕ) (hd : 0 < d) :
    V3w n X - V3w n (X/d) ≤ 1 + Real.log d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlogd : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd)
  by_cases hX : X = 0
  · simp [hX, V3w]
    positivity
  have hXR : (0 : ℝ) < X := by exact_mod_cast Nat.pos_of_ne_zero hX
  have hfloor := Nat.div_le_self X d
  have hQ : (0 : ℝ) < ((X / d : ℕ) : ℝ) + 1 := by positivity
  have hdiv : (X : ℝ) / (((X / d : ℕ) : ℝ) + 1) ≤ d := by
    apply (div_le_iff₀ hQ).mpr
    exact_mod_cast (Nat.lt_mul_div_succ X hd).le
  have hlogs : Real.log (X : ℝ) - Real.log (((X / d : ℕ) : ℝ) + 1) ≤ Real.log d := by
    rw [← Real.log_div hXR.ne' hQ.ne']
    exact Real.log_le_log (div_pos hXR hQ) hdiv
  have hH := harmonic_le_one_add_log X
  have hL := log_add_one_le_harmonic (X/d)
  have hsum : (∑ k ∈ Ioc (X/d) X, (k : ℝ)⁻¹) =
      (harmonic X:ℝ) - (harmonic (X/d):ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    have hp := Vm.Vki (fun k : ℕ => (k : ℝ)⁻¹) hfloor
    linarith
  rw [V1h8 n hfloor]
  calc
    _ ≤ ∑ k ∈ Ioc (X/d) X, (k : ℝ)⁻¹ := by
      apply sum_le_sum
      intro k _
      rw [div_eq_mul_inv]
      exact mul_le_of_le_one_left (inv_nonneg.mpr (Nat.cast_nonneg k)) (Vg7 n k).2
    _ = _ := hsum
    _ ≤ _ := by
      rw [Nat.cast_add, Nat.cast_one] at hL
      linarith
theorem V1pn (n A : ℕ) (hA : 0 < A) (t η : ℝ)
    (hlo : |Vm.gAvg n A - t| ≤ η)
    (hhi : |Vm.gAvg n (2*A) - t| ≤ η) :
    t/2 - (3/2)*η ≤ V3w n (2*A) - V3w n A := by
  have hAB : A ≤ 2*A := by omega
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hBA := Vm.Vki (Vm.g n) hAB
  change Vm.gSum n (2*A) = Vm.gSum n A + _ at hBA
  have hweak : Vm.gAvg n (2*A) - Vm.gAvg n A / 2 ≤
      V3w n (2*A) - V3w n A := by
    rw [V1h8 n hAB]
    calc
      _ = (∑ j ∈ Ioc A (2*A), Vm.g n j) / ((2*A : ℕ) : ℝ) := by
        unfold Vm.gAvg
        rw [← sub_eq_of_eq_add hBA]
        push_cast
        field_simp; ring
      _ ≤ _ := by
        rw [sum_div]
        apply sum_le_sum
        intro k hk
        apply div_le_div_of_nonneg_left (Vg7 n k).1
        · exact_mod_cast hA.trans (mem_Ioc.mp hk).1
        · exact_mod_cast (mem_Ioc.mp hk).2
  linarith [(abs_le.mp hlo).2, (abs_le.mp hhi).1]
theorem V18x (n : ℕ) (t η : ℝ) :
    ∀ (L A : ℕ), 0 < A →
      (∀ j ≤ L, |Vm.gAvg n (2^j*A) - t| ≤ η) →
      (L : ℝ) * (t/2 - (3/2)*η) ≤ V3w n (2^L*A) - V3w n A := by
  intro L
  induction L with
  | zero => simp
  | succ L ih =>
    intro A hA hnear
    have hm := ih A hA (fun j hj => hnear j (by omega))
    have ht : 0 < 2^L*A := Nat.mul_pos (pow_pos (by decide) _) hA
    have hh := V1pn n (2^L*A) ht t η (hnear L (by omega)) (by
      simpa only [pow_succ', mul_assoc] using hnear (L+1) le_rfl)
    push_cast
    rw [pow_succ', mul_assoc]
    linarith
end V1s
namespace V1s
open Finset Filter ArithmeticFunction
open scoped Topology
private theorem V1bs (X : ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ q ∈ Icc 1 X, ∑ v ∈ q.divisorsAntidiagonal, f v) =
      ∑ d ∈ Icc 1 X, ∑ k ∈ Icc 1 (X/d), f (d,k) := by
  classical
  let S := Icc 1 X
  have hf (q : ℕ) (hq : q ∈ S) :
      q.divisorsAntidiagonal = (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q) := by
    obtain ⟨hq0,hqQ⟩ := mem_Icc.mp hq
    ext ab
    constructor
    · intro hab
      have hm (a : ℕ) (ha : a ∈ q.divisors) : a ∈ S :=
        mem_Icc.mpr ⟨Nat.pos_of_mem_divisors ha,(Nat.le_of_dvd hq0 (Nat.dvd_of_mem_divisors ha)).trans hqQ⟩
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hm _ (Nat.fst_mem_divisors_of_mem_antidiagonal hab),
        hm _ (Nat.snd_mem_divisors_of_mem_antidiagonal hab)⟩,(Nat.mem_divisorsAntidiagonal.mp hab).1⟩
    · intro hh; exact Nat.mem_divisorsAntidiagonal.mpr ⟨(mem_filter.mp hh).2,by omega⟩
  calc
    _ = ∑ q ∈ S, ∑ v ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q), f v :=
      sum_congr rfl (fun q hq => by rw [hf q hq])
    _ = ∑ v ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2 ∈ S), f v :=
      sum_fiberwise_eq_sum_filter _ _ _ _
    _ = _ := by
      rw [sum_filter,sum_product]
      apply sum_congr rfl
      intro d hd
      have hd0 := (mem_Icc.mp hd).1
      have hkd : (S.filter fun k => d*k∈S)=Icc 1 (X/d) := by
        ext k
        simp only [S,mem_filter,mem_Icc]
        constructor
        · rintro ⟨⟨hk,_⟩,_,hdk⟩
          exact ⟨hk,(Nat.le_div_iff_mul_le hd0).mpr (by simpa [mul_comm] using hdk)⟩
        · rintro ⟨hk,hkx⟩
          exact ⟨⟨hk,hkx.trans (Nat.div_le_self _ _)⟩,Nat.mul_pos hd0 hk,by simpa [mul_comm] using (Nat.le_div_iff_mul_le hd0).mp hkx⟩
      rw [←sum_filter,hkd]
theorem V18y (n X : ℕ) :
    V1za n X = ∑ d ∈ Icc 1 X, Vm.z n d * V3w n (X/d) := by
  let f := fun v : ℕ × ℕ => Vm.z n v.1 * (Vm.g n v.2 / (v.2 : ℝ))
  calc
    _ = ∑ q ∈ Icc 1 X, ∑ v ∈ q.divisorsAntidiagonal, f v := by
      apply sum_congr rfl
      intro q _
      rw [Vm.convolution n,mul_comm (Vm.g n) (Vm.h n),ArithmeticFunction.mul_apply,sum_div]
      apply sum_congr rfl
      intro v hv
      change Vm.h n v.1*Vm.g n v.2/(q:ℝ) =
        (Vm.h n v.1/(v.1:ℝ))*(Vm.g n v.2/(v.2:ℝ))
      rw [←(Nat.mem_divisorsAntidiagonal.mp hv).1, Nat.cast_mul,div_eq_mul_inv,mul_inv]
      simp only [div_eq_mul_inv]
      ring
    _ = ∑ d ∈ Icc 1 X, ∑ k ∈ Icc 1 (X/d), f (d,k) := V1bs X f
    _ = _ := by simp [f,V3w,mul_sum]
theorem Vq3 (n X : ℕ) :
    (∑ q ∈ Icc 1 X, |Vm.F n q|) ≤ Vm.V2i * (X:ℝ) := by
  classical
  let f : ℕ × ℕ → ℝ := fun v => |Vm.h n v.1|
  calc
    _ ≤ ∑ q ∈ Icc 1 X, ∑ v ∈ q.divisorsAntidiagonal, f v := by
      apply sum_le_sum
      intro q _
      rw [Vm.convolution n,mul_comm (Vm.g n) (Vm.h n),ArithmeticFunction.mul_apply]
      refine (abs_sum_le_sum_abs _ _).trans ?_
      apply sum_le_sum
      intro v _
      rw [abs_mul,abs_of_nonneg (Vg7 n v.2).1]
      exact mul_le_of_le_one_right (abs_nonneg _) (Vg7 n v.2).2
    _ = ∑ d ∈ Icc 1 X, ∑ k ∈ Icc 1 (X/d), f (d,k) := V1bs X f
    _ ≤ ∑ d ∈ Icc 1 X, |Vm.z n d| * (X:ℝ) := by
      apply sum_le_sum
      intro d hd
      have hd0 := (mem_Icc.mp hd).1
      have hdR : (0:ℝ)<d := by exact_mod_cast hd0
      have hdiv : ((X/d:ℕ):ℝ) ≤ (X:ℝ)/(d:ℝ) := by
        apply (le_div_iff₀ hdR).2
        exact_mod_cast Nat.div_mul_le_self X d
      calc
        _ = ((X/d:ℕ):ℝ)*|Vm.h n d| := by
          simp [f,Nat.card_Icc,nsmul_eq_mul]
        _ ≤ ((X:ℝ)/(d:ℝ))*|Vm.h n d| := mul_le_mul_of_nonneg_right hdiv (abs_nonneg _)
        _ = _ := by
          rw [Vm.z,ArithmeticFunction.coe_mk,abs_div,abs_of_pos hdR]
          ring
    _ = (∑ d ∈ Icc 1 X, |Vm.z n d|) * (X:ℝ) := (sum_mul ..).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa using Vm.V1bh n 1 (Icc 1 X) (by decide) (fun d hd => (mem_Icc.mp hd).1)
theorem V19z (n K X : ℕ) (hKX : K ≤ X) :
    (∑ q ∈ Ioc K X, Vm.F n q / (q:ℝ)) =
      ∑ d ∈ Icc 1 X, Vm.z n d * (V3w n (X/d)-V3w n (K/d)) := by
  have hsub := Vm.Vki (fun q => Vm.F n q / (q:ℝ)) hKX
  have hsub' : (∑ q ∈ Ioc K X, Vm.F n q / (q:ℝ)) = V1za n X-V1za n K := by
    unfold V1za
    linarith
  have hK :
      ∑ d ∈ Icc 1 K, Vm.z n d * V3w n (K/d) =
        ∑ d ∈ Icc 1 X, Vm.z n d * V3w n (K/d) := by
    apply sum_subset (Icc_subset_Icc_right hKX)
    intro d hd hnot
    have hdK : K<d := by
      simp only [mem_Icc,not_and] at hnot
      have hd' := mem_Icc.mp hd
      omega
    simp [Nat.div_eq_of_lt hdK,V3w]
  rw [hsub',V18y n X,V18y n K,hK,←sum_sub_distrib]
  apply sum_congr rfl
  intro d _
  ring
theorem V1zc (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ J : ℕ in atTop, 0 < J ∧ ∀ n : ℕ, ∀ s : Finset ℕ, (∀ d ∈ s, J ≤ d) →
      (∑ d ∈ s, |Vm.z n d| *(1+Real.log d)) ≤ ε := by
  have hC : 0 < Vm.V2i := Real.exp_pos _
  let τ := ε/(2*Vm.V2i)
  have hτ : 0<τ := by dsimp [τ]; positivity
  have hc := tendsto_natCast_atTop_atTop (R:=ℝ)
  have hm := ((isLittleO_log_rpow_rpow_atTop (1:ℝ) (by norm_num : (0:ℝ)<1/4)).comp_tendsto hc).bound hτ
  have hlog := (Real.tendsto_log_atTop.comp hc).eventually_ge_atTop (1:ℝ)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hm.and hlog)
  filter_upwards [eventually_ge_atTop (max N 1)] with J hJ
  have hJ' : 0<J := lt_of_lt_of_le (by decide : 0<1) ((le_max_right N 1).trans hJ)
  refine ⟨hJ',?_⟩
  intro n s hs
  have hbound (d : ℕ) (hd : d ∈ s) : |Vm.z n d| *(1+Real.log d) ≤
      (ε/Vm.V2i)*Vm.w n d := by
    have hdJ := hs d hd
    have hd0 := hJ'.trans_le hdJ
    have hz : (0:ℝ)<(d:ℝ)^(1/4:ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hd0) _
    obtain ⟨ha,hb⟩ := hN d ((le_max_left N 1).trans (hJ.trans hdJ))
    change ‖(Real.log (d:ℝ))^(1:ℝ)‖ ≤ τ*‖(d:ℝ)^(1/4:ℝ)‖ at ha
    change 1 ≤ Real.log (d:ℝ) at hb
    rw [Real.rpow_one,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0≤Real.log (d:ℝ)),
      Real.norm_eq_abs,abs_of_pos hz] at ha
    have hh : 1+Real.log (d:ℝ) ≤ (ε/Vm.V2i)*(d:ℝ)^(1/4:ℝ) := by
      have hτ' : 2*τ=ε/Vm.V2i := by dsimp [τ]; ring
      rw [←hτ',mul_assoc]
      linarith
    calc
      _ ≤ (Vm.w n d/(d:ℝ)^(1/4:ℝ))*(1+Real.log d) :=
        mul_le_mul_of_nonneg_right (Vm.V239 n d d hd0 le_rfl) (by linarith)
      _ ≤ (Vm.w n d/(d:ℝ)^(1/4:ℝ))*((ε/Vm.V2i)*(d:ℝ)^(1/4:ℝ)) :=
        mul_le_mul_of_nonneg_left hh (div_nonneg (Vm.w_nonneg n d) hz.le)
      _ = _ := by field_simp
  have hu : ∑ d ∈ s, Vm.w n d ≤ Vm.V2i := by
    apply le_trans _ (Vm.V1yh n (s.sup id))
    apply sum_le_sum_of_subset_of_nonneg
    · intro d hd
      exact mem_Icc.mpr ⟨hJ'.trans_le (hs d hd),le_sup (f:=id) hd⟩
    · intro d _ _
      exact Vm.w_nonneg n d
  calc
    _ ≤ ∑ d ∈ s, (ε/Vm.V2i)*Vm.w n d := sum_le_sum hbound
    _ = (ε/Vm.V2i)*(∑ d ∈ s,Vm.w n d) := (mul_sum ..).symm
    _ ≤ (ε/Vm.V2i)*Vm.V2i := mul_le_mul_of_nonneg_left hu (by positivity)
    _ = _ := by field_simp
end V1s
namespace V1s
open Finset Filter
open scoped Topology
private theorem V1rf (n K X d : ℕ) :
    V3w n (X/d) - V3w n (K/d) -
      (V3w n X - V3w n K) =
      (V3w n K - V3w n (K/d)) -
      (V3w n X - V3w n (X/d)) := by ring
private theorem V1ow (n K X d : ℕ) :
    |V3w n (X/d) - V3w n (K/d) -
      (V3w n X - V3w n K)| ≤
      (V3w n K - V3w n (K/d)) +
      (V3w n X - V3w n (X/d)) := by
  rw [V1rf]
  have hK := sub_nonneg.mpr (Vxj n (Nat.div_le_self K d))
  have hX := sub_nonneg.mpr (Vxj n (Nat.div_le_self X d))
  exact abs_le.mpr ⟨by linarith, by linarith⟩
private theorem V1sk (n X : ℕ) : 0 ≤ Vm.gAvg n X := by
  unfold Vm.gAvg Vm.gSum
  exact div_nonneg (sum_nonneg fun k _ => (Vg7 n k).1) (by positivity)
theorem V1i6 (n K X J : ℕ) (hK : 0 < K) (hKX : K ≤ X)
    (hJX : J ≤ X) (e : ℝ)
    (hZ : (1/8 : ℝ) ≤ ∑ d ∈ Icc 1 X, Vm.z n d)
    (hlog : (∑ d ∈ Ioc J X, |Vm.z n d| * (1 + Real.log d)) ≤ e) :
    (1/8 : ℝ) * (V3w n X - V3w n K) -
      (J : ℝ) * Vm.V2i * (Vm.gAvg n K + Vm.gAvg n X) - 2*e ≤
      ∑ q ∈ Ioc K X, Vm.F n q / (q:ℝ) := by
  let A := V3w n X - V3w n K
  let D (d : ℕ) := V3w n (X/d) - V3w n (K/d) - A
  let t := Vm.gAvg n K + Vm.gAvg n X
  have ht := add_nonneg (V1sk n K) (V1sk n X)
  have hpos := sub_nonneg.mpr (Vxj n hKX)
  have hlow (d : ℕ) : -(abs (Vm.z n d) * abs (D d)) ≤ Vm.z n d * D d := by
    rw [← abs_mul]
    exact neg_abs_le _
  have hsmall : -((J : ℝ) * Vm.V2i * t) ≤ ∑ d ∈ Icc 1 J, Vm.z n d * D d := by
    have habs (d : ℕ) (hd : d ∈ Icc 1 J) : |D d| ≤ (J : ℝ) * t := by
      have hd0 := (mem_Icc.mp hd).1
      calc
        _ ≤ _ := V1ow n K X d
        _ ≤ (d : ℝ) * t := by
          dsimp [t]
          rw [mul_add]
          exact add_le_add (V1lm n K d hK hd0)
            (V1lm n X d (hK.trans_le hKX) hd0)
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (mem_Icc.mp hd).2) ht
    have hU : (∑ d ∈ Icc 1 J, |Vm.z n d|) ≤ Vm.V2i := by
      simpa using Vm.V1bh n 1 (Icc 1 J) (by decide) (fun d hd => (mem_Icc.mp hd).1)
    calc
      _ = -(Vm.V2i * ((J : ℝ) * t)) := by ring
      _ ≤ -((∑ d ∈ Icc 1 J, |Vm.z n d|) * ((J : ℝ) * t)) :=
        neg_le_neg (mul_le_mul_of_nonneg_right hU (mul_nonneg (Nat.cast_nonneg J) ht))
      _ = ∑ d ∈ Icc 1 J, -(|Vm.z n d| * ((J : ℝ) * t)) := by rw [sum_neg_distrib, sum_mul]
      _ ≤ _ := sum_le_sum fun d hd =>
        (neg_le_neg (mul_le_mul_of_nonneg_left (habs d hd) (abs_nonneg _))).trans (hlow d)
  have hlarge : -(2*e) ≤ ∑ d ∈ Ioc J X, Vm.z n d * D d := by
    have habs (d : ℕ) (hd : d ∈ Ioc J X) : |D d| ≤ 2 * (1 + Real.log d) := by
      have hd0 := (Nat.zero_le J).trans_lt (mem_Ioc.mp hd).1
      calc
        _ ≤ _ := V1ow n K X d
        _ ≤ (1 + Real.log d) + (1 + Real.log d) := by
          exact add_le_add (V1oz n K d hd0) (V1oz n X d hd0)
        _ = _ := by ring
    calc
      _ ≤ -(2*(∑ d ∈ Ioc J X, |Vm.z n d| * (1 + Real.log d))) :=
        neg_le_neg (mul_le_mul_of_nonneg_left hlog (by norm_num))
      _ = ∑ d ∈ Ioc J X, -(|Vm.z n d| * (2 * (1 + Real.log d))) := by
        rw [sum_neg_distrib, mul_sum]
        congr 1
        apply sum_congr rfl
        intro d _
        ring
      _ ≤ _ := sum_le_sum fun d hd =>
        (neg_le_neg (mul_le_mul_of_nonneg_left (habs d hd) (abs_nonneg _))).trans (hlow d)
  have hsplit := Vm.Vki (fun d => Vm.z n d * D d) hJX
  rw [V19z n K X hKX]
  have hrewrite : (∑ d ∈ Icc 1 X, Vm.z n d *
      (V3w n (X/d) - V3w n (K/d))) =
      (∑ d ∈ Icc 1 X, Vm.z n d) * A + ∑ d ∈ Icc 1 X, Vm.z n d * D d := by
    rw [sum_mul, ←sum_add_distrib]
    apply sum_congr rfl
    intro d _
    dsimp [D]
    ring
  rw [hrewrite, hsplit]
  change (1/8 : ℝ) * A - (J : ℝ)*Vm.V2i*t - 2*e ≤ _
  linarith [mul_le_mul_of_nonneg_right hZ hpos]
end V1s
namespace V1s
open Finset Filter
open scoped Topology
theorem Vr9 (ε : ℝ) (hε : 0 < ε) :
    ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ n X : ℕ, Even n → K ≤ X →
      -ε ≤ ∑ q ∈ Ioc K X, Vm.F n q / (q:ℝ) := by
  obtain ⟨J,hJ⟩ := eventually_atTop.mp
    (V1od.and (V1zc (ε/4) (by positivity)))
  obtain ⟨hJ₀,_⟩ := (hJ J le_rfl).1
  obtain ⟨m,hm⟩ := exists_nat_ge (16 * ((J:ℝ) * Vm.V2i))
  let L := m+1
  let T : ℕ := 2^L
  have hT : 0 < T := pow_pos (by decide) _
  have hC : (1:ℝ) ≤ 2*(T:ℝ) := by
    have ht' : (1:ℝ) ≤ T := by exact_mod_cast hT
    linarith
  have hL : (0:ℝ) < L := by exact_mod_cast (Nat.zero_lt_succ m)
  have hLJ : (J:ℝ)*Vm.V2i ≤ (L:ℝ)/16 := by
    change (J:ℝ)*Vm.V2i ≤ ((m+1:ℕ):ℝ)/16
    push_cast
    linarith
  let η := ε/(L:ℝ)
  have hη : 0 < η := div_pos hε hL
  have hLη : (L:ℝ)*η=ε := by dsimp [η]; field_simp
  obtain ⟨M,hM⟩ := eventually_atTop.mp (Vm.V22r (2*(T:ℝ)) η hC hη)
  have hR : 1 ≤ T*T := Nat.mul_pos hT hT
  obtain ⟨N,hN⟩ := Vm.V1uk (T*T) hR ε hε
  refine ⟨max J (max M N),?_⟩
  intro K hK₀ n X hn hKX
  have hJK : J ≤ K := (le_max_left J (max M N)).trans hK₀
  have hMK : M ≤ K := ((le_max_left M N).trans (le_max_right J (max M N))).trans hK₀
  have hNK : N ≤ K := ((le_max_right M N).trans (le_max_right J (max M N))).trans hK₀
  have hK : 0 < K := hJ₀.trans_le hJK
  have hKR : (0:ℝ)<K := by exact_mod_cast hK
  by_cases hnear : X ≤ (T*T)*K
  · have hh := Vm.V1ss K X (Vm.F n)
      (fun q => (q:ℝ)⁻¹) (ε*(K:ℝ)) hKX (by positivity)
      (fun i _ => by positivity)
      (fun i hi => by
        apply inv_anti₀
        · exact_mod_cast hK.trans_le hi
        · exact_mod_cast Nat.le_succ i)
      (fun i hi hiX => hN K hNK n i hi (hiX.trans hnear))
    have hEq : -(ε*(K:ℝ)*(K:ℝ)⁻¹) = -ε := by field_simp
    rw [hEq] at hh
    simpa [div_eq_mul_inv] using hh
  · let B := X/T
    have hfar : (T*T)*K ≤ X := le_of_lt (lt_of_not_ge hnear)
    have hKB : T*K ≤ B := by
      apply (Nat.le_div_iff_mul_le hT).2
      calc
        T*K*T = (T*T)*K := by ring
        _ ≤ X := hfar
    have hB : 0<B := (Nat.mul_pos hT hK).trans_le hKB
    have hBX : T*B ≤ X := Nat.mul_div_le X T
    have hXT : X ≤ 2*T*B := by
      have hmod := Nat.mod_lt X hT
      have hdiv : X % T + T * B = X := Nat.mod_add_div X T
      have hTB : T ≤ T*B := by
        simpa using Nat.mul_le_mul_left T (show 1≤B from hB)
      have he : 2*T*B=T*B+T*B := by ring
      rw [he]
      omega
    have hdT (j : ℕ) (hj : j≤L) : (2:ℕ)^j≤T := Nat.pow_le_pow_right (by decide) hj
    have hd1 (j : ℕ) : 1≤(2:ℕ)^j := pow_pos (by decide : 0<(2:ℕ)) j
    have hKm (j : ℕ) : K ≤ 2^j*K := by simpa using Nat.mul_le_mul_right K (hd1 j)
    have hBm (j : ℕ) : B ≤ 2^j*B := by simpa using Nat.mul_le_mul_right B (hd1 j)
    have hslowK (j : ℕ) (hj : j≤L) : |Vm.gAvg n (2^j*K)-Vm.gAvg n K| ≤ η := by
      apply hM (2^j*K) (hMK.trans (hKm j)) K hK (hKm j) _ n
      have hx : (2:ℕ)^j*K≤T*K := Nat.mul_le_mul_right K (hdT j hj)
      have hx' : (((2:ℕ)^j*K : ℕ):ℝ) ≤ (T:ℝ)*(K:ℝ) := by exact_mod_cast hx
      nlinarith [show (0:ℝ)≤(T:ℝ)*(K:ℝ) by positivity]
    have hslowX (j : ℕ) (hj : j≤L) : |Vm.gAvg n (2^j*B)-Vm.gAvg n X| ≤ η := by
      rw [abs_sub_comm]
      apply hM X (hMK.trans hKX) (2^j*B) (hB.trans_le (hBm j))
        ((Nat.mul_le_mul_right B (hdT j hj)).trans hBX) _ n
      have hXj : X ≤ 2*T*(2^j*B) := hXT.trans (Nat.mul_le_mul_left (2*T) (hBm j))
      exact_mod_cast hXj
    have hnearK := V18x n (Vm.gAvg n K) η L K hK hslowK
    have hnearX := V18x n (Vm.gAvg n X) η L B hB hslowX
    have hmid := Vxj n hKB
    have hlast := Vxj n hBX
    change (L:ℝ)*(Vm.gAvg n K/2 - (3/2)*η) ≤ V3w n (T*K)-V3w n K at hnearK
    change (L:ℝ)*(Vm.gAvg n X/2 - (3/2)*η) ≤ V3w n (T*B)-V3w n B at hnearX
    have hlong : ((L:ℝ)/2)*(Vm.gAvg n K+Vm.gAvg n X)-3*ε ≤
      V3w n X-V3w n K := by linarith
    have hJX := hJK.trans hKX
    have hZ := (hJ X hJX).1.2 n hn
    have hlog := (hJ J le_rfl).2.2 n (Ioc J X) (fun d hd => (mem_Ioc.mp hd).1.le)
    have hlower := V1i6 n K X J hK hKX hJX (ε/4) hZ hlog
    have hdom := mul_le_mul_of_nonneg_right hLJ
      (add_nonneg (V1sk n K) (V1sk n X))
    linarith
end V1s
namespace V1s
open Finset
theorem Vlv (n q : ℕ) (hq : 0 < q) :
    (Vr.V3f q n).re = Vm.F n q / (q:ℝ) := by
  have hqR : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  simp [Vm.F,hqR]
theorem V19y (ε : ℝ) (hε : 0 < ε) :
    ∃ Q₀ : ℕ, ∀ Q ≥ Q₀, ∀ n : ℕ, Even n → ∀ w : ℕ → ℝ, Monotone w →
      (∀ q, 0 ≤ w q) → w Q ≤ 2 →
      (∀ q ∈ Icc 1 Q, w q ≤ (q:ℝ)/(Q:ℝ)) →
      -ε ≤ ∑ q ∈ Icc 1 Q, (Vm.F n q / (q:ℝ)) * w q := by
  have hδ : 0 < ε/4 := by positivity
  obtain ⟨K₀,hK₀⟩ := Vr9 (ε/4) hδ
  let K := max K₀ 1
  have hK₁ : 1 ≤ K := le_max_right _ _
  obtain ⟨M,hM⟩ := exists_nat_ge (2 * (Vm.V2i * (K:ℝ)) / ε)
  refine ⟨max K M, ?_⟩
  intro Q hQ n hn w hw hw₀ hwQ hweight
  have hKQ : K ≤ Q := (le_max_left _ _).trans hQ
  have hMQ : M ≤ Q := (le_max_right _ _).trans hQ
  have hQR : (0:ℝ) < Q := by exact_mod_cast hK₁.trans hKQ
  have hQM : 2 * (Vm.V2i * (K:ℝ)) / ε ≤ (Q:ℝ) :=
    hM.trans (by exact_mod_cast hMQ)
  have hcut : Vm.V2i * (K:ℝ) / (Q:ℝ) ≤ ε/2 := by
    have hs := (div_le_iff₀ hε).1 hQM
    apply (div_le_iff₀ hQR).2
    linarith
  have hterm (q : ℕ) (hq : q ∈ Icc 1 K) :
      -(|Vm.F n q| / (Q:ℝ)) ≤ (Vm.F n q / (q:ℝ)) * w q := by
    have hqR : (0:ℝ) < q := by exact_mod_cast (mem_Icc.mp hq).1
    have hh := hweight q ((Icc_subset_Icc_right hKQ) hq)
    calc
      _ = -((|Vm.F n q| / (q:ℝ)) * ((q:ℝ)/(Q:ℝ))) := by field_simp
      _ ≤ -((|Vm.F n q| / (q:ℝ)) * w q) :=
        neg_le_neg (mul_le_mul_of_nonneg_left hh (div_nonneg (abs_nonneg _) hqR.le))
      _ ≤ _ := by
        have he : |(Vm.F n q / (q:ℝ)) * w q| =
            (|Vm.F n q| / (q:ℝ)) * w q := by
          rw [abs_mul, abs_div, abs_of_pos hqR, abs_of_nonneg (hw₀ q)]
        rw [←he]
        exact neg_abs_le _
  have hsmall :
      -(ε/2) ≤ ∑ q ∈ Icc 1 K, (Vm.F n q / (q:ℝ)) * w q := by
    calc
      _ ≤ -(Vm.V2i * (K:ℝ) / (Q:ℝ)) := neg_le_neg hcut
      _ ≤ -((∑ q ∈ Icc 1 K, |Vm.F n q|) / (Q:ℝ)) :=
        neg_le_neg (div_le_div_of_nonneg_right (Vq3 n K) hQR.le)
      _ = ∑ q ∈ Icc 1 K, -(|Vm.F n q| / (Q:ℝ)) := by
        rw [sum_neg_distrib, sum_div]
      _ ≤ _ := sum_le_sum hterm
  have hlen : K+(Q-K)=Q := Nat.add_sub_of_le hKQ
  have htail := V18p (fun q => Vm.F n q/(q:ℝ)) (ε/4) hδ.le
    (Q-K) K w hw (fun q _ => hw₀ q)
  rw [hlen] at htail
  have hrest := htail (fun k hk hkQ => hK₀ k ((le_max_left _ _).trans hk) n Q hn hkQ)
  have hrest' : -(ε/2) ≤ ∑ q ∈ Ioc K Q, (Vm.F n q/(q:ℝ))*w q := by
    exact (by linarith [mul_le_mul_of_nonneg_left hwQ hδ.le] : -(ε/2) ≤ -(ε/4 * w Q)).trans hrest
  rw [Vm.Vki (fun q => (Vm.F n q/(q:ℝ))*w q) hKQ]
  linarith
end V1s
namespace V1s
open Finset
theorem V1y5 (ε : ℝ) (hε : 0 < ε) :
    ∃ Q₀ : ℕ, ∀ Q ≥ Q₀, ∀ n U : ℕ, Even n → Q ≤ U →
      ∀ mass defect : ℝ, mass ∈ Set.Icc 0 2 → 0 ≤ defect →
      defect * (Vm.V2i * (U:ℝ)) ≤ ε/4 →
      ∀ wide taper : ℕ → ℝ, Monotone taper → (∀ q, 0 ≤ taper q) → taper Q ≤ 2 →
      (∀ q ∈ Icc 1 Q, taper q ≤ (q:ℝ)/(Q:ℝ)) →
      (∀ q ∈ Icc 1 U, |wide q-mass| ≤ defect*(q:ℝ)) →
      -ε ≤ (∑ q ∈ Ioc Q U, (Vr.V3f q n).re * wide q) +
        ∑ q ∈ Icc 1 Q, (Vr.V3f q n).re *
          (wide q-mass+taper q) := by
  have hδ : 0 < ε/4 := by positivity
  obtain ⟨Q₁,hQ₁⟩ := Vr9 (ε/4) hδ
  obtain ⟨Q₂,hQ₂⟩ := V19y (ε/4) hδ
  refine ⟨max Q₁ Q₂,?_⟩
  intro Q hQ n U hn hQU mass defect hmass hdefect hcost wide taper hmono hnonneg
    hcap hscale hwide
  let a (q : ℕ) := (Vr.V3f q n).re
  have hite (q : ℕ) (hq : q ∈ Ioc Q U) : 0 < q := (Nat.zero_le Q).trans_lt (mem_Ioc.mp hq).1
  have hlarge : -(ε/4) ≤ ∑ q ∈ Ioc Q U, a q := by
    have hh := hQ₁ Q ((le_max_left _ _).trans hQ) n U hn hQU
    refine hh.trans (le_of_eq (sum_congr rfl ?_))
    intro q hq
    exact (Vlv n q (hite q hq)).symm
  have hmain : -(ε/2) ≤ (∑ q ∈ Ioc Q U, a q)*mass := by
    exact (by linarith [mul_le_mul_of_nonneg_left hmass.2 hδ.le] :
      -(ε/2) ≤ -(ε/4)*mass).trans (mul_le_mul_of_nonneg_right hlarge hmass.1)
  have hsmall : -(ε/4) ≤ ∑ q ∈ Icc 1 Q, a q*taper q := by
    have hh := hQ₂ Q ((le_max_right _ _).trans hQ) n hn taper hmono hnonneg hcap hscale
    refine hh.trans (le_of_eq (sum_congr rfl ?_))
    intro q hq
    exact congrArg (fun x : ℝ => x*taper q) (Vlv n q (mem_Icc.mp hq).1).symm
  have herror : -(ε/4) ≤ ∑ q ∈ Icc 1 U, a q*(wide q-mass) := by
    have hterm (q : ℕ) (hq : q ∈ Icc 1 U) :
        -(defect*|Vm.F n q|) ≤ a q*(wide q-mass) := by
      have hq0 := (mem_Icc.mp hq).1
      have hqR : (0:ℝ)<q := by exact_mod_cast hq0
      have hAbs : |a q*(wide q-mass)| ≤ defect*|Vm.F n q| := by
        dsimp [a]
        rw [abs_mul, Vlv n q hq0, abs_div, abs_of_pos hqR]
        calc
          _ ≤ (|Vm.F n q|/(q:ℝ))*(defect*(q:ℝ)) :=
            mul_le_mul_of_nonneg_left (hwide q hq) (div_nonneg (abs_nonneg _) hqR.le)
          _ = _ := by field_simp
      exact (neg_le_neg hAbs).trans (neg_abs_le _)
    calc
      _ ≤ -(defect*(Vm.V2i*(U:ℝ))) := neg_le_neg hcost
      _ ≤ -(defect*(∑ q ∈ Icc 1 U, |Vm.F n q|)) :=
        neg_le_neg (mul_le_mul_of_nonneg_left (Vq3 n U) hdefect)
      _ = ∑ q ∈ Icc 1 U, -(defect*|Vm.F n q|) := by rw [sum_neg_distrib,mul_sum]
      _ ≤ _ := sum_le_sum hterm
  change -ε ≤ (∑ q ∈ Ioc Q U, a q * wide q) +
    ∑ q ∈ Icc 1 Q, a q * (wide q-mass+taper q)
  have H :
      (∑ q ∈ Ioc Q U, a q * wide q) =
        (∑ q ∈ Ioc Q U, a q)*mass + ∑ q ∈ Ioc Q U, a q*(wide q-mass) := by
    rw [sum_mul,←sum_add_distrib]
    apply sum_congr rfl
    intro q _
    ring
  have E := Vm.Vki (fun q => a q*(wide q-mass)) hQU
  rw [H]
  simp only [mul_add,sum_add_distrib]
  linarith
end V1s
end V1s
section V72
open Filter Finset MeasureTheory
open scoped Topology Interval Classical
namespace V72
open V20 (narrow cutoff width)
open V19 (radius centers cell)
open V24 (mass)
open Vr (V3f)
theorem Vdi (m : ℕ) : ∀ᶠ n : ℕ in atTop, m ≤ narrow n := by
  filter_upwards [eventually_ge_atTop (2^m : ℕ)] with n hn
  have h := Nat.le_log_of_pow_le (by decide : 1 < 2) (hn.trans (by omega : n≤n+2))
  have h₁ : 1 ≤ Nat.log 2 (n+2) := Nat.log_pos (by decide) (by omega)
  have h₂ := Nat.mul_le_mul_left (Nat.log 2 (n+2)) h₁
  exact h.trans (by simpa [narrow,pow_two] using h₂)
noncomputable def normalized (n T q : ℕ) : ℝ :=
  mass n (radius n T (max 1 q)) / (n:ℝ)
theorem Vdy (n T q : ℕ) (hn : 0 < n) (hT : 0 < T) (hbudget : 24*T≤n) :
    0 ≤ ((n:ℝ)+1)/(n:ℝ)-normalized n T q ∧
     ((n:ℝ)+1)/(n:ℝ)-normalized n T q ≤ (max 1 q:ℕ)/(2*(T:ℝ)) := by
  let r := radius n T (max 1 q)
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hTR : 0 < (T:ℝ) := by exact_mod_cast hT
  have hqR : (1:ℝ) ≤ (max 1 q:ℕ) := by exact_mod_cast le_max_left 1 q
  have hqpos : (0:ℝ) < ((max 1 q:ℕ):ℝ) := by linarith
  have hbn : 24*(T:ℝ) ≤ (n:ℝ) := by exact_mod_cast hbudget
  have hqp := mul_le_mul_of_nonneg_right hqR hnR.le
  have hr : 0 < r := by unfold r radius; positivity
  have hr' : r ≤ 1/2 := by
    apply (div_le_iff₀ (mul_pos hqpos hnR)).2
    nlinarith only [hqp,hbn,hTR]
  have hmass := V24.V23r n hr hr'
  change 0 ≤ ((n:ℝ)+1)/(n:ℝ) - mass n r/(n:ℝ) ∧
    ((n:ℝ)+1)/(n:ℝ) - mass n r/(n:ℝ) ≤ _
  rw [← sub_div]
  constructor
  · exact div_nonneg hmass.1 hnR.le
  · calc
      _ ≤ (1/(2*r))/(n:ℝ) := div_le_div_of_nonneg_right hmass.2 hnR.le
      _ = _ := by
        unfold r radius
        field_simp [hnR.ne',hqpos.ne',hTR.ne']
end V72
end V72
section V8k
open Filter Finset MeasureTheory
open scoped Interval Topology Classical
namespace V8k
open V31 (phase Vi3 Vb2)
open V20 (narrow cutoff width)
open V19 (cap center centers cell radius)
open Va2 (model Ve5)
open V54 (V8a)
open Vf0 (Vll V1bv)
open Vcr (poly)
noncomputable def V13w (n : ℕ) (t : ℝ) : ℂ := Vi3 n t ^ 2 * phase (-(n:ℝ)*t)
end V8k
end V8k
end
section
open Filter Finset MeasureTheory
open scoped Topology Interval Classical
namespace V18m
open V20 (narrow cutoff width)
open V19 (radius centers cell cap)
open V24 (mass)
open Vr (V3f)
open V72 (normalized Vdy)
open V31 (phase Vi3 Vb2)
open Va2 (model Ve5)
open V8k (V13w)
theorem Vdi (m : ℕ) : ∀ᶠ n : ℕ in atTop, m ≤ narrow n := by
  filter_upwards [eventually_ge_atTop (2^m : ℕ)] with n hn
  have h := Nat.le_log_of_pow_le (by decide : 1 < 2) (hn.trans (by omega : n≤n+2))
  have h₁ : 1 ≤ Nat.log 2 (n+2) := Nat.log_pos (by decide) (by omega)
  have h₂ := Nat.mul_le_mul_left (Nat.log 2 (n+2)) h₁
  exact h.trans (by simpa [narrow,pow_two] using h₂)
theorem Vkq (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Even n →
      -ε * (n:ℝ) ≤
      (∑ i ∈ centers (narrow n), ∫ t in cell n (narrow n) (width n) i,
        Va2.model n i t^2 * V31.phase (-(n:ℝ)*t)).re := by
  obtain ⟨Q₀,hfloor⟩ := V1s.V1y5 ε hε
  obtain ⟨P,hP⟩ := exists_nat_ge (4*(|Vm.V2i|+1)/ε)
  filter_upwards [V20.Vhd, Vdi Q₀,
    Vdi P] with n hgeo hQ₀ hQP
  intro hEven
  obtain ⟨hn,hQ,hQU,_,hbudget,_⟩ := hgeo
  let Q := narrow n
  let U := cutoff n
  let H := width n
  let full := ((n:ℝ)+1)/(n:ℝ)
  let d := 1/(2*(H:ℝ))
  let wide := normalized n H
  let taper (q : ℕ) := full - normalized n Q q
  have hn₀ : 0 < n := by omega
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn₀
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (show 1≤n by omega)
  have hU₀ : 1≤U := hQ.trans hQU
  have hUH : U≤H := V20.Vrx n hQ
  have hQH : Q≤H := hQU.trans hUH
  have hH₀ : 0<H := hU₀.trans hUH
  have hHn : H≤n := by change 24*H≤n at hbudget; omega
  have hH' : 0 < (H:ℝ) := by exact_mod_cast hH₀
  have hQ' : 0 < (Q:ℝ) := by exact_mod_cast hQ
  have hU' : 0 < (U:ℝ) := by exact_mod_cast hU₀
  have hQbudget : 24*Q≤n := (Nat.mul_le_mul_left 24 hQH).trans hbudget
  have hfull : full ∈ Set.Icc 0 2 := ⟨by unfold full; positivity,
    (div_le_iff₀ hnR).2 (by linarith)⟩
  have hcost : d*(Vm.V2i*(U:ℝ)) ≤ ε/4 := by
    have hhQ : (4*(|Vm.V2i|+1)/ε : ℝ) ≤ (Q:ℝ) :=
      hP.trans (by exact_mod_cast hQP)
    have hv := (div_le_iff₀ hε).1 hhQ
    have hconst : Vm.V2i ≤ (ε/4)*(512*(Q:ℝ)) := by
      have hnon := mul_nonneg hε.le hQ'.le
      nlinarith [le_abs_self Vm.V2i]
    have hval : d*(Vm.V2i*(U:ℝ)) = Vm.V2i/(512*(Q:ℝ)) := by
      unfold d H width
      push_cast
      change 1/(2*(256*(U:ℝ)*(Q:ℝ)))*(Vm.V2i*(U:ℝ)) = _
      field_simp [hU'.ne', hQ'.ne']
      ring
    rw [hval]
    exact (div_le_iff₀ (show 0 < 512*(Q:ℝ) by positivity)).2 hconst
  have htaper : ∀ q, 0≤taper q := fun q =>
    (Vdy n Q q hn₀ hQ hQbudget).1
  have hmono : Monotone taper := by
    intro q r hqr
    apply sub_le_sub_left
    unfold normalized
    apply div_le_div_of_nonneg_right _ hnR.le
    apply V24.V22s
    · unfold radius
      positivity
    · unfold radius
      apply div_le_div_of_nonneg_left (by positivity)
        (mul_pos (by exact_mod_cast (show 0 < max 1 q by omega)) hnR)
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast max_le_max (le_refl 1) hqr) hnR.le
  have htcap : taper Q≤2 := by
    have hnon : 0≤normalized n Q Q := by
      unfold normalized
      apply div_nonneg _ hnR.le
      exact V24.V20p _ (by unfold radius; positivity)
    unfold taper
    linarith [hfull.2]
  have htbound : ∀ q∈Icc 1 Q, taper q ≤ (q:ℝ)/(Q:ℝ) := by
    intro q hq
    have hh := (Vdy n Q q hn₀ hQ hQbudget).2
    rw [max_eq_right (Finset.mem_Icc.mp hq).1] at hh
    exact hh.trans (div_le_div_of_nonneg_left (by positivity) hQ' (by linarith))
  have hwbound : ∀ q∈Icc 1 U, |wide q-full|≤d*(q:ℝ) := by
    intro q hq
    obtain ⟨h₁,h₂⟩ := Vdy n H q hn₀ hH₀ hbudget
    rw [max_eq_right (Finset.mem_Icc.mp hq).1] at h₂
    change 0≤full-wide q at h₁
    change full-wide q ≤ _ at h₂
    rw [abs_sub_comm, abs_of_nonneg h₁]
    unfold d
    exact h₂.trans_eq (by ring)
  have hCnon : 0 ≤ Vm.V2i := (Real.exp_pos _).le
  have hcostLow : d * (Vm.V2i * (Q : ℝ)) ≤ ε / 4 := by
    apply le_trans _ hcost
    apply mul_le_mul_of_nonneg_left _ (by unfold d; positivity)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hQU) hCnon
  have hwLow : ∀ q ∈ Icc 1 Q, |wide q-full| ≤ d*(q:ℝ) := by
    intro q hq
    exact hwbound q (mem_Icc.mpr ⟨(mem_Icc.mp hq).1, (mem_Icc.mp hq).2.trans hQU⟩)
  have hm := hfloor Q hQ₀ n Q hEven le_rfl full d hfull (by unfold d; positivity)
    hcostLow wide taper hmono htaper htcap htbound hwLow
  simp only [Finset.Ioc_self, Finset.sum_empty, zero_add] at hm
  rw [V4o.V1yo hQ hQH hHn]
  have hrew :
      (∑ q ∈ Icc 1 Q, (V3f q n).re * V4o.Vba n Q H q)
      = (∑ q ∈ Icc 1 Q, (V3f q n).re * (wide q-full+taper q)) * (n:ℝ) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q hq
    obtain ⟨hqL,hqU⟩ := Finset.mem_Icc.mp hq
    simp only [V4o.Vba, ite_eq_left hqU, taper,
      wide, normalized, max_eq_right hqL]
    field_simp [hnR.ne']
    ring
  rw [hrew]
  exact mul_le_mul_of_nonneg_right hm hnR.le
noncomputable def V1kw (n : ℕ) : ℂ :=
  ∫ t in (0:ℝ)..1,
    (cap n (narrow n) (width n) \ cap n (narrow n) (narrow n)).indicator (V13w n) t
noncomputable def V1zp (n : ℕ) : ℂ :=
  ∑ i ∈ centers (narrow n), ∫ t in cell n (narrow n) (width n) i,
    model n i t ^ 2 * phase (-(n:ℝ)*t)
end V18m
end
section
open Finset MeasureTheory
open scoped Interval Classical
namespace V73
open V54 (V8a V76 Viq V1u9)
open Vcr (poly moving)
open Vf0 (Vll)
variable {q : ℕ} [NeZero q]
private noncomputable def Vj0 (I : Finset ℕ) (w : ℕ → ℂ) (r : ZMod q) : ℂ :=
  ∑ k ∈ I.filter (fun k : ℕ => (k : ZMod q) = r), w k
private noncomputable def V95 (I : Finset ℕ) (w : ℕ → ℂ) (r : ZMod q) : ℂ :=
  Vj0 I w r - if IsUnit r then (I.card : ℂ) / (q.totient : ℂ) else 0
private theorem Vpi (I : Finset ℕ) (w : ℕ → ℂ) (K : ZMod q → ℂ) :
    (∑ r : ZMod q, Vj0 I w r * K r) =
      ∑ k ∈ I, w k * K (k : ZMod q) := by
  calc
    _ = ∑ r : ZMod q, ∑ k ∈ I.filter (fun k : ℕ => (k : ZMod q) = r),
        w k * K (k : ZMod q) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Vj0, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [(Finset.mem_filter.mp hk).2]
    _ = _ := Finset.sum_fiberwise I (fun k => (k : ZMod q)) _
private theorem V1yi (F : ZMod q → ℂ) :
    (∑ r : ZMod q, if IsUnit r then F r else 0) = ∑ u : (ZMod q)ˣ, F (u : ZMod q) := by
  classical
  rw [← Finset.sum_filter]
  have hs : (univ : Finset (ZMod q)).filter IsUnit =
      (univ : Finset (ZMod q)ˣ).map ⟨(↑), Units.val_injective⟩ := by
    ext r
    simp [IsUnit]
  rw [hs, Finset.sum_map]
  rfl
private theorem Vo4 (I : Finset ℕ) (w : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) :
    (∑ r : ZMod q, V95 I w r * χ r) =
      (∑ k ∈ I, w k * χ (k : ZMod q)) - (if χ = 1 then (I.card : ℂ) else 0) := by
  classical
  unfold V95
  simp only [sub_mul, Finset.sum_sub_distrib, Vpi]
  congr 1
  have hs : (∑ r : ZMod q, (if IsUnit r then (I.card : ℂ) / (q.totient : ℂ) else 0) * χ r) =
      ((I.card : ℂ) / (q.totient : ℂ)) * (∑ r : ZMod q, χ r) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hr : IsUnit r
    · simp [hr]
    · simp [hr, MulChar.map_nonunit χ hr]
  rw [hs]
  by_cases hχ : χ = 1
  · subst χ
    rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient, ite_eq_left rfl]
    exact div_mul_cancel₀ _ (by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne')
  · rw [MulChar.sum_eq_zero_of_ne_one hχ, mul_zero, ite_eq_right hχ]
private theorem V1t1 (I : Finset ℕ) (w : ℕ → ℂ) (a : ZMod q) :
    (∑ r : ZMod q, V95 I w r * ZMod.stdAddChar (a * r)) =
      ∑ k ∈ I, (w k * ZMod.stdAddChar (a * (k : ZMod q)) - V8a q a) := by
  classical
  simp only [V95, sub_mul, Finset.sum_sub_distrib, Vpi]
  congr 1
  calc
    _ = ((I.card : ℂ) / (q.totient : ℂ)) *
        (∑ r : ZMod q, if IsUnit r then ZMod.stdAddChar (a * r) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hr : IsUnit r <;> simp [hr]
    _ = _ := by
      rw [V1yi, Finset.sum_const, nsmul_eq_mul]
      unfold V8a
      simp only [div_eq_mul_inv]
      ring
theorem Vwd (I : Finset ℕ) (w : ℕ → ℂ)
    (P : ℝ) (_hP : 0 ≤ P)
    (hnon : (∑ k ∈ I.filter (fun k : ℕ => ¬ IsUnit (k : ZMod q)), ‖w k‖) ≤ P) :
    (∑ a : ZMod q,
      ‖∑ k ∈ I, (w k * ZMod.stdAddChar (a * (k : ZMod q)) - V8a q a)‖ ^ 2) ≤
      (q : ℝ) * ((∑ χ : DirichletCharacter ℂ q,
        ‖(∑ k ∈ I, w k * χ (k : ZMod q)) -
          (if χ = 1 then (I.card : ℂ) else 0)‖ ^ 2) / (q.totient : ℝ) + P ^ 2) := by
  have hφ : 0 < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hUnit : (∑ r ∈ (univ : Finset (ZMod q)).filter IsUnit, ‖V95 I w r‖ ^ 2) =
      (∑ χ : DirichletCharacter ℂ q,
        ‖(∑ k ∈ I, w k * χ (k : ZMod q)) -
          (if χ = 1 then (I.card : ℂ) else 0)‖ ^ 2) / (q.totient : ℝ) := by
    apply (eq_div_iff hφ.ne').mpr
    rw [mul_comm, ← Viq]
    simp_rw [Vo4]
  let V : Finset (ZMod q) := univ.filter (fun r => ¬ IsUnit r)
  have hV : (∑ r ∈ V, ‖V95 I w r‖) ≤ P := by
    calc
      _ ≤ ∑ r ∈ V, ∑ k ∈ I.filter (fun k : ℕ => (k : ZMod q) = r), ‖w k‖ := by
        refine sum_le_sum fun r hr => ?_
        have hr' : ¬ IsUnit r := (mem_filter.mp hr).2
        simpa [V95, hr', Vj0] using
          norm_sum_le (I.filter (fun k : ℕ => (k : ZMod q) = r)) w
      _ = ∑ k ∈ I.filter (fun k : ℕ => ¬ IsUnit (k : ZMod q)), ‖w k‖ := by
        rw [Finset.sum_fiberwise_eq_sum_filter]
        simp [V]
      _ ≤ _ := hnon
  have hNonUnit : (∑ r ∈ V, ‖V95 I w r‖ ^ 2) ≤ P ^ 2 :=
    (Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)).trans
      (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hV 2)
  simp_rw [← V1t1]
  rw [V1u9]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q)
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := (univ : Finset (ZMod q))) (p := IsUnit), hUnit]
  exact add_le_add le_rfl hNonUnit
def window (N h m : ℕ) : Finset ℕ :=
  (range N).filter (fun k => m+1-h ≤ k ∧ k ≤ m)
noncomputable def Via (q : ℕ) [NeZero q] (I : Finset ℕ) : ℝ :=
  ∑ χ : DirichletCharacter ℂ q,
    ‖(∑ k ∈ I, V76 k * χ (k : ZMod q)) -
      (if χ = 1 then (I.card : ℂ) else 0)‖ ^ 2
noncomputable def Ve3 (q : ℕ) [NeZero q] (N h : ℕ) : ℝ :=
  ∑ m ∈ range (N+h), Via q (window N h m)
noncomputable def Vsn (q : ℕ) [NeZero q] (N : ℕ) (δ : ℝ) : ℝ :=
  ∑ a : ZMod q, ∫ β in (-δ)..δ, ‖poly N (Vll a) β‖ ^ 2
theorem V14p (N h m : ℕ) :
    (∑ a : ZMod q, ‖moving N h (Vll a) m‖ ^ 2) ≤
      (q:ℝ)*(Via q (window N h m)/(q.totient:ℝ) + (Real.log (q:ℝ))^2) := by
  simp only [Vcr.V21l]
  exact Vwd (q:=q) (window N h m) V76
    (Real.log (q:ℝ)) (Real.log_nonneg (by exact_mod_cast NeZero.pos q))
    (V54.Vx9 _)
theorem V1an (N h : ℕ) (δ : ℝ)
    (hh : 0 < h) (hδ : 0 ≤ δ) (hwidth : 6*(h:ℝ)*δ ≤ 1) :
    (h:ℝ)^2/4 * Vsn q N δ ≤
      ((q:ℝ)/(q.totient:ℝ))*Ve3 q N h +
        (q:ℝ)*((N+h:ℕ):ℝ)*(Real.log (q:ℝ))^2 := by
  unfold Vsn
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ a : ZMod q, ∑ m ∈ range (N+h), ‖moving N h (Vll a) m‖^2 :=
      sum_le_sum fun a _ => Vcr.V1zo N h (Vll a) δ hh hδ hwidth
    _ = ∑ m ∈ range (N+h), ∑ a : ZMod q, ‖moving N h (Vll a) m‖^2 :=
      Finset.sum_comm
    _ ≤ ∑ m ∈ range (N+h), (q:ℝ)*
        (Via q (window N h m)/(q.totient:ℝ) + (Real.log (q:ℝ))^2) :=
      sum_le_sum fun m _ => V14p N h m
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.sum_div, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Ve3]
      ring
theorem V106 (N h : ℕ) (δ : ℝ)
    (hh : 0 < h) (hδ : 0 ≤ δ) (hwidth : 6*(h:ℝ)*δ ≤ 1) :
    Vsn q N δ ≤
      (4*(q:ℝ)/((h:ℝ)^2*(q.totient:ℝ)))*Ve3 q N h +
        (4*(q:ℝ)*((N+h:ℕ):ℝ)/(h:ℝ)^2)*(Real.log (q:ℝ))^2 := by
  have hbound := V1an (q:=q) N h δ hh hδ hwidth
  have hhR : 0 < (h:ℝ) := by exact_mod_cast hh
  have hφR : 0 < (q.totient:ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  apply le_of_mul_le_mul_left ?_ (show 0 < (h:ℝ)^2/4 by positivity)
  calc
    _ ≤ _ := hbound
    _ = _ := by field_simp
end V73
end
section
open Finset
open scoped BigOperators Classical
namespace V7d
open V54 (V76 Viq)
open V73 (window Via Ve3)
variable {q : ℕ} [NeZero q]
private noncomputable def Vj0 (I : Finset ℕ) (w : ℕ → ℂ) (r : ZMod q) : ℂ :=
  ∑ k ∈ I.filter (fun k : ℕ => (k : ZMod q) = r), w k
private noncomputable def V95 (I : Finset ℕ) (w : ℕ → ℂ) (r : ZMod q) : ℂ :=
  Vj0 I w r - if IsUnit r then (I.card : ℂ) / (q.totient : ℂ) else 0
private theorem Vpi (I : Finset ℕ) (w : ℕ → ℂ) (K : ZMod q → ℂ) :
    (∑ r : ZMod q, Vj0 I w r * K r) =
      ∑ k ∈ I, w k * K (k : ZMod q) := by
  calc
    _ = ∑ r : ZMod q, ∑ k ∈ I.filter (fun k : ℕ => (k : ZMod q) = r),
        w k * K (k : ZMod q) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Vj0, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [(Finset.mem_filter.mp hk).2]
    _ = _ := Finset.sum_fiberwise I (fun k => (k : ZMod q)) _
private theorem V1yi (F : ZMod q → ℂ) :
    (∑ r : ZMod q, if IsUnit r then F r else 0) = ∑ u : (ZMod q)ˣ, F (u : ZMod q) := by
  classical
  rw [← Finset.sum_filter]
  have hs : (univ : Finset (ZMod q)).filter IsUnit =
      (univ : Finset (ZMod q)ˣ).map ⟨(↑), Units.val_injective⟩ := by
    ext r
    simp [IsUnit]
  rw [hs, Finset.sum_map]
  rfl
private theorem Vo4 (I : Finset ℕ) (w : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) :
    (∑ r : ZMod q, V95 I w r * χ r) =
      (∑ k ∈ I, w k * χ (k : ZMod q)) - (if χ = 1 then (I.card : ℂ) else 0) := by
  classical
  unfold V95
  simp only [sub_mul, Finset.sum_sub_distrib, Vpi]
  congr 1
  have hs : (∑ r : ZMod q, (if IsUnit r then (I.card : ℂ) / (q.totient : ℂ) else 0) * χ r) =
      ((I.card : ℂ) / (q.totient : ℂ)) * (∑ r : ZMod q, χ r) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hr : IsUnit r
    · simp [hr]
    · simp [hr, MulChar.map_nonunit χ hr]
  rw [hs]
  by_cases hχ : χ = 1
  · subst χ
    rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient, ite_eq_left rfl]
    exact div_mul_cancel₀ _ (by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne')
  · rw [MulChar.sum_eq_zero_of_ne_one hχ, mul_zero, ite_eq_right hχ]
noncomputable def V6t (q : ℕ) [NeZero q] (I : Finset ℕ) (r : ZMod q) : ℝ :=
  ‖Vj0 I V76 r - (I.card : ℂ) / (q.totient : ℂ)‖
theorem V1jr (I : Finset ℕ) :
    Via q I = (q.totient : ℝ) *
      ∑ r ∈ (univ : Finset (ZMod q)).filter IsUnit, ‖V95 I V76 r‖^2 := by
  rw [← Viq]
  simp_rw [Vo4]
  rfl
private theorem V1uj (I : Finset ℕ) (w : ℕ → ℂ) :
    (∑ r ∈ (univ : Finset (ZMod q)).filter IsUnit, ‖Vj0 I w r‖) ≤
      ∑ k ∈ I, ‖w k‖ := by
  calc
    _ ≤ ∑ r ∈ (univ : Finset (ZMod q)).filter IsUnit,
        ∑ k ∈ I.filter (fun k : ℕ => (k : ZMod q) = r), ‖w k‖ := by
      exact sum_le_sum fun r _ => norm_sum_le _ _
    _ ≤ ∑ r : ZMod q, ∑ k ∈ I.filter (fun k : ℕ => (k : ZMod q) = r), ‖w k‖ := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro r _ _
      positivity
    _ = _ := Finset.sum_fiberwise I (fun k => (k : ZMod q)) (fun k => ‖w k‖)
private theorem V1xm (I : Finset ℕ) (w : ℕ → ℂ) :
    (∑ r ∈ (univ : Finset (ZMod q)).filter IsUnit, ‖V95 I w r‖) ≤
      (∑ k ∈ I, ‖w k‖) + I.card := by
  have hφ : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hU : (univ : Finset (ZMod q)).filter IsUnit =
      (univ : Finset (ZMod q)ˣ).map ⟨(↑), Units.val_injective⟩ := by
    ext r
    simp [IsUnit]
  have hcard : ((univ : Finset (ZMod q)).filter IsUnit).card = q.totient := by
    rw [hU, card_map, card_univ, ZMod.card_units_eq_totient]
  have hmain : (∑ _r ∈ (univ : Finset (ZMod q)).filter IsUnit,
      ‖(I.card : ℂ) / (q.totient : ℂ)‖) = (I.card : ℝ) := by
    rw [sum_const, nsmul_eq_mul, hcard]
    simp only [norm_div, norm_natCast]
    field_simp
  calc
    _ ≤ ∑ r ∈ (univ : Finset (ZMod q)).filter IsUnit,
        (‖Vj0 I w r‖ + ‖(I.card : ℂ) / (q.totient : ℂ)‖) := by
      apply sum_le_sum
      intro r hr
      simpa only [V95, ite_eq_left (mem_filter.mp hr).2] using
        norm_sub_le (Vj0 I w r) ((I.card : ℂ) / (q.totient : ℂ))
    _ = (∑ r ∈ (univ : Finset (ZMod q)).filter IsUnit, ‖Vj0 I w r‖) + I.card := by
      rw [sum_add_distrib, hmain]
    _ ≤ _ := by linarith [V1uj (q := q) I w]
theorem V1jq (I : Finset ℕ) (E : ℝ) (hE : 0 ≤ E)
    (hAP : ∀ r : ZMod q, IsUnit r → V6t q I r ≤ E) :
    Via q I ≤ (q.totient : ℝ) * E * ((∑ k ∈ I, ‖V76 k‖) + I.card) := by
  rw [V1jr]
  calc
    _ ≤ (q.totient : ℝ) *
        (∑ r ∈ (univ : Finset (ZMod q)).filter IsUnit, E * ‖V95 I V76 r‖) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply sum_le_sum
      intro r hr
      have hu := (mem_filter.mp hr).2
      have hb : ‖V95 I V76 r‖ ≤ E := by
        simpa only [V95, ite_eq_left hu, V6t] using hAP r hu
      simpa only [pow_two] using mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ = (q.totient : ℝ) * E *
        (∑ r ∈ (univ : Finset (ZMod q)).filter IsUnit, ‖V95 I V76 r‖) := by
      rw [← mul_sum, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (V1xm I V76) (by positivity)
private theorem Vod (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) :
    ‖V76 k‖ ≤ Real.log (n : ℝ) := by
  unfold V76
  by_cases hp : k.Prime
  · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hp.one_lt.le
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hp.pos
    have hkn : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
    simp only [hp, ite_true, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg hk1)]
    exact Real.log_le_log hk0 hkn
  · simp only [hp, ite_false, Complex.ofReal_zero, norm_zero]
    exact Real.log_nonneg (by exact_mod_cast hn)
theorem V1z7 (n : ℕ) (hn : 1 ≤ n) (I : Finset ℕ)
    (hI : I ⊆ range (n+1)) (E : ℝ) (hE : 0 ≤ E)
    (hAP : ∀ r : ZMod q, IsUnit r → V6t q I r ≤ E) :
    Via q I ≤ (q.totient : ℝ) * I.card * (1 + Real.log (n : ℝ)) * E := by
  have hmass : (∑ k ∈ I, ‖V76 k‖) ≤ (I.card : ℝ) * Real.log (n : ℝ) := by
    calc
      _ ≤ ∑ _k ∈ I, Real.log (n : ℝ) := by
        exact sum_le_sum fun k hk => Vod n k hn (by have := mem_range.mp (hI hk); omega)
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  calc
    _ ≤ (q.totient : ℝ) * E * ((∑ k ∈ I, ‖V76 k‖) + I.card) :=
      V1jq I E hE hAP
    _ ≤ (q.totient : ℝ) * E * ((I.card : ℝ) * Real.log (n : ℝ) + I.card) := by
      gcongr
    _ = _ := by ring
theorem V1mn (N h m : ℕ) : (window N h m).card ≤ h := by
  have hsub : window N h m ⊆ Icc (m+1-h) m := by
    intro k hk
    exact mem_Icc.mpr (mem_filter.mp hk).2
  calc
    _ ≤ (Icc (m+1-h) m).card := card_le_card hsub
    _ ≤ h := by rw [Nat.card_Icc]; omega
theorem V1m8 (n h : ℕ) (hn : 1 ≤ n) (E : ℕ → ℝ)
    (hE : ∀ m ∈ range (n+1+h), 0 ≤ E m)
    (hAP : ∀ m ∈ range (n+1+h), ∀ r : ZMod q, IsUnit r →
      V6t q (window (n+1) h m) r ≤ E m) :
    Ve3 q (n+1) h ≤
      (q.totient : ℝ) * h * (1 + Real.log (n : ℝ)) *
        ∑ m ∈ range (n+1+h), E m := by
  have hL : 0 ≤ 1 + Real.log (n : ℝ) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast hn)
    linarith
  unfold Ve3
  calc
    _ ≤ ∑ m ∈ range (n+1+h), (q.totient : ℝ) * h * (1+Real.log (n : ℝ)) * E m := by
      apply sum_le_sum
      intro m hm
      have hb := V1z7 n hn (window (n+1) h m)
        (filter_subset _ _) (E m) (hE m hm) (hAP m hm)
      apply hb.trans
      have hc : ((window (n+1) h m).card : ℝ) ≤ h := by exact_mod_cast V1mn (n+1) h m
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _)) hL) (hE m hm)
    _ = _ := by rw [← mul_sum]
end V7d
end
section
open Filter Finset MeasureTheory
open scoped Topology Interval Classical
namespace Vuh
open V20 (narrow cutoff width)
open V19 (centers cell)
open V31 (phase Vi3 Vb2)
open Va2 (model Ve5)
open V8k (V13w)
noncomputable def V1h4 (n : ℕ) : ℝ :=
  ∑ i ∈ centers (narrow n), ∫ t in cell n (narrow n) (width n) i,
    ‖Vi3 n t-model n i t‖^2
open V18m (V1kw V1zp Vkq)
end Vuh
end
section
open Filter Finset MeasureTheory
open scoped Topology Interval Classical
namespace Vmk
open V20 (narrow cutoff width)
open V19 (radius centers cell cap center)
open V24 (mass kernel)
open Va2 (model)
open V4o (Vc5 Vba)
open Vr (V3f)
noncomputable def factor (q : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius q : ℝ) / (q.totient : ℝ)) ^ 2
theorem V21p (q : ℕ) : 0 ≤ factor q := sq_nonneg _
theorem V1uq (q a : ℕ) : (Vc5 0 q a).re = factor q := by
  simp [Vc5, factor, V31.phase,
    ← Complex.ofReal_intCast, ← Complex.ofReal_natCast,
    ← Complex.ofReal_div, ← Complex.ofReal_pow]
theorem V21k (n q a : ℕ) (t : ℝ) :
    ‖model n (q,a) t‖ ^ 2 = factor q * ‖kernel n (t-center (q,a))‖ ^ 2 := by
  unfold model factor
  rw [norm_mul, mul_pow]
  congr 1
  have hc : (ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) =
      (((ArithmeticFunction.moebius q : ℝ) / (q.totient : ℝ) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hc, Complex.norm_real, Real.norm_eq_abs, sq_abs]
theorem V1p2 (n Q H q a : ℕ) :
    (∫ t in cell n Q H (q,a), ‖model n (q,a) t‖ ^ 2) =
      factor q * (∫ t in cell n Q H (q,a), ‖kernel n (t-center (q,a))‖ ^ 2) := by
  simp_rw [V21k]
  exact integral_const_mul _ _
theorem V21g (q : ℕ) :
    (∑ _a ∈ (range q).filter (fun a => Nat.Coprime a q), factor q) =
      (V3f q 0).re := by
  have h := congrArg Complex.re (V4o.V1bq 0 q)
  simpa only [Complex.re_sum, V1uq] using h
theorem V11l (q : ℕ) : 0 ≤ (V3f q 0).re := by
  rw [← V21g]
  exact sum_nonneg fun _ _ => V21p q
theorem V1sv {n Q H U : ℕ} (hQH : Q ≤ H) (hHn : H ≤ n) :
    (∑ i ∈ centers U, ∫ t in cell n Q H i, ‖model n i t‖ ^ 2) =
      ∑ q ∈ Icc 1 U, (V3f q 0).re * Vba n Q H q := by
  rw [V19.V1mo]
  refine sum_congr rfl fun q hq => ?_
  have hq1 := (mem_Icc.mp hq).1
  by_cases hqOne : q = 1
  · subst q
    have hf : ((range (1+1)).filter (fun a : ℕ => Nat.Coprime a 1)) =
        ({0,1} : Finset ℕ) := by
      ext a
      simp only [mem_filter, mem_range, Nat.coprime_one_right_iff, and_true,
        mem_insert, mem_singleton]
      omega
    rw [hf, sum_pair (by decide : (0:ℕ) ≠ 1)]
    simp only [V1p2, show factor 1 = 1 by norm_num [factor], one_mul,
      V4g.V198 hQH hHn,
      Vr.V13x, Complex.one_re, Vba]
  · have hq2 : 2 ≤ q := by omega
    have hf : ((range (q+1)).filter (fun a => Nat.Coprime a q)) =
        (range q).filter (fun a => Nat.Coprime a q) := by
      ext a
      simp only [mem_filter, mem_range]
      constructor
      · rintro ⟨haq,hcop⟩
        have hne : a ≠ q := by
          intro heq
          subst a
          have h : q = 1 := by simpa [Nat.Coprime] using hcop
          exact hqOne h
        exact ⟨lt_of_le_of_ne (Nat.lt_succ_iff.mp haq) hne,hcop⟩
      · rintro ⟨haq,hcop⟩
        exact ⟨haq.trans (Nat.lt_succ_self q),hcop⟩
    rw [hf, ← V21g, Finset.sum_mul]
    refine sum_congr rfl fun a ha => ?_
    obtain ⟨haq,hcop⟩ := mem_filter.mp ha
    rw [V1p2, V4g.V1ei hQH hHn hq2
      (mem_range.mp haq).le hcop, Vba]
noncomputable def V1ni (n : ℕ) : ℝ :=
  ∑ i ∈ centers (narrow n), ∫ t in cell n (narrow n) (width n) i,
    ‖model n i t‖ ^ 2
theorem V1wv {n Q H : ℕ} (hn : 0 < n) (hQ : 1 ≤ Q)
    (hQH : Q ≤ H) (hH : 24*H ≤ n) :
    (∑ i ∈ centers Q, ∫ t in cell n Q H i, ‖model n i t‖ ^ 2) ≤
      (Vm.V2i / 2) * (n : ℝ) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hQR : 0 < (Q:ℝ) := by exact_mod_cast hQ
  have hHn : H ≤ n := by omega
  have hHQ : 24*Q ≤ n := (Nat.mul_le_mul_left 24 hQH).trans hH
  have hHpos : 0 < H := hQ.trans hQH
  rw [V1sv hQH hHn]
  have hmass (q : ℕ) (hq : q ∈ Icc 1 Q) :
      Vba n Q H q ≤ (q:ℝ)*(n:ℝ)/(2*(Q:ℝ)) := by
    obtain ⟨hq0,hqQ⟩ := mem_Icc.mp hq
    obtain ⟨hwide,_⟩ := V72.Vdy n H q hn hHpos hH
    obtain ⟨_,hnarrow⟩ := V72.Vdy n Q q hn hQ hHQ
    rw [max_eq_right hq0] at hnarrow
    unfold V72.normalized at hwide hnarrow
    rw [max_eq_right hq0] at hwide hnarrow
    unfold Vba
    rw [ite_eq_left hqQ]
    have h₂ := mul_le_mul_of_nonneg_right hnarrow hnR.le
    field_simp [hnR.ne'] at h₂
    have hw : mass n (radius n H q) ≤ (n:ℝ)+1 := by
      apply (div_le_div_iff_of_pos_right hnR).mp
      linarith only [hwide]
    have hl : (n:ℝ)+1-mass n (radius n Q q) ≤ (q:ℝ)*(n:ℝ)/(2*(Q:ℝ)) := by
      apply (le_div_iff₀ (by positivity : 0 < 2*(Q:ℝ))).mpr
      nlinarith [h₂]
    linarith
  calc
    _ ≤ ∑ q ∈ Icc 1 Q, (V3f q 0).re * ((q:ℝ)*(n:ℝ)/(2*(Q:ℝ))) :=
      sum_le_sum fun q hq => mul_le_mul_of_nonneg_left (hmass q hq)
        (V11l q)
    _ = (∑ q ∈ Icc 1 Q, |Vm.F 0 q|) * ((n:ℝ)/(2*(Q:ℝ))) := by
      rw [sum_mul]
      apply sum_congr rfl
      intro q hq
      change _ = |(q:ℝ)*(V3f q 0).re| * _
      rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg q) (V11l q))]
      ring
    _ ≤ (Vm.V2i*(Q:ℝ))*((n:ℝ)/(2*(Q:ℝ))) :=
      mul_le_mul_of_nonneg_right (V1s.Vq3 0 Q) (by positivity)
    _ = _ := by field_simp
theorem V1lq :
    ∀ᶠ n : ℕ in atTop, V1ni n ≤ (Vm.V2i/2)*(n:ℝ) := by
  filter_upwards [V20.Vhd] with n hgeo
  obtain ⟨hn,hQ,hQU,_,hH,_⟩ := hgeo
  exact V1wv (by omega) hQ
    (hQU.trans (V20.Vrx n hQ)) hH
end Vmk
end
section
open Filter Finset MeasureTheory
open scoped Topology Interval Classical
namespace V8j
open V20 (narrow cutoff width)
open V19 (centers cell)
open V31 (phase Vi3)
open Va2 (model Ve5)
open V8k (V13w)
open V18m (V1kw V1zp Vkq)
open Vuh (V1h4)
open Vmk (V1ni)
theorem V14j (z w : ℂ) {η : ℝ} (hη : 0 < η) :
    ‖z^2-w^2‖ ≤ (1+1/η)*‖z-w‖^2 + η*‖w‖^2 := by
  have hfactor : z^2-w^2 = (2:ℂ)*w*(z-w)+(z-w)^2 := by ring
  have hmain : 2*‖w‖*‖z-w‖ ≤ (1/η)*‖z-w‖^2 + η*‖w‖^2 := by
    apply le_of_mul_le_mul_right ?_ hη
    have hsq := sq_nonneg (η*‖w‖-‖z-w‖)
    field_simp
    nlinarith only [hsq]
  calc
    _ ≤ ‖(2:ℂ)*w*(z-w)‖ + ‖(z-w)^2‖ := hfactor ▸ norm_add_le _ _
    _ = 2*‖w‖*‖z-w‖+‖z-w‖^2 := by simp [norm_pow]
    _ ≤ _ := by linarith
theorem Vvf {ι : Type*} (s : Finset ι)
    (D : ι → Set ℝ) (hsub : ∀ i∈s, D i ⊆ Set.Ioc 0 1)
    (S : ℝ → ℂ) (M : ι → ℝ → ℂ) (osc : ℝ → ℂ)
    (hS : Continuous S) (hM : ∀ i∈s, Continuous (M i))
    (hosc : Continuous osc) (hnorm : ∀ t, ‖osc t‖ ≤ 1) {η : ℝ} (hη : 0 < η) :
    (∑ i∈s, ‖∫ t in D i, (S t^2-M i t^2)*osc t‖) ≤
      (1+1/η)*(∑ i∈s, ∫ t in D i, ‖S t-M i t‖^2) +
      η*(∑ i∈s, ∫ t in D i, ‖M i t‖^2) := by
  have hlocal (i : ι) (hi : i∈s) :
      ‖∫ t in D i, (S t^2-M i t^2)*osc t‖ ≤
      (1+1/η)*(∫ t in D i, ‖S t-M i t‖^2)+η*(∫ t in D i, ‖M i t‖^2) := by
    have hC : Continuous (fun t => ‖S t-M i t‖^2) :=
      ((hS.sub (hM i hi)).norm.pow 2)
    have hG : Continuous (fun t => ‖M i t‖^2) := (hM i hi).norm.pow 2
    have hCi : IntegrableOn (fun t => ‖S t-M i t‖^2) (D i) volume :=
      (hC.intervalIntegrable 0 1).1.mono_set (hsub i hi)
    have hGi : IntegrableOn (fun t => ‖M i t‖^2) (D i) volume :=
      (hG.intervalIntegrable 0 1).1.mono_set (hsub i hi)
    have hF : Continuous (fun t => (S t^2-M i t^2)*osc t) :=
      ((hS.pow 2).sub ((hM i hi).pow 2)).mul hosc
    have hFi : IntegrableOn (fun t => ‖(S t^2-M i t^2)*osc t‖) (D i) volume :=
      (hF.norm.intervalIntegrable 0 1).1.mono_set (hsub i hi)
    calc
      _ ≤ ∫ t in D i, ‖(S t^2-M i t^2)*osc t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in D i, (1+1/η)*‖S t-M i t‖^2+η*‖M i t‖^2 := by
        apply integral_mono hFi ((hCi.const_mul _).add (hGi.const_mul _))
        intro t
        change ‖(S t^2-M i t^2)*osc t‖ ≤ (1+1/η)*‖S t-M i t‖^2+η*‖M i t‖^2
        rw [norm_mul]
        exact (mul_le_of_le_one_right (norm_nonneg _) (hnorm t)).trans
          (V14j (S t) (M i t) hη)
      _ = _ := by
        rw [integral_add (hCi.const_mul _) (hGi.const_mul _),
          integral_const_mul, integral_const_mul]
  calc
    _ ≤ ∑ i∈s, ((1+1/η)*(∫ t in D i, ‖S t-M i t‖^2)+
        η*(∫ t in D i, ‖M i t‖^2)) := Finset.sum_le_sum hlocal
    _ = _ := by rw [sum_add_distrib,mul_sum,mul_sum]
theorem V1w6 {ε C x B G : ℝ} (hε : 0 < ε) (hC : 0 ≤ C) (hx : 0 ≤ x)
    (hB : B ≤ (ε^2/(2*(ε+2*(C+1))))*x) (hG : G ≤ C*x) :
    (1+1/(ε/(2*(C+1))))*B+(ε/(2*(C+1)))*G ≤ ε*x := by
  have hCp : 0 < C+1 := by linarith
  have hη : 0 < ε/(2*(C+1)) := by positivity
  have hb := mul_le_mul_of_nonneg_left hB (show 0 ≤ 1+1/(ε/(2*(C+1))) by positivity)
  have he := mul_le_mul_of_nonneg_left hG hη.le
  have hbeq : (1+1/(ε/(2*(C+1))))*((ε^2/(2*(ε+2*(C+1))))*x) = ε*x/2 := by
    field_simp
  rw [hbeq] at hb
  have hcost : (ε/(2*(C+1)))*C ≤ ε/2 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 2*(C+1))).mpr
    nlinarith
  have hlast := mul_le_mul_of_nonneg_right hcost hx
  have he' : (ε/(2*(C+1)))*G ≤ ε*x/2 := by
    apply he.trans
    calc
      _ = ((ε/(2*(C+1)))*C)*x := by ring
      _ ≤ (ε/2)*x := hlast
      _ = _ := by ring
  linarith
def V3d (B : ℕ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, B n ≤ δ*(n:ℝ)
theorem V177 (hEnergy : V3d V1h4) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ‖V1kw n - V1zp n‖ ≤ ε*(n:ℝ) := by
  let C := Vm.V2i/2
  have hC : 0 ≤ C := by unfold C; exact div_nonneg (Real.exp_pos _).le (by norm_num)
  have hδ : 0 < ε^2/(2*(ε+2*(C+1))) := by positivity
  filter_upwards [V20.Vhd,
    Vmk.V1lq, hEnergy _ hδ] with n hgeo hModel hErr
  obtain ⟨hn,hQ,hQU,_,_,hbudget⟩ := hgeo
  have hη : 0 < ε/(2*(C+1)) := by positivity
  have hQH : narrow n ≤ width n := hQU.trans (V20.Vrx n hQ)
  have hbudgetLow : 2 * width n * narrow n < n :=
    (Nat.mul_le_mul_left (2 * width n) hQU).trans_lt hbudget
  let η := ε/(2*(C+1))
  let osc (t : ℝ) := phase (-(n:ℝ)*t)
  have hOsc : Continuous osc := by unfold osc phase; fun_prop
  have hS : Continuous (Vi3 n) := by unfold Vi3 phase; fun_prop
  have hF : Continuous (V13w n) := (hS.pow 2).mul hOsc
  rw [V1kw, V19.V1ff le_rfl hQH hbudgetLow _ hF,
    V1zp, ← Finset.sum_sub_distrib]
  have hsplit (i : ℕ × ℕ) :
      (∫ t in cell n (narrow n) (width n) i, V13w n t) -
        (∫ t in cell n (narrow n) (width n) i, model n i t ^ 2 * osc t) =
      ∫ t in cell n (narrow n) (width n) i,
        (Vi3 n t ^ 2 - model n i t ^ 2) * osc t := by
    have hpart : cell n (narrow n) (width n) i ⊆ Set.Ioc (0:ℝ) 1 :=
      Set.inter_subset_right
    have h₁ : IntegrableOn (V13w n) (cell n (narrow n) (width n) i) volume :=
      (hF.intervalIntegrable 0 1).1.mono_set hpart
    have hm : Continuous (fun t => model n i t ^ 2 * osc t) :=
      ((Ve5 n i).pow 2).mul hOsc
    have h₂ : IntegrableOn (fun t => model n i t ^ 2 * osc t)
        (cell n (narrow n) (width n) i) volume :=
      (hm.intervalIntegrable 0 1).1.mono_set hpart
    rw [← integral_sub h₁ h₂]
    simp [V13w, osc, sub_mul]
  dsimp only [osc] at hsplit
  simp_rw [hsplit]
  apply (norm_sum_le _ _).trans
  apply (Vvf
    (centers (narrow n)) (cell n (narrow n) (width n))
    (fun _ _ => Set.inter_subset_right)
    (Vi3 n) (model n) osc hS (fun i _ => Ve5 n i) hOsc
    (fun t => le_of_eq (Complex.norm_exp_ofReal_mul_I (2*Real.pi*(-(n:ℝ)*t)))) hη).trans
  simpa only [η, V1h4, V1ni] using
    (V1w6 hε hC (Nat.cast_nonneg n) hErr hModel)
theorem Vr6 (hEnergy : V3d V1h4) :
  let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowSkirt := fun n : ℕ => intervalIntegral (fun t => (lowWideArcs n \ arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (lowSkirt n).re := by
  dsimp only
  intro ε hε
  have he : 0 < ε/2 := by positivity
  have h := (V177 hEnergy (ε/2) he).and
    (Vkq (ε/2) he)
  obtain ⟨N,hN⟩ := eventually_atTop.1 h
  refine ⟨N, ?_⟩
  intro n hn hEven
  obtain ⟨hErr,hModel⟩ := hN n hn
  have hb := (abs_le.mp ((Complex.abs_re_le_norm _).trans hErr)).1
  rw [Complex.sub_re] at hb
  have hM : -(ε/2) * (n:ℝ) ≤ (V1zp n).re := hModel hEven
  have hsum := add_le_add hb hM
  rw [sub_add_cancel] at hsum
  change -(ε * (n:ℝ)) ≤ (V1kw n).re
  calc
    -(ε * (n:ℝ)) = -(ε/2 * (n:ℝ)) + -(ε/2) * (n:ℝ) := by ring
    _ ≤ _ := hsum
end V8j
end
section
open Filter Finset MeasureTheory
open scoped Topology Interval Classical
namespace V8i
open V20 (narrow cutoff width)
open V19 (radius center centers cell)
open V31 (phase Vi3)
open Va2 (model)
open Vcr (poly)
open Vf0 (Vll V1bv)
open V73 (Ve3 Vsn)
open Vuh (V1h4)
open V8j (V3d)
noncomputable def V15 (n q : ℕ) : ℕ :=
  ⌊1/(12*radius n (width n) q)⌋₊
noncomputable def Vph (n q : ℕ) : ℝ :=
  if hq : q=0 then 0 else
    letI : NeZero q := ⟨hq⟩
    (q:ℝ)/((V15 n q:ℝ)^2*(q.totient:ℝ))*
      Ve3 q (n+1) (V15 n q)
noncomputable def Vo0 (n : ℕ) : ℝ :=
  ∑ q∈Icc 1 (narrow n), Vph n q
noncomputable def Vj6 (n : ℕ) : ℝ :=
  ∑ q∈Icc 1 (narrow n),
    (8*(q:ℝ)*((n+1+V15 n q:ℕ):ℝ)/(V15 n q:ℝ)^2)*
      (Real.log (q:ℝ))^2
theorem Vo6 (N : ℕ) (δ : ℝ) (hδ : 0<δ)
    (hsmall : δ≤1/24) (hlarge : 1≤(N:ℝ)*δ) :
    let h := ⌊1/(12*δ)⌋₊
    0<h ∧ 6*(h:ℝ)*δ≤1 ∧ (h:ℝ)≤(N:ℝ) ∧ 1/(h:ℝ)^2≤(24*δ)^2 := by
  let h := ⌊1/(12*δ)⌋₊
  have hz : 0 < 12*δ := by positivity
  have hrec : 2≤1/(12*δ) := (le_div_iff₀ hz).2 (by linarith)
  have hh : 0<h := lt_of_lt_of_le (by decide : 0<2) (Nat.le_floor (by simpa using hrec))
  have hhlo : 1/(24*δ)≤(h:ℝ) := by
    have hf := Nat.lt_floor_add_one (1/(12*δ))
    change 1/(12*δ)<(h:ℝ)+1 at hf
    have heq : 1/(24*δ)=(1/(12*δ))/2 := by ring
    rw [heq]
    linarith
  have hhhi : (h:ℝ)≤1/(12*δ) := Nat.floor_le (by positivity)
  have hwidth : 6*(h:ℝ)*δ≤1 := by
    have h := (le_div_iff₀ hz).1 hhhi
    nlinarith only [h]
  have hhN : (h:ℝ)≤(N:ℝ) := hhhi.trans <|
    (div_le_iff₀ hz).2 (by nlinarith only [hlarge])
  have hhR : 0<(h:ℝ) := by exact_mod_cast hh
  have hscale : 1≤(24*δ)*(h:ℝ) := by
    have h := (div_le_iff₀ (by positivity : 0<24*δ)).1 hhlo
    nlinarith only [h]
  have hinv : 1/(h:ℝ)^2≤(24*δ)^2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hhR)).2
    nlinarith [sq_nonneg ((24*δ)*(h:ℝ)-1)]
  exact ⟨hh,hwidth,hhN,hinv⟩
theorem V160 (n q : ℕ) [NeZero q]
    (hn : 0<n) (hH : 0<width n) :
    (∑ a∈(range (q+1)).filter (fun a => a.Coprime q),
      ∫ t in cell n (narrow n) (width n) (q,a),
        ‖Vi3 n t-model n (q,a) t‖^2) ≤
      2*Vsn q (n+1) (radius n (width n) q) := by
  let r := radius n (width n) q
  have hq0 : 0<q := NeZero.pos q
  have hr : 0<r := by unfold r radius; positivity
  let E (a : ZMod q) := ∫ β in (-r)..r, ‖poly (n+1) (Vll a) β‖^2
  have hE (a : ZMod q) : 0≤E a :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => by positivity)
  have hcell (a : ℕ) (ha : a∈(range (q+1)).filter (fun a => a.Coprime q)) :
      (∫ t in cell n (narrow n) (width n) (q,a),
        ‖Vi3 n t-model n (q,a) t‖^2) ≤ E (a:ZMod q) := by
    have hunit := (ZMod.isUnit_iff_coprime a q).2 (mem_filter.mp ha).2
    let G (β : ℝ) := ‖poly (n+1) (Vll (a:ZMod q)) β‖^2
    have hGc : Continuous G := by unfold G poly phase; fun_prop
    have hG₀ (t : ℝ) : 0≤G t := by unfold G; positivity
    have ht (t : ℝ) : G (t-center (q,a))=‖Vi3 n t-model n (q,a) t‖^2 := by
      unfold G
      rw [V1bv, V54.V1ol _ hunit]
      unfold model
      have ha' : ((a:ℝ)/q)+(t-center (q,a))=t := by unfold center; ring
      rw [ha']
    have hc := V4g.V23k n (narrow n) (width n) (q,a) G hGc hG₀
    simpa only [ht,G,E,r] using hc
  calc
    _ ≤ ∑ a∈(range (q+1)).filter (fun a => a.Coprime q), E (a:ZMod q) :=
      Finset.sum_le_sum hcell
    _ ≤ _ := V19.V1qp q E hE
theorem Vkp : ∀ᶠ n : ℕ in atTop,
    2≤n ∧ 0<width n ∧ ∀ q∈Icc 1 (narrow n),
      1≤q ∧ q≤n ∧ 0<radius n (width n) q ∧
      radius n (width n) q≤1/24 ∧
      1≤((n+1:ℕ):ℝ)*radius n (width n) q := by
  filter_upwards [V20.Vhd] with n hgeo
  obtain ⟨hn,hQ,hQU,hUn,hHn,_⟩ := hgeo
  have hUH := V20.Vrx n hQ
  have hU₀ : 1≤cutoff n := hQ.trans hQU
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  have hnpos : 0<(n:ℝ) := by linarith
  have hH : 0<width n := hU₀.trans hUH
  have hHnR : 24*(width n:ℝ)≤(n:ℝ) := by exact_mod_cast hHn
  refine ⟨hn,hH,?_⟩
  intro q hq
  obtain ⟨hq1,hqQ⟩ := mem_Icc.mp hq
  have hqU := hqQ.trans hQU
  have hqR : (1:ℝ)≤q := by exact_mod_cast hq1
  have hqpos : 0<(q:ℝ) := by linarith
  have hr : 0<radius n (width n) q := by unfold radius; positivity
  refine ⟨hq1,hqU.trans hUn,hr,?_,?_⟩
  · apply (div_le_iff₀ (by positivity : 0<(q:ℝ)*(n:ℝ))).2
    have hqn := mul_le_mul_of_nonneg_right hqR hnpos.le
    nlinarith only [hqn,hHnR]
  · have hqH : (q:ℝ)≤(width n:ℝ) := by exact_mod_cast hqU.trans hUH
    have hprod := mul_le_mul_of_nonneg_right hqH hnpos.le
    have hnon : 0≤(width n:ℝ) := by positivity
    unfold radius
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by positivity : 0<(q:ℝ)*(n:ℝ))).2
    push_cast
    nlinarith only [hprod,hnon]
theorem V1ar : ∀ᶠ n : ℕ in atTop,
    V1h4 n ≤ 8*Vo0 n + Vj6 n := by
  filter_upwards [Vkp] with n hgeo
  obtain ⟨hn,hH,hqgeo⟩ := hgeo
  unfold V1h4
  rw [V19.V1mo]
  have hq (q : ℕ) (hq : q∈Icc 1 (narrow n)) :
      (∑ a∈(range (q+1)).filter (fun a => a.Coprime q),
        ∫ t in cell n (narrow n) (width n) (q,a),
          ‖Vi3 n t-model n (q,a) t‖^2) ≤
        8*Vph n q+
          (8*(q:ℝ)*((n+1+V15 n q:ℕ):ℝ)/(V15 n q:ℝ)^2)*
            (Real.log (q:ℝ))^2 := by
    obtain ⟨hq1,_,hr,hrSmall,hrLarge⟩ := hqgeo q hq
    let : NeZero q := ⟨(show 0<q by omega).ne'⟩
    obtain ⟨hh,hw,_,_⟩ := Vo6 (n+1) (radius n (width n) q) hr hrSmall hrLarge
    have hfreq := V73.V106
      (q:=q) (n+1) (V15 n q) (radius n (width n) q) hh hr.le hw
    apply (V160 n q (by omega) hH).trans
    apply (mul_le_mul_of_nonneg_left hfreq (by norm_num : (0:ℝ)≤2)).trans_eq
    simp only [Vph, dite_eq_right (NeZero.ne q)]
    ring
  apply (Finset.sum_le_sum hq).trans_eq
  simp only [Vo0,Vj6,sum_add_distrib,mul_sum]
theorem V15f : ∀ᶠ n : ℕ in atTop,
    Vj6 n ≤ 221184*(width n:ℝ)^2*(Real.log (n:ℝ))^5 := by
  filter_upwards [V20.Vhd, Vkp] with n hgeo hwgeo
  obtain ⟨hn,hQ,hQU,hUn,_,_⟩ := hgeo
  obtain ⟨_,hH,hqgeo⟩ := hwgeo
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  have hnpos : 0<(n:ℝ) := by linarith
  let L := Real.log (n:ℝ)
  have hlog : (1/2:ℝ)≤L := by
    have hh := Real.log_le_log (by norm_num : 0<(2:ℝ)) hnR
    dsimp [L]
    linarith [Real.log_two_gt_d9]
  have hlog0 : 0≤L := by linarith
  have hqbound (q : ℕ) (hq : q∈Icc 1 (narrow n)) :
      (8*(q:ℝ)*((n+1+V15 n q:ℕ):ℝ)/(V15 n q:ℝ)^2)*
        (Real.log (q:ℝ))^2 ≤ 18432*(width n:ℝ)^2/(q:ℝ)*L^2 := by
    obtain ⟨hq1,hqn,hr,hrSmall,hrLarge⟩ := hqgeo q hq
    have hqR : (1:ℝ)≤q := by exact_mod_cast hq1
    have hqpos : 0<(q:ℝ) := by linarith
    obtain ⟨hh,_,hhN,hinv⟩ := Vo6 (n+1) (radius n (width n) q) hr hrSmall hrLarge
    change 0<V15 n q at hh
    change (V15 n q:ℝ)≤((n+1:ℕ):ℝ) at hhN
    change 1/(V15 n q:ℝ)^2≤(24*radius n (width n) q)^2 at hinv
    have hsum : ((n+1+V15 n q:ℕ):ℝ)≤4*(n:ℝ) := by
      push_cast at hhN ⊢
      linarith
    have hlogq : 0≤Real.log (q:ℝ) := Real.log_nonneg hqR
    have hlogqn : Real.log (q:ℝ)≤L := Real.log_le_log hqpos (by exact_mod_cast hqn)
    have hinvn : 1/(n:ℝ)≤1 := (div_le_iff₀ hnpos).2 (by linarith)
    calc
      _ = (8*(q:ℝ)*((n+1+V15 n q:ℕ):ℝ))*
          (1/(V15 n q:ℝ)^2)*(Real.log (q:ℝ))^2 := by ring
      _ ≤ (8*(q:ℝ)*(4*(n:ℝ)))*(24*radius n (width n) q)^2*L^2 := by
        gcongr
      _ = (18432*(width n:ℝ)^2/(q:ℝ)*L^2)*(1/(n:ℝ)) := by
        unfold radius
        field_simp
        ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity) hinvn
  have hlogQ : Real.log (narrow n:ℝ)≤L := Real.log_le_log
    (by exact_mod_cast (show 0<narrow n by omega)) (by exact_mod_cast hQU.trans hUn)
  have hhar : (∑ q∈Icc 1 (narrow n), 1/(q:ℝ))≤3*L := by
    have ht := V20.V233 (narrow n)
    linarith
  have hpower : L^3≤4*L^5 := by
    have hsq : (1:ℝ)≤4*L^2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hsq (pow_nonneg hlog0 3)
    nlinarith
  unfold Vj6
  calc
    _ ≤ ∑ q∈Icc 1 (narrow n), 18432*(width n:ℝ)^2/(q:ℝ)*L^2 := sum_le_sum hqbound
    _ = (18432*(width n:ℝ)^2*L^2)*(∑ q∈Icc 1 (narrow n), 1/(q:ℝ)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro q _
      ring
    _ ≤ (18432*(width n:ℝ)^2*L^2)*(3*L) :=
      mul_le_mul_of_nonneg_left hhar (by positivity)
    _ = (55296*(width n:ℝ)^2)*L^3 := by ring
    _ ≤ (55296*(width n:ℝ)^2)*(4*L^5) :=
      mul_le_mul_of_nonneg_left hpower (by positivity)
    _ = _ := by dsimp [L]; ring
theorem V17w : ∀ᶠ n : ℕ in atTop,
    Vj6 n≤(n:ℝ)^(5/6:ℝ) := by
  filter_upwards [V15f,
    V20.V1rw 221184 (by norm_num)] with n hrem hpower
  exact hrem.trans hpower
theorem V1xb (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ n : ℕ in atTop, (n:ℝ)^(5/6:ℝ)≤δ*(n:ℝ) := by
  filter_upwards [Vi0.V1py δ hδ] with n hb
  obtain ⟨hη,hb⟩ := hb
  let η := (n:ℝ)^(-1/12:ℝ)
  have hη' : 0<η := hη
  have hpow : 0≤(n:ℝ)^(5/6:ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hfactor : (1:ℝ)≤1+1/η := le_add_of_nonneg_right (by positivity)
  have hother : 0≤η*((n:ℝ)+1)*(Real.log (n:ℝ))^2 := by positivity
  calc
    _ ≤ (1+1/η)*(n:ℝ)^(5/6:ℝ) := le_mul_of_one_le_left hpow hfactor
    _ ≤ (1+1/η)*(n:ℝ)^(5/6:ℝ)+η*((n:ℝ)+1)*(Real.log (n:ℝ))^2 :=
      le_add_of_nonneg_right hother
    _ ≤ _ := hb
theorem V1r2 : V3d Vj6 := by
  intro δ hδ
  filter_upwards [V17w, V1xb δ hδ] with n h₁ h₂
  exact h₁.trans h₂
theorem V1kv (hMoment : V3d Vo0) :
    V3d V1h4 := by
  intro δ hδ
  filter_upwards [V1ar, hMoment (δ/16) (by positivity),
    V1r2 (δ/2) (by positivity)] with n hlow hM hR
  nlinarith
theorem V1ix (hMoment : V3d Vo0) :
  let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowSkirt := fun n : ℕ => intervalIntegral (fun t => (lowWideArcs n \ arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (lowSkirt n).re := by
  exact V8j.Vr6
    (V1kv hMoment)
end V8i
end
section
open Filter Finset
open scoped Topology Classical
namespace V3z
open V20 (narrow width)
open V73 (window Ve3)
open V7d (V6t)
open V8i (V15 Vph Vo0)
open V8j (V3d)
noncomputable def V6v (q : ℕ) [NeZero q] (I : Finset ℕ) : ℝ :=
  ((univ : Finset (ZMod q)).filter IsUnit).sup'
    ⟨1, by simp⟩ (V6t q I)
theorem V114 {q : ℕ} [NeZero q] (I : Finset ℕ)
    (r : ZMod q) (hr : IsUnit r) : V6t q I r ≤ V6v q I := by
  exact Finset.le_sup' _ (by simp [hr])
theorem Vtd (q : ℕ) [NeZero q] (I : Finset ℕ) : 0 ≤ V6v q I := by
  exact (norm_nonneg _).trans (V114 I 1 isUnit_one)
noncomputable def Vi1 (n q : ℕ) : ℝ :=
  if hq : q=0 then 0 else
    letI : NeZero q := ⟨hq⟩
    (q:ℝ)/(V15 n q:ℝ) *
      ∑ m ∈ range (n+1+V15 n q),
        V6v q (window (n+1) (V15 n q) m)
noncomputable def Vfb (n : ℕ) : ℝ :=
  (1+Real.log (n:ℝ)) * ∑ q ∈ Icc 1 (narrow n), Vi1 n q
theorem V1uh {n q : ℕ} (hn : 1 ≤ n) [NeZero q]
    (hh : 0 < V15 n q) :
    Vph n q ≤ (1+Real.log (n:ℝ))*Vi1 n q := by
  let E (m : ℕ) := V6v q (window (n+1) (V15 n q) m)
  have hbound := V7d.V1m8 (q:=q)
    n (V15 n q) hn E (fun m _ => Vtd q _)
    (fun m _ r hr => V114 _ r hr)
  have hhR : 0 < (V15 n q:ℝ) := by exact_mod_cast hh
  have hφR : 0 < (q.totient:ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  unfold Vph Vi1
  simp only [dite_eq_right (NeZero.ne q)]
  apply (mul_le_mul_of_nonneg_left hbound
    (by positivity : 0 ≤ (q:ℝ)/((V15 n q:ℝ)^2*(q.totient:ℝ)))).trans_eq
  dsimp [E]
  field_simp
theorem V1g5 :
    ∀ᶠ n : ℕ in atTop, Vo0 n ≤ Vfb n := by
  filter_upwards [V8i.Vkp] with n hgeo
  obtain ⟨hn,_,hqgeo⟩ := hgeo
  unfold Vo0 Vfb
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  obtain ⟨hq1,_,hδ,hδsmall,hδlarge⟩ := hqgeo q hq
  let : NeZero q := ⟨(show 0<q by omega).ne'⟩
  have hh := (V8i.Vo6 (n+1)
    (V19.radius n (width n) q) hδ hδsmall hδlarge).1
  exact V1uh (by omega) hh
theorem V1p5 (hAP : V3d Vfb) :
    V3d Vo0 := by
  intro ε hε
  filter_upwards [V1g5, hAP ε hε] with n h₁ h₂
  exact h₁.trans h₂
theorem V1ti (hAP : V3d Vfb) :
  let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowSkirt := fun n : ℕ => intervalIntegral (fun t => (lowWideArcs n \ arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (lowSkirt n).re := by
  exact V8i.V1ix (V1p5 hAP)
end V3z
end
section
open Filter Finset MeasureTheory
open scoped Topology Interval BigOperators Classical
namespace V2h
open V73 (window)
open V3z (V6v)
open V7d (V6t)
open V54 (V76)
noncomputable def V9a (h : ℕ) (y : ℝ) : Finset ℕ :=
  Ioc ⌊y⌋₊ (⌊y⌋₊ + h)
noncomputable def V4z (q : ℕ) [NeZero q] (h : ℕ) (y : ℝ) : ℝ :=
  V6v q (V9a h y)
theorem Vj2 (q : ℕ) [NeZero q] (h : ℕ) (y : ℝ) :
    0 ≤ V4z q h y := V3z.Vtd q _
theorem V21d (n h m : ℕ) (hh : h ≤ m) (hm : m ≤ n) :
    window (n+1) h m = Ioc (m-h) m := by
  ext k
  simp only [window, mem_filter, mem_range, mem_Ioc]
  omega
theorem V11e {r : ℕ} {y : ℝ}
    (hy : y ∈ Set.Ico (r : ℝ) ((r+1 : ℕ) : ℝ)) : ⌊y⌋₊ = r := by
  apply (Nat.floor_eq_iff ((Nat.cast_nonneg r).trans hy.1)).2
  refine ⟨hy.1, ?_⟩
  simpa only [Nat.cast_add, Nat.cast_one] using hy.2
theorem V1ao (F : ℕ → ℝ) (r : ℕ) :
    IntervalIntegrable (fun y : ℝ => F ⌊y⌋₊) volume (r : ℝ) ((r+1 : ℕ) : ℝ) := by
  have hab : (r : ℝ) ≤ ((r+1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ r
  apply (intervalIntegrable_const :
    IntervalIntegrable (fun _y : ℝ => F r) volume (r : ℝ) ((r+1 : ℕ) : ℝ)).congr_uIoo
  intro y hy
  rw [Set.uIoo_of_le hab] at hy
  change F r = F ⌊y⌋₊
  rw [V11e ⟨hy.1.le, hy.2⟩]
theorem V1x0 (F : ℕ → ℝ) (r : ℕ) :
    (∫ y in (r : ℝ)..((r+1 : ℕ) : ℝ), F ⌊y⌋₊) = F r := by
  have hab : (r : ℝ) ≤ ((r+1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ r
  calc
    _ = ∫ _y in (r : ℝ)..((r+1 : ℕ) : ℝ), F r := by
      apply intervalIntegral.integral_congr_Ioo_of_le hab
      intro y hy
      change F ⌊y⌋₊ = F r
      rw [V11e ⟨hy.1.le, hy.2⟩]
    _ = _ := by simp
theorem V8z (F : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    (∑ r ∈ Ico a b, F r) = ∫ y in (a : ℝ)..(b : ℝ), F ⌊y⌋₊ := by
  calc
    _ = ∑ r ∈ Ico a b, ∫ y in (r : ℝ)..((r+1 : ℕ) : ℝ), F ⌊y⌋₊ := by
      exact sum_congr rfl fun r _ => (V1x0 F r).symm
    _ = _ := intervalIntegral.sum_integral_adjacent_intervals_Ico
      (a := fun r : ℕ => (r : ℝ)) hab (fun r _ => V1ao F r)
theorem Vdb (q : ℕ) [NeZero q] (h : ℕ)
    {a b : ℕ} (hab : a ≤ b) :
    (∑ r ∈ Ico a b, V6v q (Ioc r (r+h))) =
      ∫ y in (a : ℝ)..(b : ℝ), V4z q h y := by
  exact V8z (fun r => V6v q (Ioc r (r+h))) hab
theorem V11z (q : ℕ) [NeZero q] (n h : ℕ)
    {a b : ℕ} (hab : a ≤ b) (hbn : b+h ≤ n+1) :
    (∑ r ∈ Ico a b, V6v q (window (n+1) h (r+h))) =
      ∫ y in (a : ℝ)..(b : ℝ), V4z q h y := by
  rw [← Vdb q h hab]
  apply sum_congr rfl
  intro r hr
  have hrb := (mem_Ico.mp hr).2
  rw [V21d n h (r+h) (by omega) (by omega), Nat.add_sub_cancel]
theorem V142 (q : ℕ) [NeZero q] (n h : ℕ)
    {a b : ℕ} (hab : a ≤ b) (hbn : b+h ≤ n+1) :
    (∑ m ∈ Ico (a+h) (b+h), V6v q (window (n+1) h m)) =
      ∫ y in (a : ℝ)..(b : ℝ), V4z q h y := by
  rw [← Finset.sum_Ico_add' (fun m => V6v q (window (n+1) h m)) a b h]
  exact V11z q n h hab hbn
theorem V11y (q : ℕ) [NeZero q] (n h Y : ℕ)
    (hY : Y+h ≤ n+1) :
    (∑ m ∈ Ico (Y+h) (n+1), V6v q (window (n+1) h m)) =
      ∫ y in (Y : ℝ)..((n+1-h : ℕ) : ℝ), V4z q h y := by
  have hh : h ≤ n+1 := by omega
  have heq : n+1-h+h = n+1 := Nat.sub_add_cancel hh
  simpa only [heq] using V142 q n h
    (a := Y) (b := n+1-h) (by omega) (by omega)
theorem Vh1 (q : ℕ) [NeZero q] (h : ℕ)
    {a b : ℕ} (hab : a ≤ b) :
    (∑ r ∈ Ico a b, V4z q h (r : ℝ)) =
      ∫ y in (a : ℝ)..(b : ℝ), V4z q h y := by
  simpa only [V4z, V9a, Nat.floor_natCast] using
    Vdb q h hab
end V2h
end
section
open Finset
open scoped Classical
namespace V1ua
theorem V1uo (F : ℕ → ℝ) (Y J : ℕ) (C : ℝ)
    (hblock : ∀ j<J, (∑ r∈Ico (2^j*Y) (2^(j+1)*Y), F r) ≤ C*(2^j*Y:ℕ)) :
    (∑ r∈Ico Y (2^J*Y), F r) ≤ C*((2^J*Y:ℕ)-(Y:ℝ)) := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hfirst := ih (fun j hj => hblock j (by omega))
    have hsecond := hblock J (by omega)
    have hY : Y ≤ 2^J*Y := by
      have hp : 1≤2^J := Nat.one_le_pow J 2 (by omega)
      nlinarith
    have hstep : 2^J*Y≤2^(J+1)*Y := by
      rw [pow_succ]
      nlinarith
    rw [← Finset.sum_Ico_consecutive F hY hstep]
    apply (add_le_add hfirst hsecond).trans_eq
    push_cast
    rw [pow_succ]
    ring
theorem V1xa {Y n : ℕ} (hY : 0<Y) (hYn : Y≤n) :
    ∃ J : ℕ, n+1≤2^J*Y ∧ 2^J*Y≤2*n ∧ ∀ j<J, 2^j*Y≤n := by
  have hex : ∃ J : ℕ, n+1≤2^J*Y := by
    refine ⟨n+1, ?_⟩
    have hp := Nat.lt_two_pow_self (n:=n+1)
    have hm : 2^(n+1)≤2^(n+1)*Y := by nlinarith
    omega
  let J := Nat.find hex
  have hcover : n+1≤2^J*Y := Nat.find_spec hex
  have hsmall : ∀ j<J, 2^j*Y≤n := by
    intro j hj
    have hh := Nat.find_min hex hj
    omega
  have hupper : 2^J*Y≤2*n := by
    cases hJ : J with
    | zero => simp only [hJ,pow_zero,one_mul] at hcover; omega
    | succ j =>
      have hj := hsmall j (by omega)
      rw [pow_succ]
      nlinarith
  exact ⟨J,hcover,hupper,hsmall⟩
theorem V1up (F : ℕ → ℝ) {Y n : ℕ} (hY : 0<Y)
    (hYn : Y≤n) {C : ℝ} (hC : 0≤C) (hF : ∀ r, 0≤F r)
    (hblock : ∀ X : ℕ, Y≤X → X≤n →
      (∑ r∈Ico X (2*X), F r) ≤ C*(X:ℝ)) :
    (∑ r∈Ico Y (n+1), F r) ≤ 2*C*(n:ℝ) := by
  obtain ⟨J,hcover,hupper,hsmall⟩ := V1xa hY hYn
  have hblocks : ∀ j<J,
      (∑ r∈Ico (2^j*Y) (2^(j+1)*Y), F r) ≤ C*(2^j*Y:ℕ) := by
    intro j hj
    have hYj : Y≤2^j*Y := by
      have hp : 1≤2^j := Nat.one_le_pow j 2 (by omega)
      nlinarith
    have hh := hblock (2^j*Y) hYj (hsmall j hj)
    convert hh using 1 <;> congr 2 <;> ring
  calc
    _ ≤ ∑ r∈Ico Y (2^J*Y), F r := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro r hr
        simp only [mem_Ico] at hr ⊢
        omega
      · intro r _ _
        exact hF r
    _ ≤ C*((2^J*Y:ℕ)-(Y:ℝ)) := V1uo F Y J C hblocks
    _ ≤ C*(2*n:ℕ) := by
      apply mul_le_mul_of_nonneg_left _ hC
      have h := (show ((2^J*Y:ℕ):ℝ)≤(2*n:ℕ) by exact_mod_cast hupper)
      linarith [Nat.cast_nonneg (α:=ℝ) Y]
    _ = _ := by push_cast; ring
end V1ua
end
section
open Filter Finset MeasureTheory
open scoped Topology Interval Classical
namespace Vbi
open V2h (V4z V9a)
open V3z (V6v Vtd)
def Vv8 : Prop :=
  ∃ C : ℝ, 0<C ∧ ∃ X₀ : ℕ,
    ∀ (q : ℕ) [NeZero q] (X h : ℕ),
      X₀≤X → 2≤X → 0<h → h≤X →
      (q:ℝ)^2*(X:ℝ)^(7/12:ℝ)≤(h:ℝ) →
      (X:ℝ)^(5/8:ℝ)≤(h:ℝ) →
      (∫ y in (X:ℝ)..((2*X:ℕ):ℝ), V4z q h y) ≤
        C*(h:ℝ)*(X:ℝ)/(Real.log (X:ℝ))^12
theorem Vj2 (q : ℕ) [NeZero q] (h : ℕ) (y : ℝ) :
    0≤V4z q h y := Vtd q _
theorem Vh1 (q : ℕ) [NeZero q] (h : ℕ)
    {a b : ℕ} (hab : a≤b) :
    (∑ r∈Ico a b, V4z q h (r:ℝ)) =
      ∫ y in (a:ℝ)..(b:ℝ), V4z q h y := by
  simpa only [V4z, V9a, Nat.floor_natCast] using
    V2h.Vdb q h hab
theorem V1tv (q : ℕ) [NeZero q] (n h Y X₀ : ℕ) (C : ℝ)
    (hC : 0≤C) (hY : 2≤Y) (hYn : Y≤n) (hXY : X₀≤Y)
    (hh : 0<h) (hhY : h≤Y) (hL : 0<Real.log (n:ℝ))
    (hlog : Real.log (n:ℝ)/2≤Real.log (Y:ℝ))
    (hscale : (q:ℝ)^2*(n:ℝ)^(7/12:ℝ)≤(h:ℝ))
    (hscale58 : (n:ℝ)^(5/8:ℝ)≤(h:ℝ))
    (hmean : ∀ X : ℕ, X₀≤X → 2≤X → h≤X →
      (q:ℝ)^2*(X:ℝ)^(7/12:ℝ)≤(h:ℝ) →
      (X:ℝ)^(5/8:ℝ)≤(h:ℝ) →
      (∫ y in (X:ℝ)..((2*X:ℕ):ℝ), V4z q h y) ≤
        C*(h:ℝ)*(X:ℝ)/(Real.log (X:ℝ))^12) :
    (∑ r∈Ico Y (n+1), V4z q h (r:ℝ)) ≤
      8192*C*(h:ℝ)*(n:ℝ)/(Real.log (n:ℝ))^12 := by
  let L := Real.log (n:ℝ)
  let K := 4096*C*(h:ℝ)/L^12
  have hK : 0≤K := by dsimp [K]; positivity
  have hblock : ∀ X : ℕ, Y≤X → X≤n →
      (∑ r∈Ico X (2*X), V4z q h (r:ℝ))≤K*(X:ℝ) := by
    intro X hYX hXn
    have hX2 : 2≤X := hY.trans hYX
    have hXpos : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
    have hYpos : 0<(Y:ℝ) := by exact_mod_cast (show 0<Y by omega)
    have hLX : L/2≤Real.log (X:ℝ) := hlog.trans
      (Real.log_le_log hYpos (by exact_mod_cast hYX))
    have hLXpos : 0<Real.log (X:ℝ) := (by dsimp [L]; positivity : 0<L/2).trans_le hLX
    have hXscale : (q:ℝ)^2*(X:ℝ)^(7/12:ℝ)≤(h:ℝ) := by
      apply le_trans _ hscale
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hXn) (by norm_num)
    rw [Vh1 q h (show X≤2*X by omega)]
    calc
      _ ≤ C*(h:ℝ)*(X:ℝ)/(Real.log (X:ℝ))^12 :=
        hmean X (hXY.trans hYX) hX2 (hhY.trans hYX) hXscale
          (le_trans (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hXn) (by norm_num)) hscale58)
      _ ≤ C*(h:ℝ)*(X:ℝ)/(L/2)^12 := by
        apply div_le_div_of_nonneg_left (by positivity) (by dsimp [L]; positivity)
        exact pow_le_pow_left₀ (by dsimp [L]; positivity) hLX 12
      _ = K*(X:ℝ) := by
        dsimp [K]
        field_simp
        ring
  have h := V1ua.V1up
    (fun r => V4z q h (r:ℝ)) (by omega) hYn hK
    (fun r => Vj2 q h _) hblock
  apply h.trans_eq
  dsimp [K,L]
  ring
end Vbi
end
section
open Filter Finset
open scoped Topology Classical
namespace V9i
open V54 (V76)
open V20 (narrow)
open V73 (window)
open V7d (V6t V1mn)
open V8i (V15)
open V3z (V6v Vi1 Vfb)
def bulk (n h Y : ℕ) : Finset ℕ :=
  (range (n+1+h)).filter (fun m => Y+h ≤ m ∧ m ≤ n)
def boundary (n h Y : ℕ) : Finset ℕ :=
  range (n+1+h) \ bulk n h Y
theorem V1zn (n h Y m : ℕ) :
    m ∈ bulk n h Y ↔ Y+h ≤ m ∧ m ≤ n := by
  simp only [bulk, mem_filter, mem_range]
  omega
theorem V20q (n h Y : ℕ) : bulk n h Y = Icc (Y+h) n := by
  ext m
  rw [V1zn, mem_Icc]
theorem V235 (n h Y : ℕ) : bulk n h Y ⊆ range (n+1+h) :=
  filter_subset _ _
theorem V20m (n h Y : ℕ) :
    boundary n h Y ⊆ range (Y+h) ∪ Icc (n+1) (n+h) := by
  intro m hm
  obtain ⟨hmrange, hmnot⟩ := mem_sdiff.mp hm
  have hmr := mem_range.mp hmrange
  by_cases hstart : m < Y+h
  · exact mem_union_left _ (mem_range.mpr hstart)
  · have hend : n < m := by
      by_contra hn
      exact hmnot ((V1zn n h Y m).mpr (by omega))
    exact mem_union_right _ (mem_Icc.mpr (by omega))
theorem V1zv (n h Y : ℕ) : (boundary n h Y).card ≤ Y+2*h := by
  calc
    _ ≤ (range (Y+h) ∪ Icc (n+1) (n+h)).card := card_le_card (V20m n h Y)
    _ ≤ (range (Y+h)).card + (Icc (n+1) (n+h)).card := card_union_le _ _
    _ ≤ Y+2*h := by simp only [card_range, Nat.card_Icc]; omega
theorem V1sw (n h Y : ℕ) (f : ℕ → ℝ) :
    (∑ m ∈ range (n+1+h), f m) =
      (∑ m ∈ bulk n h Y, f m) + ∑ m ∈ boundary n h Y, f m := by
  simpa only [boundary, add_comm] using
    (Finset.sum_sdiff (f:=f) (V235 n h Y)).symm
private theorem Vod (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) :
    ‖V76 k‖ ≤ Real.log (n : ℝ) := by
  unfold V76
  by_cases hp : k.Prime
  · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hp.one_lt.le
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hp.pos
    have hkn : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
    simp only [hp, ite_true, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg hk1)]
    exact Real.log_le_log hk0 hkn
  · simp only [hp, ite_false, Complex.ofReal_zero, norm_zero]
    exact Real.log_nonneg (by exact_mod_cast hn)
theorem V1n4 (n q : ℕ) [NeZero q] (hn : 1 ≤ n)
    (I : Finset ℕ) (hI : I ⊆ range (n+1)) (r : ZMod q) :
    V6t q I r ≤ (I.card : ℝ) * (1+Real.log (n : ℝ)) := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hφ : 0 < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hφ1 : (1 : ℝ) ≤ q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hmass : ‖∑ k ∈ I.filter (fun k : ℕ => (k : ZMod q) = r), V76 k‖ ≤
      (I.card : ℝ) * Real.log (n : ℝ) := by
    calc
      _ ≤ ∑ k ∈ I.filter (fun k : ℕ => (k : ZMod q) = r), ‖V76 k‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _k ∈ I.filter (fun k : ℕ => (k : ZMod q) = r), Real.log (n : ℝ) := by
        apply sum_le_sum
        intro k hk
        have hkI := (mem_filter.mp hk).1
        exact Vod n k hn (by have := mem_range.mp (hI hkI); omega)
      _ = ((I.filter (fun k : ℕ => (k : ZMod q) = r)).card : ℝ) *
          Real.log (n : ℝ) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (I.card : ℝ) * Real.log (n : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hlog
        exact_mod_cast card_filter_le I _
  have hmain : ‖(I.card : ℂ) / (q.totient : ℂ)‖ ≤ (I.card : ℝ) := by
    rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
    apply (div_le_iff₀ hφ).mpr
    nlinarith [Nat.cast_nonneg (α:=ℝ) I.card]
  change ‖(∑ k ∈ I.filter (fun k : ℕ => (k : ZMod q) = r), V76 k) -
    (I.card : ℂ) / (q.totient : ℂ)‖ ≤ _
  calc
    _ ≤ ‖∑ k ∈ I.filter (fun k : ℕ => (k : ZMod q) = r), V76 k‖ +
        ‖(I.card : ℂ) / (q.totient : ℂ)‖ := norm_sub_le _ _
    _ ≤ (I.card : ℝ) * Real.log (n : ℝ) + I.card := add_le_add hmass hmain
    _ = _ := by ring
theorem V1y6 (n q : ℕ) [NeZero q] (hn : 1 ≤ n)
    (I : Finset ℕ) (hI : I ⊆ range (n+1)) :
    V6v q I ≤ (I.card : ℝ) * (1+Real.log (n : ℝ)) := by
  unfold V6v
  exact Finset.sup'_le _ _ (fun r _ => V1n4 n q hn I hI r)
theorem V1v7 (n q h m : ℕ) [NeZero q] (hn : 1 ≤ n) :
    V6v q (window (n+1) h m) ≤ (h : ℝ) * (1+Real.log (n : ℝ)) := by
  have hL : 0 ≤ 1+Real.log (n : ℝ) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast hn)
    linarith
  apply (V1y6 n q hn _ (filter_subset _ _)).trans
  apply mul_le_mul_of_nonneg_right _ hL
  exact_mod_cast V1mn (n+1) h m
theorem V1yf (n q h Y : ℕ) [NeZero q] (hn : 1 ≤ n) :
    (∑ m ∈ boundary n h Y, V6v q (window (n+1) h m)) ≤
      ((Y+2*h : ℕ) : ℝ) * h * (1+Real.log (n : ℝ)) := by
  have hL : 0 ≤ 1+Real.log (n : ℝ) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast hn)
    linarith
  calc
    _ ≤ ∑ _m ∈ boundary n h Y, (h : ℝ)*(1+Real.log (n : ℝ)) :=
      sum_le_sum (fun m _ => V1v7 n q h m hn)
    _ = ((boundary n h Y).card : ℝ) * ((h : ℝ)*(1+Real.log (n : ℝ))) := by
      rw [sum_const, nsmul_eq_mul]
    _ ≤ ((Y+2*h : ℕ) : ℝ) * ((h : ℝ)*(1+Real.log (n : ℝ))) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Nat.cast_nonneg _) hL)
      exact_mod_cast V1zv n h Y
    _ = _ := by ring
noncomputable def V98 (n Y q : ℕ) : ℝ :=
  if hq : q=0 then 0 else
    letI : NeZero q := ⟨hq⟩
    (q : ℝ)/(V15 n q : ℝ) *
      ∑ m ∈ bulk n (V15 n q) Y,
        V6v q (window (n+1) (V15 n q) m)
noncomputable def Vb1 (n Y q : ℕ) : ℝ :=
  if hq : q=0 then 0 else
    letI : NeZero q := ⟨hq⟩
    (q : ℝ)/(V15 n q : ℝ) *
      ∑ m ∈ boundary n (V15 n q) Y,
        V6v q (window (n+1) (V15 n q) m)
noncomputable def Vic (n Y : ℕ) : ℝ :=
  (1+Real.log (n : ℝ)) * ∑ q ∈ Icc 1 (narrow n), V98 n Y q
noncomputable def Vb8 (n Y : ℕ) : ℝ :=
  (1+Real.log (n : ℝ)) * ∑ q ∈ Icc 1 (narrow n), Vb1 n Y q
theorem V1st (n Y q : ℕ) :
    Vi1 n q = V98 n Y q + Vb1 n Y q := by
  by_cases hq : q=0
  · simp [Vi1, V98, Vb1, hq]
  · let : NeZero q := ⟨hq⟩
    simp only [Vi1, V98, Vb1,
      dite_eq_right hq]
    rw [V1sw n (V15 n q) Y, mul_add]
theorem V1yg (n Y : ℕ) :
    Vfb n = Vic n Y + Vb8 n Y := by
  unfold Vfb Vic Vb8
  simp_rw [V1st n Y]
  rw [sum_add_distrib, mul_add]
theorem V1hh (n Y q : ℕ) [NeZero q] (hn : 1 ≤ n)
    (hh : 0 < V15 n q) :
    Vb1 n Y q ≤
      (q : ℝ) * ((Y+2*V15 n q : ℕ) : ℝ) * (1+Real.log (n : ℝ)) := by
  have hhR : (0 : ℝ) < V15 n q := by exact_mod_cast hh
  unfold Vb1
  simp only [dite_eq_right (NeZero.ne q)]
  apply (mul_le_mul_of_nonneg_left (V1yf n q (V15 n q) Y hn)
    (div_nonneg (Nat.cast_nonneg _) hhR.le)).trans_eq
  field_simp
theorem V1os (Q : ℕ) : (∑ q ∈ Icc 1 Q, (q : ℝ)) ≤ (Q : ℝ)^2 := by
  calc
    _ ≤ ∑ _q ∈ Icc 1 Q, (Q : ℝ) := by
      apply sum_le_sum
      intro q hq
      exact_mod_cast (mem_Icc.mp hq).2
    _ = (Q : ℝ)^2 := by simp [sum_const, nsmul_eq_mul, Nat.card_Icc, pow_two]
theorem V1xg (n Y hmax : ℕ) (hn : 1 ≤ n)
    (hh : ∀ q ∈ Icc 1 (narrow n), 0 < V15 n q)
    (hmax_bound : ∀ q ∈ Icc 1 (narrow n), V15 n q ≤ hmax) :
    Vb8 n Y ≤ (1+Real.log (n : ℝ))^2 *
      ((Y+2*hmax : ℕ) : ℝ) * (narrow n : ℝ)^2 := by
  have hL : 0 ≤ 1+Real.log (n : ℝ) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast hn)
    linarith
  unfold Vb8
  calc
    _ ≤ (1+Real.log (n : ℝ)) *
        ∑ q ∈ Icc 1 (narrow n), (q : ℝ)*((Y+2*hmax : ℕ) : ℝ)*(1+Real.log (n : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hL
      apply sum_le_sum
      intro q hq
      have hq1 := (mem_Icc.mp hq).1
      let : NeZero q := ⟨by omega⟩
      apply (V1hh n Y q hn (hh q hq)).trans
      apply mul_le_mul_of_nonneg_right _ hL
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact_mod_cast (show Y+2*V15 n q ≤ Y+2*hmax by have := hmax_bound q hq; omega)
    _ = (1+Real.log (n : ℝ))^2 * ((Y+2*hmax : ℕ) : ℝ) *
        (∑ q ∈ Icc 1 (narrow n), (q : ℝ)) := by
      rw [← sum_mul, ← sum_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (V1os (narrow n)) (by positivity)
end V9i
end
section
open Filter Finset MeasureTheory
open scoped Topology Interval Classical
namespace V1ub
open V20 (narrow)
open V8i (V15)
open V73 (window)
open V3z (V6v)
open V2h (V4z)
open V9i (bulk V98 Vic)
open Vbi (Vj2)
theorem V1gk (q : ℕ) [NeZero q] (n h Y : ℕ) :
    (∑ m∈bulk n h Y, V6v q (window (n+1) h m)) ≤
      ∑ r∈Ico Y (n+1), V4z q h (r:ℝ) := by
  by_cases hY : Y+h≤n+1
  · have heq : (∑ m∈bulk n h Y, V6v q (window (n+1) h m)) =
        ∑ r∈Ico Y (n+1-h), V4z q h (r:ℝ) := by
      have hs : Icc (Y+h) n = Ico (Y+h) (n+1) := by
        ext m
        simp only [mem_Icc, mem_Ico]
        omega
      rw [V9i.V20q, hs]
      rw [V2h.V11y q n h Y hY,
        ← Vbi.Vh1 q h (show Y≤n+1-h by omega)]
    rw [heq]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro r hr
      simp only [mem_Ico] at hr ⊢
      omega
    · intro r _ _
      exact Vj2 q h _
  · have he : bulk n h Y = ∅ := by
      rw [V9i.V20q]
      exact Finset.Icc_eq_empty_of_lt (by omega)
    rw [he,sum_empty]
    exact Finset.sum_nonneg (fun r _ => Vj2 q h _)
theorem V1zb (q : ℕ) [NeZero q] (n Y : ℕ) (C : ℝ)
    (hh : 0<V15 n q)
    (hprefix : (∑ r∈Ico Y (n+1), V4z q (V15 n q) (r:ℝ)) ≤
      8192*C*(V15 n q:ℝ)*(n:ℝ)/(Real.log (n:ℝ))^12) :
    V98 n Y q ≤ 8192*C*(q:ℝ)*(n:ℝ)/(Real.log (n:ℝ))^12 := by
  have hhR : 0<(V15 n q:ℝ) := by exact_mod_cast hh
  unfold V98
  simp only [dite_eq_right (NeZero.ne q)]
  apply (mul_le_mul_of_nonneg_left
    ((V1gk q n (V15 n q) Y).trans hprefix)
    (by positivity : 0≤(q:ℝ)/(V15 n q:ℝ))).trans_eq
  field_simp
theorem V1s9 (n Y X₀ : ℕ) (C : ℝ)
    (hC : 0≤C) (hY : 2≤Y) (hYn : Y≤n) (hXY : X₀≤Y)
    (hL : 1≤Real.log (n:ℝ))
    (hlog : Real.log (n:ℝ)/2≤Real.log (Y:ℝ))
    (hQ : (narrow n:ℝ)≤16*(Real.log (n:ℝ))^2)
    (hgeom : ∀ q∈Icc 1 (narrow n),
      0<V15 n q ∧ V15 n q≤Y ∧
        (q:ℝ)^2*(n:ℝ)^(7/12:ℝ)≤(V15 n q:ℝ) ∧ (n:ℝ)^(5/8:ℝ)≤(V15 n q:ℝ))
    (hmean : ∀ (q : ℕ) [NeZero q] (X h : ℕ),
      X₀≤X → 2≤X → 0<h → h≤X →
      (q:ℝ)^2*(X:ℝ)^(7/12:ℝ)≤(h:ℝ) →
      (X:ℝ)^(5/8:ℝ)≤(h:ℝ) →
      (∫ y in (X:ℝ)..((2*X:ℕ):ℝ), V4z q h y) ≤
        C*(h:ℝ)*(X:ℝ)/(Real.log (X:ℝ))^12) :
    Vic n Y ≤ 4194304*C*(n:ℝ)/(Real.log (n:ℝ))^7 := by
  let L := Real.log (n:ℝ)
  have hLpos : 0<L := by dsimp [L]; linarith
  have hfactor : 0≤1+L := by linarith
  have heach : ∀ q∈Icc 1 (narrow n),
      V98 n Y q≤8192*C*(q:ℝ)*(n:ℝ)/L^12 := by
    intro q hq
    have hq1 := (mem_Icc.mp hq).1
    let : NeZero q := ⟨by omega⟩
    obtain ⟨hh,hhY,hscale,hscale58⟩ := hgeom q hq
    apply V1zb q n Y C hh
    exact Vbi.V1tv q n (V15 n q) Y X₀ C
      hC hY hYn hXY hh hhY hLpos hlog hscale hscale58
      (fun X hX₀ hX2 hhX hs h5 => hmean q X (V15 n q) hX₀ hX2 hh hhX hs h5)
  unfold Vic
  change (1+L)*(∑ q∈Icc 1 (narrow n), V98 n Y q)≤_
  calc
    _ ≤ (1+L)*(∑ q∈Icc 1 (narrow n), 8192*C*(q:ℝ)*(n:ℝ)/L^12) :=
      mul_le_mul_of_nonneg_left (sum_le_sum heach) hfactor
    _ = (1+L)*(8192*C*(n:ℝ)/L^12)*(∑ q∈Icc 1 (narrow n), (q:ℝ)) := by
      have hs : (∑ q∈Icc 1 (narrow n), 8192*C*(q:ℝ)*(n:ℝ)/L^12) =
          (8192*C*(n:ℝ)/L^12)*(∑ q∈Icc 1 (narrow n), (q:ℝ)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro q _
        ring
      rw [hs]
      ring
    _ ≤ (1+L)*(8192*C*(n:ℝ)/L^12)*(narrow n:ℝ)^2 :=
      mul_le_mul_of_nonneg_left (V9i.V1os (narrow n)) (by positivity)
    _ ≤ (2*L)*(8192*C*(n:ℝ)/L^12)*(16*L^2)^2 := by
      have hL1 : 1≤L := hL
      gcongr
      · linarith
    _ = _ := by
      change _ = 4194304*C*(n:ℝ)/L^7
      field_simp
      ring
end V1ub
end
section
open Filter Finset
open scoped Topology BigOperators Classical
namespace Vfn
open V20 (narrow cutoff width V90)
open V19 (radius)
open V8i (V15)
noncomputable def start (n : ℕ) : ℕ :=
  ⌈(n : ℝ) / (Real.log (n : ℝ))^12⌉₊
structure Parameters (n : ℕ) : Prop where
  n_ge_two : 2 ≤ n
  log_ge_one : 1 ≤ Real.log (n : ℝ)
  narrow_pos : 1 ≤ narrow n
  narrow_le_log : (narrow n : ℝ) ≤ 16 * (Real.log (n : ℝ))^2
  start_ge_two : 2 ≤ start n
  start_le : start n ≤ n
  start_upper : (start n : ℝ) ≤ 2 * (n : ℝ) / (Real.log (n : ℝ))^12
  start_log : Real.log (n : ℝ) / 2 ≤ Real.log (start n : ℝ)
  start_lower : (n : ℝ)^(3/4 : ℝ) ≤ (start n : ℝ)
  window_bounds : ∀ q ∈ Icc 1 (narrow n),
    0 < V15 n q ∧ V15 n q ≤ start n ∧
    (V15 n q : ℝ) ≤ (n : ℝ)^(3/4 : ℝ) ∧
    (q : ℝ)^2 * (n : ℝ)^(7/12 : ℝ) ≤ (V15 n q : ℝ) ∧
    (n : ℝ)^(5/8 : ℝ) ≤ (V15 n q : ℝ)
private theorem V1wx (n : ℕ) (hn : 2 ≤ n) :
    (Nat.log 2 (n+2) : ℝ) ≤ 4 * Real.log (n : ℝ) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (2 : ℝ)^(Nat.log 2 (n+2)) ≤ ((n+2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n+2 ≠ 0)
  have hraw := Real.log_le_log (by positivity) hpow
  have hin : ((n+2 : ℕ) : ℝ) ≤ (n : ℝ)^2 := by
    push_cast
    nlinarith only [hnR, sq_nonneg ((n : ℝ)-2)]
  have hlog := Real.log_le_log (by positivity) hin
  rw [Real.log_pow] at hraw hlog
  have hl2 : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left hl2
    (Nat.cast_nonneg (Nat.log 2 (n+2)) : 0 ≤ (_ : ℝ))
  push_cast at hlog hraw
  linarith only [hm, hraw, hlog]
set_option maxHeartbeats 4000000 in
theorem Vy1 : ∀ᶠ n : ℕ in atTop, Parameters n := by
  have hloglim : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    hloglim.eventually (eventually_ge_atTop (1 : ℝ)),
    V90 12 (1/4) 1 (by norm_num) (by norm_num),
    V90 4 (1/12) (1/1572864) (by norm_num) (by norm_num),
    V90 0 (1/12) (1/2) (by norm_num) (by norm_num),
    V90 2 (1/24) (1/98304) (by norm_num) (by norm_num)]
      with n hn hL hlog12 hlog4 hpower hlog2
  let x : ℝ := n
  let L := Real.log x
  have hx : 0 < x := by dsimp [x]; exact_mod_cast (show 0 < n by omega)
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast (show 1 ≤ n by omega)
  change 1 ≤ L at hL
  have hL0 : 0 < L := by linarith
  have hL12 : 0 < L^12 := pow_pos hL0 _
  have h12 : L^12 ≤ x^(1/4 : ℝ) := by simpa only [one_mul] using hlog12
  have h4 : 1572864 * L^4 ≤ x^(1/12 : ℝ) := by
    change L^4 ≤ (1/1572864 : ℝ) * x^(1/12 : ℝ) at hlog4
    linarith
  have hp12 : 2 ≤ x^(1/12 : ℝ) := by
    change L^0 ≤ (1/2 : ℝ) * x^(1/12 : ℝ) at hpower
    norm_num only [pow_zero] at hpower
    linarith
  have hp14 : 1 ≤ x^(1/4 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hp34 : 1 ≤ x^(3/4 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hp34two : 2 ≤ x^(3/4 : ℝ) := hp12.trans
    (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num))
  have hQ1 : 1 ≤ narrow n := by
    unfold narrow
    exact Nat.pow_pos (Nat.log_pos (by decide) (by omega))
  have hQpos : 0 < (narrow n : ℝ) := by exact_mod_cast (show 0 < narrow n by omega)
  have hQup : (narrow n : ℝ) ≤ 16 * L^2 := by
    calc
      _ = (Nat.log 2 (n+2) : ℝ)^2 := by simp [narrow]
      _ ≤ (4*L)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) (V1wx n hn) _
      _ = _ := by ring
  have hRlo : x^(1/4 : ℝ) ≤ (cutoff n : ℝ) := by
    have hf := Nat.lt_floor_add_one (x^(1/3 : ℝ))
    change x^(1/3 : ℝ) < (cutoff n : ℝ)+1 at hf
    have hp : 2*x^(1/4 : ℝ) ≤ x^(1/3 : ℝ) := by
      calc
        _ ≤ x^(1/4 : ℝ) * x^(1/12 : ℝ) := by
          nlinarith only [mul_le_mul_of_nonneg_left hp12 (Real.rpow_nonneg hx.le (1/4 : ℝ))]
        _ = _ := by rw [← Real.rpow_add hx]; norm_num
    linarith
  have hRup : (cutoff n : ℝ) ≤ x^(1/3 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hx.le _)
  have hRpos : 0 < (cutoff n : ℝ) := (Real.rpow_pos_of_pos hx _).trans_le hRlo
  have hwidth : (width n : ℝ) = 256 * (cutoff n : ℝ) * (narrow n : ℝ) := by
    simp [width]
  have hHpos : 0 < (width n : ℝ) := by rw [hwidth]; positivity
  have hYraw : x^(3/4 : ℝ) ≤ x/L^12 := by
    apply (le_div_iff₀ hL12).2
    calc
      _ ≤ x^(3/4 : ℝ) * x^(1/4 : ℝ) :=
        mul_le_mul_of_nonneg_left h12 (Real.rpow_nonneg hx.le _)
      _ = x := by rw [← Real.rpow_add hx]; norm_num
  have hYraw1 : 1 ≤ x/L^12 := hp34.trans hYraw
  have hYceil : x/L^12 ≤ (start n : ℝ) := Nat.le_ceil _
  have hYlower : x^(3/4 : ℝ) ≤ (start n : ℝ) := hYraw.trans hYceil
  have hY2 : 2 ≤ start n := by exact_mod_cast hp34two.trans hYlower
  have hYn : start n ≤ n := by
    apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hL12).2
    exact le_mul_of_one_le_right hx.le (one_le_pow₀ hL)
  have hYupper : (start n : ℝ) ≤ 2*x/L^12 := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ x/L^12 by positivity)
    change (start n : ℝ) < x/L^12+1 at hc
    calc
      _ ≤ 2*(x/L^12) := by linarith
      _ = _ := by ring
  have hYlog : L/2 ≤ Real.log (start n : ℝ) := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hx (3/4 : ℝ)) hYlower
    rw [Real.log_rpow hx] at hh
    change (3/4 : ℝ)*L ≤ Real.log (start n : ℝ) at hh
    linarith
  refine ⟨hn, hL, hQ1, hQup, hY2, hYn, hYupper, hYlog, hYlower, ?_⟩
  intro q hq
  obtain ⟨hq1,hqQ⟩ := mem_Icc.mp hq
  have hq1R : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hqpos : 0 < (q : ℝ) := by linarith
  have hqQreal : (q : ℝ) ≤ (narrow n : ℝ) := by exact_mod_cast hqQ
  have hqlog : (q : ℝ) ≤ 16*L^2 := hqQreal.trans hQup
  have hrec : 1/(12*radius n (width n) q) = (q : ℝ)*x/(12*(width n : ℝ)) := by
    unfold radius
    change 1/(12*((width n : ℝ)/((q : ℝ)*x))) = _
    field_simp
  have hhup : (V15 n q : ℝ) ≤ (q : ℝ)*x/(12*(width n : ℝ)) := by
    rw [V15, hrec]
    exact Nat.floor_le (by positivity)
  have hhfloor : (q : ℝ)*x/(12*(width n : ℝ)) < (V15 n q : ℝ)+1 := by
    rw [V15, hrec]
    exact Nat.lt_floor_add_one _
  have hHq : (q : ℝ)*(cutoff n : ℝ) ≤ 12*(width n : ℝ) := by
    calc
      _ ≤ (narrow n : ℝ)*(cutoff n : ℝ) :=
        mul_le_mul_of_nonneg_right hqQreal hRpos.le
      _ ≤ 3072*((narrow n : ℝ)*(cutoff n : ℝ)) :=
        le_mul_of_one_le_left (by positivity) (by norm_num)
      _ = _ := by rw [hwidth]; ring
  have hproduct : x^(1/4 : ℝ)*x^(3/4 : ℝ) = x := by
    rw [← Real.rpow_add hx]; norm_num
  have hhscale : (V15 n q : ℝ) ≤ x^(3/4 : ℝ) := by
    apply hhup.trans
    apply (div_le_iff₀ (show 0 < 12*(width n : ℝ) by positivity)).2
    calc
      _ = ((q : ℝ)*x^(1/4 : ℝ))*x^(3/4 : ℝ) := by rw [mul_assoc, hproduct]
      _ ≤ ((q : ℝ)*(cutoff n : ℝ))*x^(3/4 : ℝ) := by gcongr
      _ ≤ (12*(width n : ℝ))*x^(3/4 : ℝ) :=
        mul_le_mul_of_nonneg_right hHq (Real.rpow_nonneg hx.le _)
      _ = _ := by ring
  have hcritical : 24*(width n : ℝ)*(q : ℝ)*x^(7/12 : ℝ) ≤ x := by
    calc
      _ = 24*256*(cutoff n : ℝ)*(narrow n : ℝ)*(q : ℝ)*x^(7/12 : ℝ) := by
        rw [hwidth]; ring
      _ ≤ 24*256*x^(1/3 : ℝ)*(16*L^2)*(16*L^2)*x^(7/12 : ℝ) := by
        gcongr
      _ = (1572864*L^4)*(x^(1/3 : ℝ)*x^(7/12 : ℝ)) := by ring
      _ = (1572864*L^4)*x^(11/12 : ℝ) := by
        rw [← Real.rpow_add hx]; norm_num
      _ ≤ x^(1/12 : ℝ)*x^(11/12 : ℝ) :=
        mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hx.le _)
      _ = x := by rw [← Real.rpow_add hx]; norm_num
  have htarget : 2*((q : ℝ)^2*x^(7/12 : ℝ)) ≤
      (q : ℝ)*x/(12*(width n : ℝ)) := by
    apply (le_div_iff₀ (show 0 < 12*(width n : ℝ) by positivity)).2
    have hh := mul_le_mul_of_nonneg_left hcritical hqpos.le
    convert hh using 1; ring
  have htarget1 : 1 ≤ (q : ℝ)^2*x^(7/12 : ℝ) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hq1R)
      (Real.one_le_rpow hx1 (by norm_num))
  have hhcritical : (q : ℝ)^2*x^(7/12 : ℝ) ≤ (V15 n q : ℝ) := by linarith
  have hhpos : 0 < V15 n q := by
    have : (0 : ℝ) < (V15 n q : ℝ) := by linarith
    exact_mod_cast this
  have hhY : V15 n q ≤ start n := by exact_mod_cast hhscale.trans hYlower
  have hA : 2*(49152*L^2) ≤ x^(1/24 : ℝ) := by
    change L^2 ≤ (1/98304 : ℝ) * x^(1/24 : ℝ) at hlog2
    linarith
  have hw : 12*(width n : ℝ) ≤ 49152*L^2*x^(1/3 : ℝ) := by
    rw [hwidth]
    have : (cutoff n : ℝ)*(narrow n : ℝ) ≤ x^(1/3 : ℝ)*(16*L^2) :=
      mul_le_mul hRup hQup hQpos.le (Real.rpow_nonneg hx.le _)
    nlinarith
  have hkey : 2*x^(5/8 : ℝ)*(12*(width n : ℝ)) ≤ x := by
    calc 2*x^(5/8 : ℝ)*(12*(width n : ℝ)) ≤ 2*x^(5/8 : ℝ)*(49152*L^2*x^(1/3 : ℝ)) := by
          gcongr
      _ = x^(5/8 : ℝ)*(2*(49152*L^2))*x^(1/3 : ℝ) := by ring
      _ ≤ x^(5/8 : ℝ)*x^(1/24 : ℝ)*x^(1/3 : ℝ) := by gcongr
      _ = x := by rw [← Real.rpow_add hx, ← Real.rpow_add hx]; norm_num
  have h58 : x^(5/8 : ℝ) ≤ (V15 n q : ℝ) := by
    have h1 : 2*x^(5/8 : ℝ) ≤ (q : ℝ)*x/(12*(width n : ℝ)) := by
      apply (le_div_iff₀ (show 0 < 12*(width n : ℝ) by positivity)).2
      exact hkey.trans (le_mul_of_one_le_left hx.le hq1R)
    have h2 : 1 ≤ x^(5/8 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
    linarith
  exact ⟨hhpos, hhY, hhscale, hhcritical, h58⟩
theorem V1j3 : ∀ᶠ n : ℕ in atTop,
    2 ≤ n ∧ 1 ≤ Real.log (n : ℝ) ∧
    (start n : ℝ) ≤ 2*(n : ℝ)/(Real.log (n : ℝ))^12 ∧
    (narrow n : ℝ) ≤ 16*(Real.log (n : ℝ))^2 ∧
    ∀ q ∈ Icc 1 (narrow n), 0 < V15 n q ∧
      (V15 n q : ℝ) ≤ (n : ℝ)^(3/4 : ℝ) := by
  filter_upwards [Vy1] with n hp
  refine ⟨hp.n_ge_two, hp.log_ge_one, hp.start_upper, hp.narrow_le_log, ?_⟩
  intro q hq
  have hh := hp.window_bounds q hq
  exact ⟨hh.1, hh.2.2.1⟩
theorem V1w8 : Tendsto start atTop atTop := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ)^(3/4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3/4)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  apply tendsto_atTop.2
  intro b
  filter_upwards [Vy1, hpow.eventually (eventually_ge_atTop (b : ℝ))]
    with n hp hb
  exact_mod_cast hb.trans hp.start_lower
end Vfn
end
section
open Filter Finset
open scoped Topology Classical
namespace Vg4
open V20 (narrow)
open V8i (V15)
open V9i (Vic Vb8)
open V3z (Vfb)
open V8j (V3d)
theorem V1pa {P : ℕ → ℝ} {a : ℝ} (ha : a < 1)
    (hRate : ∃ C : ℝ, 0<C ∧ ∀ᶠ n : ℕ in atTop,
      P n ≤ C*((n : ℝ)/(Real.log (n : ℝ))^6+
        (n : ℝ)^a*(Real.log (n : ℝ))^6)) : V3d P := by
  obtain ⟨C,hC,hRate⟩ := hRate
  intro ε hε
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hpow : Tendsto (fun n : ℕ => (Real.log (n : ℝ))^6) atTop atTop :=
    (tendsto_pow_atTop (by decide : (6 : ℕ) ≠ 0)).comp hlog
  filter_upwards [hRate, hpow.eventually_ge_atTop (2*C/ε),
    V20.V90 6 (1-a) (ε/(2*C))
      (by linarith) (by positivity), eventually_ge_atTop (2 : ℕ)] with n hP hlarge hsmall hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0<n by omega)
  have hL : 0 < (Real.log (n : ℝ))^6 :=
    (div_pos (by positivity : 0<2*C) hε).trans_le hlarge
  have hfirst : C*((n : ℝ)/(Real.log (n : ℝ))^6) ≤ ε*(n : ℝ)/2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hL).2
    have hh := (div_le_iff₀ hε).1 hlarge
    have hmul := mul_le_mul_of_nonneg_right hh hnR.le
    nlinarith
  have hsecond : C*((n : ℝ)^a*(Real.log (n : ℝ))^6) ≤ ε*(n : ℝ)/2 := by
    calc
      _ ≤ C*((n : ℝ)^a*((ε/(2*C))*(n : ℝ)^(1-a))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hnR.le _)) hC.le
      _ = (ε/2)*((n : ℝ)^a*(n : ℝ)^(1-a)) := by field_simp
      _ = ε*(n : ℝ)/2 := by
        rw [← Real.rpow_add hnR, show a+(1-a) = 1 by ring, Real.rpow_one]
        ring
  calc
    P n ≤ C*((n : ℝ)/(Real.log (n : ℝ))^6+
      (n : ℝ)^a*(Real.log (n : ℝ))^6) := hP
    _ = C*((n : ℝ)/(Real.log (n : ℝ))^6)+
      C*((n : ℝ)^a*(Real.log (n : ℝ))^6) := by ring
    _ ≤ ε*(n : ℝ)/2+ε*(n : ℝ)/2 := add_le_add hfirst hsecond
    _ = ε*(n : ℝ) := by ring
theorem V1m9 (n Y : ℕ) (hn : 2 ≤ n)
    (hlog : 1 ≤ Real.log (n : ℝ))
    (hY : (Y : ℝ) ≤ 2*(n : ℝ)/(Real.log (n : ℝ))^12)
    (hQ : (narrow n : ℝ) ≤ 16*(Real.log (n : ℝ))^2)
    (hh : ∀ q ∈ Icc 1 (narrow n), 0 < V15 n q ∧
      (V15 n q : ℝ) ≤ (n : ℝ)^(3/4 : ℝ)) :
    Vb8 n Y ≤ 2048*((n : ℝ)/(Real.log (n : ℝ))^6+
      (n : ℝ)^(3/4 : ℝ)*(Real.log (n : ℝ))^6) := by
  have hL : 0 < Real.log (n : ℝ) := lt_of_lt_of_le zero_lt_one hlog
  have hr : 0 ≤ (n : ℝ)^(3/4 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  let hmax : ℕ := ⌊(n : ℝ)^(3/4 : ℝ)⌋₊
  have hmax_bound : ∀ q ∈ Icc 1 (narrow n), V15 n q ≤ hmax := by
    intro q hq
    exact Nat.le_floor (hh q hq).2
  have hmaxR : (hmax : ℝ) ≤ (n : ℝ)^(3/4 : ℝ) := Nat.floor_le hr
  have hplus : (1+Real.log (n : ℝ))^2 ≤ 4*(Real.log (n : ℝ))^2 := by
    nlinarith
  have hYH : ((Y+2*hmax : ℕ) : ℝ) ≤
      2*(n : ℝ)/(Real.log (n : ℝ))^12+2*(n : ℝ)^(3/4 : ℝ) := by
    push_cast
    linarith
  have hQsq : (narrow n : ℝ)^2 ≤ (16*(Real.log (n : ℝ))^2)^2 := by
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hQ _
  calc
    _ ≤ (1+Real.log (n : ℝ))^2 * ((Y+2*hmax : ℕ) : ℝ) * (narrow n : ℝ)^2 :=
      V9i.V1xg n Y hmax (by omega)
        (fun q hq => (hh q hq).1) hmax_bound
    _ ≤ (4*(Real.log (n : ℝ))^2) *
        (2*(n : ℝ)/(Real.log (n : ℝ))^12+2*(n : ℝ)^(3/4 : ℝ)) *
          (16*(Real.log (n : ℝ))^2)^2 := by
      exact mul_le_mul (mul_le_mul hplus hYH (Nat.cast_nonneg _) (by positivity))
        hQsq (sq_nonneg _) (by positivity)
    _ = _ := by field_simp; ring
theorem V1js (Y : ℕ → ℕ)
    (hgeo : ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ 1 ≤ Real.log (n : ℝ) ∧
      (Y n : ℝ) ≤ 2*(n : ℝ)/(Real.log (n : ℝ))^12 ∧
      (narrow n : ℝ) ≤ 16*(Real.log (n : ℝ))^2 ∧
      ∀ q ∈ Icc 1 (narrow n), 0 < V15 n q ∧
        (V15 n q : ℝ) ≤ (n : ℝ)^(3/4 : ℝ)) :
    V3d (fun n => Vb8 n (Y n)) := by
  apply V1pa (a:=3/4) (by norm_num)
  refine ⟨2048, by norm_num, ?_⟩
  filter_upwards [hgeo] with n hn
  exact V1m9 n (Y n) hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2
theorem V1bg (Y : ℕ → ℕ)
    (hbulk : V3d (fun n => Vic n (Y n)))
    (hboundary : V3d (fun n => Vb8 n (Y n))) :
    V3d Vfb := by
  intro ε hε
  filter_upwards [hbulk (ε/2) (by positivity), hboundary (ε/2) (by positivity)]
    with n hb he
  rw [V9i.V1yg n (Y n)]
  linarith
end Vg4
end
section
open Filter Finset
open scoped Topology Classical
namespace V19d
open Vbi (Vv8)
open Vfn (start)
open V9i (Vic Vb8)
open V8j (V3d)
open V3z (Vfb)
theorem V218 : V3d (fun n => Vb8 n (start n)) :=
  Vg4.V1js start
    Vfn.V1j3
theorem V1yd (hMean : Vv8) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ n : ℕ in atTop,
      Vic n (start n) ≤ C*(n:ℝ)/(Real.log (n:ℝ))^7 := by
  obtain ⟨C,hC,X₀,hmean⟩ := hMean
  refine ⟨4194304*C, by positivity, ?_⟩
  filter_upwards [Vfn.Vy1,
    Vfn.V1w8.eventually_ge_atTop X₀] with n hp hX₀
  apply V1ub.V1s9 n (start n) X₀ C hC.le
    hp.start_ge_two hp.start_le hX₀ hp.log_ge_one hp.start_log hp.narrow_le_log
    ?_ hmean
  intro q hq
  have hh := hp.window_bounds q hq
  exact ⟨hh.1,hh.2.1,hh.2.2.2.1,hh.2.2.2.2⟩
theorem V1ej (hMean : Vv8) :
    V3d (fun n => Vic n (start n)) := by
  obtain ⟨C,hC,hrate⟩ := V1yd hMean
  intro ε hε
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hpow : Tendsto (fun n : ℕ => (Real.log (n:ℝ))^7) atTop atTop :=
    (tendsto_pow_atTop (by decide : (7:ℕ)≠0)).comp hlog
  filter_upwards [hrate,hpow.eventually_ge_atTop (C/ε)] with n hbound hlarge
  have hL : 0<(Real.log (n:ℝ))^7 := (div_pos hC hε).trans_le hlarge
  apply hbound.trans
  apply (div_le_iff₀ hL).2
  have hh := (div_le_iff₀ hε).1 hlarge
  have hm := mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg (α:=ℝ) n)
  nlinarith
theorem V10v (hMean : Vv8) :
    V3d Vfb :=
  Vg4.V1bg start
    (V1ej hMean) V218
theorem V1dp (hMean : Vv8) :
  let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowSkirt := fun n : ℕ => intervalIntegral (fun t => (lowWideArcs n \ arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (lowSkirt n).re := by
  exact V3z.V1ti
    (V10v hMean)
end V19d
end
section
open Filter Finset MeasureTheory
open scoped Topology Interval BigOperators Classical
namespace V16i
open V2h (V4z V9a)
open V3z (V6v)
open V7d (V6t)
open V54 (V76)
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
private theorem Vod (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) :
    ‖V76 k‖ ≤ Real.log (n : ℝ) := by
  unfold V76
  by_cases hp : k.Prime
  · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hp.one_lt.le
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hp.pos
    have hkn : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
    simp only [hp, ite_true, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg hk1)]
    exact Real.log_le_log hk0 hkn
  · simp only [hp, ite_false, Complex.ofReal_zero, norm_zero]
    exact Real.log_nonneg (by exact_mod_cast hn)
end V16i
end

private noncomputable def thetaF (q : ℕ) [NeZero q] (r : ZMod q) (y h : ℝ) : ℝ :=
  Finset.sum ((Finset.Icc (⌊y⌋₊+1) ⌊y+h⌋₊).filter (fun k : ℕ => (k:ZMod q)=r)) (fun k => if k.Prime then Real.log (k:ℝ) else 0)

private noncomputable def EF (q : ℕ) (h y : ℝ) : ℝ :=
  if hq : q=0 then (0:ℝ) else (letI : NeZero q := ⟨hq⟩; (Finset.univ : Finset (ZMod q)).sup' Finset.univ_nonempty (fun r => if IsUnit r then |thetaF q r y h - h/(q.totient:ℝ)| else 0))

private lemma EF_nonneg (q : ℕ) (h y : ℝ) : 0 ≤ EF q h y := by
  unfold EF
  split_ifs with hq
  · exact le_rfl
  · letI : NeZero q := ⟨hq⟩
    refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ (0 : ZMod q)))
    split_ifs <;> positivity

private lemma EF_floor (q : ℕ) (h : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    EF q (h:ℝ) y = EF q (h:ℝ) ((⌊y⌋₊ : ℕ) : ℝ) := by
  have e1 : ⌊y+(h:ℝ)⌋₊ = ⌊y⌋₊+h := Nat.floor_add_natCast hy h
  have e2 : ⌊((⌊y⌋₊ : ℕ) : ℝ)+(h:ℝ)⌋₊ = ⌊y⌋₊+h := by
    rw [show ((⌊y⌋₊ : ℕ) : ℝ)+(h:ℝ) = ((⌊y⌋₊+h : ℕ) : ℝ) by push_cast; ring]
    exact Nat.floor_natCast _
  simp only [EF, thetaF, e1, e2, Nat.floor_natCast]

private lemma V4z_le (q : ℕ) [NeZero q] (h r : ℕ) :
    V2h.V4z q h (r:ℝ) ≤ EF q (h:ℝ) (r:ℝ) := by
  unfold V2h.V4z V3z.V6v
  apply Finset.sup'_le
  intro u hu
  have hu' : IsUnit u := (Finset.mem_filter.mp hu).2
  have hq : q ≠ 0 := NeZero.ne q
  have hmem : (Finset.univ : Finset (ZMod q)).sup' Finset.univ_nonempty (fun r' => if IsUnit r' then |thetaF q r' (r:ℝ) (h:ℝ) - (h:ℝ)/(q.totient:ℝ)| else 0) ≥ |thetaF q u (r:ℝ) (h:ℝ) - (h:ℝ)/(q.totient:ℝ)| := by
    refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ u))
    simp [hu']
  have hEF : EF q (h:ℝ) (r:ℝ) = (Finset.univ : Finset (ZMod q)).sup' Finset.univ_nonempty (fun r' => if IsUnit r' then |thetaF q r' (r:ℝ) (h:ℝ) - (h:ℝ)/(q.totient:ℝ)| else 0) := by
    simp only [EF, dif_neg hq]
  rw [hEF]
  refine le_trans ?_ hmem
  have hI : V2h.V9a h (r:ℝ) = Finset.Icc (⌊(r:ℝ)⌋₊+1) ⌊(r:ℝ)+(h:ℝ)⌋₊ := by
    have e1 : ⌊(r:ℝ)+(h:ℝ)⌋₊ = r+h := by
      rw [← Nat.cast_add]; exact Nat.floor_natCast _
    rw [e1, Nat.floor_natCast]
    ext k; simp [V2h.V9a]
  have hcard : (V2h.V9a h (r:ℝ)).card = h := by simp [V2h.V9a]
  unfold V7d.V6t
  rw [hcard, hI]
  unfold V7d.Vj0 thetaF
  refine le_of_eq ?_
  rw [← Real.norm_eq_abs, ← Complex.norm_real]
  congr 1
  simp [V54.V76]

private theorem bridge (hA : ∃ C : ℝ, 0<C ∧ ∃ X : ℕ, ∀ x t : ℝ, (X:ℝ)≤x → 1≤x → 5/8≤t → t≤1 → ∀ Q : ℕ, 1≤Q → (Q:ℝ)^2*x^((1-t)/3+1/16) ≤ x^t → intervalIntegral (fun y => Finset.sum (Finset.Icc 1 Q) (fun q => EF q (x^t) y)) x (2*x) MeasureTheory.volume ≤ C*x*x^t/(Real.log x)^18) : Vbi.Vv8 := by
  obtain ⟨C,hC,X0,hh⟩ := hA
  refine ⟨C, hC, max X0 3, ?_⟩
  intro q inst X h hX hX2 hh0 hhX hq2 h58
  have hX0 : X0 ≤ X := le_trans (le_max_left _ _) hX
  have hX3 : 3 ≤ X := le_trans (le_max_right _ _) hX
  have hx3 : (3:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX3
  have hx1 : (1:ℝ) ≤ (X:ℝ) := by linarith
  have hxpos : (0:ℝ) < (X:ℝ) := by linarith
  have hlogX : 1 ≤ Real.log (X:ℝ) := by
    have := Real.exp_one_lt_d9
    rw [Real.le_log_iff_exp_le hxpos]
    linarith
  have hhpos : (0:ℝ) < (h:ℝ) := by exact_mod_cast hh0
  set t : ℝ := Real.log (h:ℝ) / Real.log (X:ℝ) with ht
  have hxt : (X:ℝ)^t = (h:ℝ) := by
    rw [Real.rpow_def_of_pos hxpos, ht, mul_div_cancel₀ _ (by linarith : Real.log (X:ℝ) ≠ 0), Real.exp_log hhpos]
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one (by linarith)]
    exact Real.log_le_log hhpos (by exact_mod_cast hhX)
  have ht58 : 5/8 ≤ t := by
    rw [ht, le_div_iff₀ (by linarith)]
    have := Real.log_le_log (Real.rpow_pos_of_pos hxpos _) h58
    rw [Real.log_rpow hxpos] at this
    linarith
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1R : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
  have hcond : (q:ℝ)^2*(X:ℝ)^((1-t)/3+1/16) ≤ (X:ℝ)^t := by
    rw [hxt]
    refine le_trans ?_ hq2
    gcongr
    have he : (1-t)/3+1/16 ≤ 7/12 := by linarith
    exact he
  have key := hh (X:ℝ) t (by exact_mod_cast hX0) hx1 ht58 ht1 q hq1 hcond
  rw [hxt] at key
  have hX2' : ((2*X:ℕ):ℝ) = 2*(X:ℝ) := by push_cast; ring
  rw [hX2']
  set F : ℕ → ℝ := fun r => Finset.sum (Finset.Icc 1 q) (fun q' => EF q' (h:ℝ) (r:ℝ)) with hF
  have hint : (∫ y in (X:ℝ)..(2*(X:ℝ)), F ⌊y⌋₊) = Finset.sum (Finset.Ico X (2*X)) F := by
    have := V2h.V8z F (a := X) (b := 2*X) (by omega)
    rw [this]
    push_cast
    rfl
  have heq : (∫ y in (X:ℝ)..(2*(X:ℝ)), F ⌊y⌋₊) = intervalIntegral (fun y => Finset.sum (Finset.Icc 1 q) (fun q' => EF q' (h:ℝ) y)) (X:ℝ) (2*(X:ℝ)) MeasureTheory.volume := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hy0 : 0 ≤ y := by
      rw [Set.uIcc_of_le (by linarith)] at hy
      linarith [hy.1]
    exact Finset.sum_congr rfl (fun q' _ => (EF_floor q' h y hy0).symm)
  have hsum : Finset.sum (Finset.Ico X (2*X)) (fun r => V2h.V4z q h (r:ℝ)) ≤ Finset.sum (Finset.Ico X (2*X)) F := by
    apply Finset.sum_le_sum
    intro r _
    refine le_trans (V4z_le q h r) ?_
    exact Finset.single_le_sum (f := fun q' => EF q' (h:ℝ) (r:ℝ)) (fun i _ => EF_nonneg _ _ _) (Finset.mem_Icc.mpr ⟨hq1, le_rfl⟩)
  have hV := V2h.Vh1 q h (a := X) (b := 2*X) (by omega)
  rw [show (((2*X:ℕ)):ℝ) = 2*(X:ℝ) from hX2'] at hV
  rw [← hV]
  refine le_trans hsum ?_
  rw [← hint, heq]
  refine le_trans key ?_
  have hlog12 : (Real.log (X:ℝ))^12 ≤ (Real.log (X:ℝ))^18 := pow_le_pow_right₀ hlogX (by norm_num)
  have hp12 : 0 < (Real.log (X:ℝ))^12 := by positivity
  have hn : 0 ≤ C * (X:ℝ) * (h:ℝ) := by positivity
  calc C * (X:ℝ) * (h:ℝ) / (Real.log (X:ℝ))^18 ≤ C * (X:ℝ) * (h:ℝ) / (Real.log (X:ℝ))^12 :=
        div_le_div_of_nonneg_left hn hp12 hlog12
    _ = C * (h:ℝ) * (X:ℝ) / (Real.log (X:ℝ))^12 := by ring

theorem Conjectures.Goldbach.LowSkirtFromShortProgressions :
    (let theta := fun (q : ℕ) [NeZero q] (r : ZMod q) (y h : ℝ) => Finset.sum ((Finset.Icc (⌊y⌋₊+1) ⌊y+h⌋₊).filter (fun k : ℕ => (k:ZMod q)=r)) (fun k => if k.Prime then Real.log (k:ℝ) else 0); let E := fun (q : ℕ) (h y : ℝ) => if hq : q=0 then (0:ℝ) else (letI : NeZero q := ⟨hq⟩; (Finset.univ : Finset (ZMod q)).sup' Finset.univ_nonempty (fun r => if IsUnit r then |theta q r y h - h/(q.totient:ℝ)| else 0)); ∃ C : ℝ, 0<C ∧ ∃ X : ℕ, ∀ x t : ℝ, (X:ℝ)≤x → 1≤x → 5/8≤t → t≤1 → ∀ Q : ℕ, 1≤Q → (Q:ℝ)^2*x^((1-t)/3+1/16) ≤ x^t → intervalIntegral (fun y => Finset.sum (Finset.Icc 1 Q) (fun q => E q (x^t) y)) x (2*x) MeasureTheory.volume ≤ C*x*x^t/(Real.log x)^18) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowSkirt := fun n : ℕ => intervalIntegral (fun t => (lowWideArcs n \ arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (lowSkirt n).re) := by
  intro hA
  exact V19d.V1dp (bridge hA)

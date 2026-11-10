module

public import ArtinMatthews.SourceProbeLogDilation
public import ArtinMatthews.SourceProbeW1
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain
open Function Set VaryingKummerAnalytic
open scoped NumberField Classical ContDiff
noncomputable section

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "A" => SLocalAdditiveCompletionSpace K S
local notation "CPlaces" => {w : InfinitePlace K // IsComplex w}

/-- The actual profile in the logarithm of `q_s/Y`, including the scalar from the physical row. -/
def sourceProbeLogProfile (y : A) (t : ℝ) : ℂ :=
  (Real.exp (-t / 2) : ℂ) * sourceProbeW1Complex (Real.exp t) *
    sourceSLocalCompletionProbe K S (sourceProbeLogDilate K hζ S (-t) y)

omit [IsTotallyComplex K] in
theorem sourceProbeLogProfile_tsupport (y : A) :
    tsupport (sourceProbeLogProfile K hζ S y) ⊆
      Icc (Real.log (3 / 2)) (Real.log (5 / 2)) := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  have hw : sourceProbeW1Complex (Real.exp t) ≠ 0 := by
    intro hz
    apply ht
    rw [sourceProbeLogProfile, hz, mul_zero, zero_mul]
  have h := subset_tsupport sourceProbeW1Complex hw
  rw [sourceProbeW1Complex_tsupport] at h
  exact ⟨(Real.log_le_log (by norm_num) h.1).trans_eq (Real.log_exp t),
    (Real.log_exp t).symm.trans_le (Real.log_le_log (Real.exp_pos t) h.2)⟩

theorem sourceProbeLogSupport_subset_period :
    Icc (Real.log (3 / 2)) (Real.log (5 / 2)) ⊆ Ioo (0 : ℝ) 1 := by
  have hlo : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hhi : Real.log (5 / 2) < 1 := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (by norm_num) ((by norm_num : (5 / 2 : ℝ) < 2.7182818283).trans
      Real.exp_one_gt_d9)
  exact fun _ h => ⟨hlo.trans_le h.1, h.2.trans_lt hhi⟩

theorem sourceProbeLogProfile_zero_outside_enlarged {y : A}
    (hy : y ∉ sourceProbeEnlargedAnnulus K hζ S) :
    sourceProbeLogProfile K hζ S y = 0 := by
  funext t
  by_contra ht
  have hp : sourceSLocalCompletionProbe K S (sourceProbeLogDilate K hζ S (-t) y) ≠ 0 := by
    intro hz
    apply ht
    rw [sourceProbeLogProfile, hz, mul_zero, Pi.zero_apply]
  exact hy ⟨(t, sourceProbeLogDilate K hζ S (-t) y),
    ⟨sourceProbeLogProfile_tsupport K hζ S y (subset_tsupport _ ht), subset_tsupport _ hp⟩,
    sourceProbeLogDilate_cancel K hζ S t y⟩

private def sourceProbeLogArch (p : ℝ × (CPlaces → ℂ)) : ℂ :=
  (Real.exp (-p.1 / 2) : ℂ) * sourceProbeW1Complex (Real.exp p.1) *
    sourceComplexProductTest (fun w : CPlaces =>
      (Real.exp (-p.1 / (Module.finrank ℚ K : ℝ)) : ℂ) * p.2 w)

omit [IsTotallyComplex K] in
private theorem sourceProbeLogArch_contDiff : ContDiff ℝ ∞ (sourceProbeLogArch K) := by
  unfold sourceProbeLogArch
  apply ContDiff.mul
  · exact (Complex.ofRealCLM.contDiff.comp
      (Real.contDiff_exp.comp (contDiff_fst.neg.div_const 2))).mul
      (sourceProbeW1Complex_contDiff.comp (Real.contDiff_exp.comp contDiff_fst))
  · apply sourceComplexProductTest_smooth.comp
    apply contDiff_pi.mpr
    intro w
    exact (Complex.ofRealCLM.contDiff.comp
      (Real.contDiff_exp.comp (contDiff_fst.neg.div_const _))).mul
      ((contDiff_apply ℝ ℂ w).comp contDiff_snd)

private def sourceProbeLogArchPoint (p : ℝ × A) : ℝ × (CPlaces → ℂ) :=
  (p.1, (sourceSLocalCompletionHomeomorph K S p.2).1)

private theorem sourceProbeLogArchPoint_continuous :
    Continuous (sourceProbeLogArchPoint K S) :=
  continuous_fst.prodMk (continuous_fst.comp
    ((sourceSLocalCompletionHomeomorph K S).continuous.comp continuous_snd))

private theorem sourceProbeLogProfile_arch_finite (y : A) (t : ℝ) :
    sourceProbeLogProfile K hζ S y t = sourceProbeLogArch K (sourceProbeLogArchPoint K S (t, y)) *
      sourceFiniteUnitTest K S y.2 := by
  rw [sourceProbeLogProfile, sourceSLocalCompletionProbe_eq_coordinate]
  change _ * (sourceComplexProductTest ((sourceComplexPlaceAdeleEquiv K).symm
    (sourceProbeLogDilate K hζ S (-t) y).1) *
      sourceFiniteUnitTest K S (sourceProbeLogDilate K hζ S (-t) y).2) = _
  have hfinite : (sourceProbeLogDilate K hζ S (-t) y).2 = y.2 :=
    funext (sourceProbeLogDilate_finite K hζ S (-t) y)
  have harch : (sourceComplexPlaceAdeleEquiv K).symm (sourceProbeLogDilate K hζ S (-t) y).1 =
      fun w : CPlaces => (Real.exp (-t / (Module.finrank ℚ K : ℝ)) : ℂ) *
        (sourceComplexPlaceAdeleEquiv K).symm y.1 w := by
    funext w
    exact sourceProbeLogDilate_complex K hζ S (-t) y w.val
  rw [hfinite, harch, ← mul_assoc]
  rfl

theorem sourceProbeLogProfile_contDiff (y : A) : ContDiff ℝ ∞ (sourceProbeLogProfile K hζ S y) := by
  rw [show sourceProbeLogProfile K hζ S y = fun t =>
      sourceProbeLogArch K (sourceProbeLogArchPoint K S (t, y)) * sourceFiniteUnitTest K S y.2 from
    funext (sourceProbeLogProfile_arch_finite K hζ S y)]
  exact ((sourceProbeLogArch_contDiff K).comp (contDiff_id.prodMk contDiff_const)).mul contDiff_const

private theorem sourceProbeLogProfile_joint_continuous :
    Continuous (fun p : ℝ × A => sourceProbeLogProfile K hζ S p.2 p.1) := by
  simp_rw [sourceProbeLogProfile_arch_finite]
  exact ((sourceProbeLogArch_contDiff K).continuous.comp (sourceProbeLogArchPoint_continuous K S)).mul
    ((sourceFiniteUnitTest_locallyConstant K S).continuous.comp (continuous_snd.comp continuous_snd))

private def logSliceDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × E → ℂ) (p : ℝ × E) : ℂ := fderiv ℝ f p (1, 0)

private theorem logSliceDeriv_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × E → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (logSliceDeriv f) :=
  (hf.contDiff_fderiv_apply (by simp)).comp (contDiff_id.prodMk contDiff_const)

private theorem logSliceDeriv_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × E → ℂ} (hf : ContDiff ℝ ∞ f) (y : E) :
    deriv (fun t => f (t, y)) = fun t => logSliceDeriv f (t, y) := by
  funext t
  exact (((hf.differentiable (by simp) (t, y)).hasFDerivAt).comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))).deriv

private theorem sourceProbeLogProfile_joint_deriv2_continuous :
    Continuous (fun p : ℝ × A => deriv (deriv (sourceProbeLogProfile K hζ S p.2)) p.1) := by
  let f := sourceProbeLogArch K
  have hf : ContDiff ℝ ∞ f := sourceProbeLogArch_contDiff K
  have hEq (y : A) : sourceProbeLogProfile K hζ S y = fun t =>
      f (t, (sourceSLocalCompletionHomeomorph K S y).1) * sourceFiniteUnitTest K S y.2 :=
    funext (sourceProbeLogProfile_arch_finite K hζ S y)
  have h2 (y : A) (t : ℝ) : deriv (deriv (sourceProbeLogProfile K hζ S y)) t =
      logSliceDeriv (logSliceDeriv f) (sourceProbeLogArchPoint K S (t, y)) *
        sourceFiniteUnitTest K S y.2 := by
    rw [hEq, deriv_mul_const_field', logSliceDeriv_eq hf,
      deriv_mul_const_field', logSliceDeriv_eq (logSliceDeriv_smooth hf)]
    rfl
  simp_rw [h2]
  exact (((logSliceDeriv_smooth (logSliceDeriv_smooth hf)).continuous.comp
    (sourceProbeLogArchPoint_continuous K S))).mul
    ((sourceFiniteUnitTest_locallyConstant K S).continuous.comp (continuous_snd.comp continuous_snd))

/-- The compact annulus bounds the derivatives jointly, and the profile vanishes off that annulus. -/
theorem sourceProbeLogProfile_uniform_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : A) (t : ℝ), t ∈ Icc 0 1 →
      ‖sourceProbeLogProfile K hζ S y t‖ ≤ C ∧
      ‖deriv (deriv (sourceProbeLogProfile K hζ S y)) t‖ ≤ C := by
  let b (p : ℝ × A) := ‖sourceProbeLogProfile K hζ S p.2 p.1‖ +
    ‖deriv (deriv (sourceProbeLogProfile K hζ S p.2)) p.1‖
  have hb : Continuous b := (sourceProbeLogProfile_joint_continuous K hζ S).norm.add
    (sourceProbeLogProfile_joint_deriv2_continuous K hζ S).norm
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod
    (sourceProbeEnlargedAnnulus_isCompact K hζ S) |>.bddAbove_image hb.continuousOn
  refine ⟨max 0 C, le_max_left _ _, fun y t ht => ?_⟩
  by_cases hy : y ∈ sourceProbeEnlargedAnnulus K hζ S
  · have h : b (t, y) ≤ C := hC (mem_image_of_mem b ⟨ht, hy⟩)
    exact ⟨((le_add_of_nonneg_right (norm_nonneg _)).trans h).trans (le_max_right _ _),
      ((le_add_of_nonneg_left (norm_nonneg _)).trans h).trans (le_max_right _ _)⟩
  · rw [sourceProbeLogProfile_zero_outside_enlarged K hζ S hy]
    have hd : deriv (0 : ℝ → ℂ) = 0 := funext fun u => deriv_const u 0
    rw [hd, hd, Pi.zero_apply, norm_zero]
    exact ⟨le_max_left _ _, le_max_left _ _⟩

end
end ArtinMatthews.SourcePhysical

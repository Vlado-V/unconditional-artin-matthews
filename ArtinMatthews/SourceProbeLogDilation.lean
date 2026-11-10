module

public import ArtinMatthews.SourceSLocalAdditiveProbeBinding
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- The fixed scaling has exactly this coordinate at each complex completion. -/
theorem sLocalPositiveScaling_complex (w : InfinitePlace K) (hw : IsComplex w) (T : ℝ) :
    ringEquivComplexOfIsComplex hw ((sLocalPositiveScaling K hζ S T).1 w : w.Completion) =
      (Real.exp (Real.log T / (Module.finrank ℚ K : ℝ)) : ℂ) := by
  change ringEquivComplexOfIsComplex hw
    ((ringEquivComplexOfIsComplex hw).symm _) = _
  exact RingEquiv.apply_symm_apply _ _

/-- The paper's all-place section respects multiplication on positive reals. -/
theorem sLocalPositiveScaling_mul {T U : ℝ} (hT : 0 < T) (hU : 0 < U) :
    sLocalPositiveScaling K hζ S (T * U) =
      sLocalPositiveScaling K hζ S T * sLocalPositiveScaling K hζ S U := by
  apply Prod.ext
  · funext w
    apply Units.ext
    let hw := (source_isTotallyComplex K hζ).isComplex w
    apply (ringEquivComplexOfIsComplex hw).injective
    change ringEquivComplexOfIsComplex hw ((sLocalPositiveScaling K hζ S (T * U)).1 w : w.Completion) =
      ringEquivComplexOfIsComplex hw ((sLocalPositiveScaling K hζ S T).1 w *
        (sLocalPositiveScaling K hζ S U).1 w : w.Completionˣ)
    rw [Units.val_mul, map_mul, sLocalPositiveScaling_complex,
      sLocalPositiveScaling_complex, sLocalPositiveScaling_complex,
      Real.log_mul hT.ne' hU.ne', add_div, Real.exp_add, Complex.ofReal_mul]
  · funext w
    change (sLocalPositiveScaling K hζ S (T * U)).2 w =
      (sLocalPositiveScaling K hζ S T).2 w * (sLocalPositiveScaling K hζ S U).2 w
    simp only [sLocalPositiveScaling_finite, one_mul]

namespace SourcePhysical
open Set
variable [IsTotallyComplex K]
local notation "A" => SLocalAdditiveCompletionSpace K S

/-- Logarithmic dilation of the literal additive completion space by the actual unit section. -/
def sourceProbeLogDilate (t : ℝ) (y : A) : A :=
  y * sourceSLocalUnitAdditivePoint K S (sLocalPositiveScaling K hζ S (Real.exp t))

omit [IsTotallyComplex K] in
theorem sourceProbeLogDilate_finite (t : ℝ) (y : A) (p : S) :
    (sourceProbeLogDilate K hζ S t y).2 p = y.2 p := by
  change y.2 p * ((sLocalPositiveScaling K hζ S (Real.exp t)).2 p : p.val.adicCompletion K) = _
  simp only [sLocalPositiveScaling_finite, Units.val_one, mul_one]

theorem sourceProbeLogDilate_complex (t : ℝ) (y : A) (w : InfinitePlace K) :
    ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
        ((sourceProbeLogDilate K hζ S t y).1 w) =
      (Real.exp (t / (Module.finrank ℚ K : ℝ)) : ℂ) *
        ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w) (y.1 w) := by
  change ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
    (y.1 w * ((sLocalPositiveScaling K hζ S (Real.exp t)).1 w : w.Completion)) = _
  rw [map_mul, sLocalPositiveScaling_complex, Real.log_exp, mul_comm]

theorem sourceProbeLogDilate_continuous :
    Continuous (fun p : ℝ × A => sourceProbeLogDilate K hζ S p.1 p.2) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro w
    let hw := IsTotallyComplex.isComplex w
    let e := isometryEquivComplexOfIsComplex hw
    have hEq : (fun p : ℝ × A => (sourceProbeLogDilate K hζ S p.1 p.2).1 w) =
        fun p : ℝ × A => e.symm ((Real.exp (p.1 / (Module.finrank ℚ K : ℝ)) : ℂ) * e (p.2.1 w)) := by
      funext p
      apply e.injective
      rw [e.apply_symm_apply]
      exact sourceProbeLogDilate_complex K hζ S p.1 p.2 w
    change Continuous (fun p : ℝ × A => (sourceProbeLogDilate K hζ S p.1 p.2).1 w)
    rw [hEq]
    exact e.symm.continuous.comp
      ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_fst.div_const _))).mul
        (e.continuous.comp ((continuous_apply w).comp (continuous_fst.comp continuous_snd))))
  · convert (continuous_snd.comp continuous_snd : Continuous (fun p : ℝ × A => p.2.2)) using 1
    funext p w
    exact sourceProbeLogDilate_finite K hζ S p.1 p.2 w

theorem sourceProbeLogDilate_neg (t : ℝ) (y : A) :
    sourceProbeLogDilate K hζ S (-t) y =
      y * sourceSLocalUnitAdditivePoint K S (sLocalPositiveScaling K hζ S (Real.exp t))⁻¹ := by
  apply Prod.ext
  · funext w
    let hw := IsTotallyComplex.isComplex w
    let e := ringEquivComplexOfIsComplex hw
    apply e.injective
    rw [sourceProbeLogDilate_complex]
    change _ = e (y.1 w * (((sLocalPositiveScaling K hζ S (Real.exp t)).1 w)⁻¹ : w.Completionˣ))
    rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, sLocalPositiveScaling_complex, Real.log_exp,
      neg_div, Real.exp_neg, Complex.ofReal_inv, mul_comm]
  · funext p
    rw [sourceProbeLogDilate_finite]
    change y.2 p = y.2 p * (((sLocalPositiveScaling K hζ S (Real.exp t)).2 p)⁻¹ : (p.val.adicCompletion K)ˣ)
    rw [sLocalPositiveScaling_finite, inv_one, Units.val_one, mul_one]

theorem sourceProbeLogDilate_cancel (t : ℝ) (y : A) :
    sourceProbeLogDilate K hζ S t (sourceProbeLogDilate K hζ S (-t) y) = y := by
  rw [sourceProbeLogDilate_neg, sourceProbeLogDilate, mul_assoc,
    ← sourceSLocalUnitAdditivePoint_mul, inv_mul_cancel]
  rw [show sourceSLocalUnitAdditivePoint K S 1 = 1 from rfl, mul_one]

/-- The enlarged annulus is the exact compact positive dilation of the probe support. -/
def sourceProbeEnlargedAnnulus : Set A :=
  (fun p : ℝ × A => sourceProbeLogDilate K hζ S p.1 p.2) ''
    (Icc (Real.log (3 / 2)) (Real.log (5 / 2)) ×ˢ tsupport (sourceSLocalCompletionProbe K S))

theorem sourceProbeEnlargedAnnulus_isCompact :
    IsCompact (sourceProbeEnlargedAnnulus K hζ S) :=
  (isCompact_Icc.prod (sourceSLocalCompletionProbe_compactSupport K S)).image
    (sourceProbeLogDilate_continuous K hζ S)

theorem sourceProbeEnlargedAnnulus_away_zero {y : A}
    (hy : y ∈ sourceProbeEnlargedAnnulus K hζ S) :
    (∀ w : InfinitePlace K, y.1 w ≠ 0) ∧ (∀ p : S, y.2 p ≠ 0) := by
  obtain ⟨⟨t, x⟩, hx, rfl⟩ := hy
  have h := sourceSLocalCompletionProbe_support_away_zero K S hx.2
  refine ⟨fun w hw => ?_, fun p hp => h.2 p ((sourceProbeLogDilate_finite K hζ S t x p).symm ▸ hp)⟩
  have hz := sourceProbeLogDilate_complex K hζ S t x w
  rw [hw, map_zero, zero_eq_mul] at hz
  rcases hz with hz | hz
  · exact (Real.exp_ne_zero _) (by exact_mod_cast hz)
  · exact h.1 w ((ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).map_eq_zero_iff.mp hz)

end SourcePhysical
end
end ArtinMatthews

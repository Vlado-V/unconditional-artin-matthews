module

public import ArtinMatthews.SourceKPAdelicCompactSection
public import ArtinMatthews.SourceKPExteriorScattering
public import ArtinMatthews.SourceKPLocalReceiverBasis
public import ArtinMatthews.SourceKPLocalUnitFixed
public import ArtinMatthews.StandardLocalConductor
public import ArtinMatthews.SourceKPExceptionalLocalFactor
public import ArtinMatthews.SourceKPLocalReceiverSection
public import ArtinMatthews.SourceKPTameParametricOpenCell
public import ArtinMatthews.SourceKPTameSphericalIntertwiner
public import ArtinMatthews.StandardLocalBall
public import ArtinMatthews.StandardLocalFourier
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
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual local spherical integral transfers to every coordinate
of the global algebraic carrier through the three-basis receiver. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀) (s : ℂ)

local notation "L" => P.val.adicCompletion K
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "h₆" => source_exterior_six_not_mem K S₀ P.val P.property
local notation "V" => SourceKPAdelicTorusInducedSpace K hζ s
local notation "f₀" => sourceKPTameParametricSphericalSection K hζ P.val h₆ π₀ hπ₀ s
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P.val
local notation "μ₀" => sourceJacquetHaar K P.val

def sourceKPLocalReceiverCoordinate
    (v : sourceKPLocalUnitFixed K hζ P.val s) (t : sourceKPAdelicCoveringTorus K hζ) :
    (ZMod 3 → ℂ) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.proj t).comp
      ((SourceKPAdelicTorusInducedSpace K hζ s).subtype.comp
        (sourceKPLocalReceiver K hζ P.val π₀ s v.val)))

theorem sourceKPLocalReceiverCoordinate_apply
    (v : sourceKPLocalUnitFixed K hζ P.val s) (t : sourceKPAdelicCoveringTorus K hζ)
    (f : ZMod 3 → ℂ) :
    sourceKPLocalReceiverCoordinate K hζ S₀ P s v t f =
      (sourceKPLocalReceiver K hζ P.val π₀ s v.val f).val t := rfl

theorem sourceKPLocalReceiver_integrable
    (v : sourceKPLocalUnitFixed K hζ P.val s) (t : sourceKPAdelicCoveringTorus K hζ)
    (hP : P.val ∉ traceBadPlaces K) (hs : 0 < s.re) :
    Integrable (fun x : L =>
      (sourceKPLocalReceiver K hζ P.val π₀ s v.val
        ((f₀).val (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x)))).val t) μ₀ :=
  (sourceKPLocalReceiverCoordinate K hζ S₀ P s v t).integrable_comp
    (sourceKPTameSphericalIntertwiner_integrable K hζ S₀ P hP hs)

theorem sourceKPLocalReceiver_integral
    (v : sourceKPLocalUnitFixed K hζ P.val s) (t : sourceKPAdelicCoveringTorus K hζ)
    (hP : P.val ∉ traceBadPlaces K) (hs : 0 < s.re) :
    (∫ x : L, (sourceKPLocalReceiver K hζ P.val π₀ s v.val
      ((f₀).val (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x)))).val t ∂μ₀) =
        sourceKPUnramifiedScatteringFactor P.val s * v.val.val t := by
  let A := sourceKPLocalReceiverCoordinate K hζ S₀ P s v t
  change (∫ x : L, A ((f₀).val (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x))) ∂μ₀) = _
  rw [A.integral_comp_comm (sourceKPTameSphericalIntertwiner_integrable K hζ S₀ P hP hs)]
  change A (sourceKPTameSphericalIntertwiner K hζ S₀ P s) = _
  rw [sourceKPTameSphericalIntertwiner_eq K hζ S₀ P hP hs, map_smul]
  change sourceKPUnramifiedScatteringFactor P.val s *
    (sourceKPLocalReceiver K hζ P.val π₀ s v.val (sourceJacquetBasis 0)).val t = _
  rw [sourceKPLocalReceiver_zero]

theorem sourceKPLocalReceiver_unit_ball
    (v : sourceKPLocalUnitFixed K hζ P.val s) (t : sourceKPAdelicCoveringTorus K hζ) :
    (∫ x : L in sourceLocalBall K P.val 0,
      (sourceKPLocalReceiver K hζ P.val π₀ s v.val
        ((f₀).val (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x)))).val t ∂μ₀) = v.val.val t := by
  have he : ∀ x ∈ sourceLocalBall K P.val 0,
      (sourceKPLocalReceiver K hζ P.val π₀ s v.val
        ((f₀).val (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x)))).val t = v.val.val t := by
    intro x hx
    rw [sourceKPTameParametricSpherical_weyl_upper_integral K hζ S₀ P s x hx,
      sourceKPLocalReceiver_zero]
  rw [setIntegral_congr_fun (sourceLocalBall_isCompact K P.val 0).measurableSet he,
    integral_const, Measure.real, Measure.restrict_apply_univ,
    sourceLocalBall_zero_eq_integerOpen, sourceJacquetHaar_integers,
    ENNReal.toReal_one, one_smul]

theorem sourceKPLocalSphericalReceiver_integral
    (t : sourceKPAdelicCoveringTorus K hζ)
    (hP : P.val ∉ traceBadPlaces K) (hs : 0 < s.re) :
    (∫ x : L, ((sourceKPAdelicCompactSection K hζ s).val
      (sourceKPAdelicLocalProjective K hζ P.val
        (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x)))).val t ∂μ₀) =
      sourceKPUnramifiedScatteringFactor P.val s *
        (sourceKPAdelicUnitSphericalVector K hζ s).val t := by
  simp_rw [sourceKPLocalSphericalReceiver_section K hζ S₀ P s]
  exact sourceKPLocalReceiver_integral K hζ S₀ P s
    (sourceKPLocalSphericalFixedVector K hζ S₀ P s) t hP hs

theorem sourceKPLocalSphericalReceiver_unit_ball
    (t : sourceKPAdelicCoveringTorus K hζ) :
    (∫ x : L in sourceLocalBall K P.val 0,
      ((sourceKPAdelicCompactSection K hζ s).val
        (sourceKPAdelicLocalProjective K hζ P.val
          (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x)))).val t ∂μ₀) =
      (sourceKPAdelicUnitSphericalVector K hζ s).val t := by
  simp_rw [sourceKPLocalSphericalReceiver_section K hζ S₀ P s]
  exact sourceKPLocalReceiver_unit_ball K hζ S₀ P s
    (sourceKPLocalSphericalFixedVector K hζ S₀ P s) t

theorem sourceKPLocalSphericalReceiver_integral_one
    (hP : P.val ∉ traceBadPlaces K) (hs : 0 < s.re) :
    (∫ x : L, ((sourceKPAdelicCompactSection K hζ s).val
      (sourceKPAdelicLocalProjective K hζ P.val
        (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x)))).val 1 ∂μ₀) =
      sourceKPUnramifiedScatteringFactor P.val s := by
  rw [sourceKPLocalSphericalReceiver_integral K hζ S₀ P s 1 hP hs,
    sourceKPAdelicUnitSphericalVector_one, mul_one]

theorem sourceKPLocalSphericalReceiver_exceptional_ne_zero
    (hP : P.val ∉ traceBadPlaces K) :
    (∫ x : L, ((sourceKPAdelicCompactSection K hζ (1/6)).val
      (sourceKPAdelicLocalProjective K hζ P.val
        (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x)))).val 1 ∂μ₀) ≠ 0 := by
  rw [sourceKPLocalSphericalReceiver_integral_one K hζ S₀ P (1/6) hP (by norm_num)]
  exact sourceKPUnramifiedScatteringFactor_exceptional_ne_zero P.val

end
end ArtinMatthews

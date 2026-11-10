module

public import ArtinMatthews.SourceSLocalProbeFactors
public import ArtinMatthews.SourceSLocalSheetMellin
public import ArtinMatthews.SourceSLocalOtherMellin
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
open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory
open ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField Classical SchwartzMap ContDiff BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (v : InfinitePlace K)
local notation "hv" => (sourceSLocalComplexPlace K hζ v)

def sourceSLocalProbeRetained : SNormOneOtherUnits S v → ℂ :=
  sourceSheetOtherTensor S v (sourceProbeArchFactor K hζ) (sourceProbeFiniteFactor K S)

def sourceSLocalProbeFourierTensor : SWholeUnits K S → ℂ :=
  sourceSLocalChosenTensor S hv sourceProbeArchFourier (sourceSLocalProbeRetained K hζ S v)

def sourceSLocalProbeMellin (s : ℂ) : ℂ :=
  ∫ x, sourceSLocalWholeMellinIntegrand K hζ S v sourceProbeArchFourier
    (sourceSLocalProbeRetained K hζ S v) s x ∂sourceSLocalUnitProductMeasure K hζ S

def sourceSLocalProbeSheet (T : ℝ) : ℂ :=
  sourceSLocalSheetProfile S (sourceSLocalNormalizedSheetMeasure K hζ S v) hζ
    (sourceSLocalProbeFourierTensor K hζ S v) T

theorem sourceSLocalProbeRetained_measurable : Measurable (sourceSLocalProbeRetained K hζ S v) :=
  measurable_sourceSheetOtherTensor S v (sourceProbeArchFactor K hζ) (sourceProbeFiniteFactor K S)
    (fun w => sourceProbeArchFactor_measurable K hζ w.val) (sourceProbeFiniteFactor_measurable K S)

theorem sourceSLocalProbeRetained_weighted_norm_integrable (σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun y => ‖sourceSLocalProbeRetained K hζ S v y‖ * sourceSheetOtherNorm S v y ^ σ)
      (sourceSLocalOtherUnitMeasure K hζ S v) := by
  have : IsTotallyComplex K := source_isTotallyComplex K hζ
  exact sourceSheetOtherTensor_weighted_norm_integrable S v (sourceSLocalArchUnitMeasure K hζ)
    (sourceSLocalFiniteUnitMeasure K S) (sourceProbeArchFactor K hζ) (sourceProbeFiniteFactor K S) σ
    (fun w => sourceProbeArchFactor_weighted_norm_integrable K hζ w.val σ hσ)
    (fun p => sourceProbeFiniteFactor_weighted_norm_integrable K S p σ hσ)

theorem sourceSLocalProbeMellin_integrable (s : ℂ) (hs : 0 < s.re) :
    Integrable (sourceSLocalWholeMellinIntegrand K hζ S v sourceProbeArchFourier
      (sourceSLocalProbeRetained K hζ S v) s) (sourceSLocalUnitProductMeasure K hζ S) := by
  have : IsTotallyComplex K := source_isTotallyComplex K hζ
  apply sourceSLocalWholeMellinIntegrand_integrable K hζ S v _ _ s hs
  exact sourceSheetOtherMellinIntegrand_integrable S v (sourceSLocalArchUnitMeasure K hζ)
    (sourceSLocalFiniteUnitMeasure K S) (sourceProbeArchFactor K hζ) (sourceProbeFiniteFactor K S) s
    (fun w => sourceProbeArchFactor_measurable K hζ w.val) (sourceProbeFiniteFactor_measurable K S)
    (fun w => sourceProbeArchFactor_weighted_norm_integrable K hζ w.val s.re hs)
    (fun p => sourceProbeFiniteFactor_weighted_norm_integrable K S p s.re hs)

theorem sourceSLocalProbeMellin_eq_products (s : ℂ) :
    sourceSLocalProbeMellin K hζ S v s =
      sourceComplexMellin sourceProbeArchFourier s *
      ((∏ _ : {w : InfinitePlace K // w ≠ v}, sourceComplexMellin sourceProbeArchFourier s) *
        ∏ p : S, sourceLocalAnnularMellin K p.val s) := by
  have : IsTotallyComplex K := source_isTotallyComplex K hζ
  rw [sourceSLocalProbeMellin, sourceSLocalWholeMellin_eq_product]
  change _ * sourceSheetOtherMellin S v (sourceSLocalArchUnitMeasure K hζ)
    (sourceSLocalFiniteUnitMeasure K S) (sourceProbeArchFactor K hζ) (sourceProbeFiniteFactor K S) s = _
  rw [sourceSheetOtherMellin_eq_prod]
  simp_rw [sourceProbeArchFactor_mellin_eq, sourceProbeFiniteFactor_mellin_eq]

theorem sourceSLocalProbeMellin_sixth_ne_zero :
    sourceSLocalProbeMellin K hζ S v (1 / 6 : ℂ) ≠ 0 := by
  rw [sourceSLocalProbeMellin_eq_products]
  exact mul_ne_zero sourceProbeArchMellin_sixth_ne_zero
    (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun _ _ => sourceProbeArchMellin_sixth_ne_zero)
      (Finset.prod_ne_zero_iff.mpr fun p _ => sourceLocalAnnularMellin_sixth_ne_zero K p.val))

end
end ArtinMatthews.SourcePhysical

module

public import ArtinMatthews.SourceThetaRotatedSheetBounds
public import ArtinMatthews.SourceLocalMultiplicativeShell
public import ArtinMatthews.SourceSLocalOtherTensor
public import ArtinMatthews.SourceSLocalOtherMellin
public import ArtinMatthews.SourceThetaArchWeighted
public import ArtinMatthews.SourceThetaFiniteWeighted
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! Construction of a genuine rotated tensor from the source03 local
conditions. The weighted retained integral is derived from its finite
product of actual local factors and Haar measures. -/
namespace ArtinMatthews.SourceReflection

open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory
open ArtinMatthews.SourcePhysical
open scoped NumberField Classical ArtinMatthews.SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (v : InfinitePlace K)
variable (δ : ℝ)

def SourceThetaRotatedTensor.ofLocal
    (g : ℕ → Circle → ℝ → ℂ)
    (hg : ∀ j, Measurable (Function.uncurry (g j)))
    (hd : ∀ j θ t, HasDerivAt (g j θ) (g (j + 1) θ t) t)
    (hgb : ∀ (j : ℕ) (A : ℝ), 0 < A → ∃ C : ℝ, 0 ≤ C ∧ ∀ θ t,
      ‖g j θ t‖ ≤ C * min (Real.exp (δ * t)) (Real.exp (-A * t)))
    (fArch : ∀ w : InfinitePlace K, w.Completionˣ → ℂ)
    (hArch : ∀ w : {w : InfinitePlace K // w ≠ v}, Measurable (fArch w.val))
    (hArchBound : ∀ (w : {w : InfinitePlace K // w ≠ v}) (A : ℝ), 0 < A →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖fArch w.val z‖ ≤
        C * min ((sourceSheetArchNorm w.val z) ^ δ) ((sourceSheetArchNorm w.val z) ^ (-A)))
    (fFinite : ∀ p : S, (p.val.adicCompletion K)ˣ → ℂ)
    (hFinite : ∀ p, Continuous (fFinite p)) (n : S → ℤ) (B : S → ℝ) (hB : ∀ p, 0 ≤ B p)
    (hFiniteSupport : ∀ (p : S) (z : (p.val.adicCompletion K)ˣ),
      z ∉ sourceLocalMulBall K p.val (n p) → fFinite p z = 0)
    (hFiniteSmall : ∀ (p : S) (z : (p.val.adicCompletion K)ˣ), z ∈ sourceLocalMulBall K p.val 0 →
      ‖fFinite p z‖ ≤ B p * (sourceSheetFiniteNorm S p z) ^ δ) :
    SourceThetaRotatedTensor K S hζ v δ where
  localDeriv := g
  retained := sourceSheetOtherTensor S v fArch fFinite
  local_measurable := hg
  retained_measurable :=
    measurable_sourceSheetOtherTensor S v fArch fFinite hArch (fun p => (hFinite p).measurable)
  local_hasDerivAt := hd
  local_weighted j σ hσ := sourceThetaLogFactor_weighted hσ (hgb j)
  retained_weighted σ hσ := by
    let := source_isTotallyComplex K hζ
    exact sourceSheetOtherTensor_weighted_norm_integrable S v (sourceSLocalArchUnitMeasure K hζ)
      (sourceSLocalFiniteUnitMeasure K S) fArch fFinite σ
      (fun w => sourceThetaArchFactor_weighted_integrable K hζ w.val (fArch w.val)
        (hArch w) hσ (hArchBound w))
      (fun p => sourceThetaFiniteFactor_weighted_integrable K p.val (fFinite p) (hFinite p)
        δ σ (B p) (hB p) hσ (n p) (hFiniteSupport p) (hFiniteSmall p))

end
end ArtinMatthews.SourceReflection

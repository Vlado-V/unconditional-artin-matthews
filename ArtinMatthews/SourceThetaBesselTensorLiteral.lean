module

public import ArtinMatthews.SourceThetaBesselTensor
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

/-! The constructed analytic tensor is the literal product of the
source03 completed Bessel factors and the supplied finite factors. -/
namespace ArtinMatthews.SourceReflection

open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory
open ArtinMatthews.SourcePhysical
open scoped NumberField Classical ArtinMatthews.SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (v : InfinitePlace K)
variable (c : InfinitePlace K → ℝ) (hc : ∀ w, 0 < c w)
variable (m : InfinitePlace K → ℤ) (δ : ℝ) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 5 / 6)
variable (fFinite : ∀ p : S, (p.val.adicCompletion K)ˣ → ℂ)
variable (hFinite : ∀ p, Continuous (fFinite p)) (n : S → ℤ) (B : S → ℝ) (hB : ∀ p, 0 ≤ B p)
variable (hSupport : ∀ (p : S) (z : (p.val.adicCompletion K)ˣ),
  z ∉ sourceLocalMulBall K p.val (n p) → fFinite p z = 0)
variable (hSmall : ∀ (p : S) (z : (p.val.adicCompletion K)ˣ), z ∈ sourceLocalMulBall K p.val 0 →
  ‖fFinite p z‖ ≤ B p * (sourceSheetFiniteNorm S p z) ^ δ)

local notation "D" => sourceThetaBesselTensor K S hζ v c hc m δ hδ hδ₁ fFinite hFinite n B hB hSupport hSmall

theorem sourceThetaBesselTensor_literal (x : SWholeUnits K S) :
    sourceThetaSLocalTensor K S hζ v ((D).localDeriv 0) (D).retained x =
      (∏ w, sourceThetaBesselCompletedFactor K hζ w (c w) (m w) (x.1 w)) *
        ∏ p, fFinite p (x.2 p) := by
  change sourceThetaBesselAngularLogDerivative (c v) (m v) 0
      (sourceComplexUnitAngle (sourceComplexPlaceUnitsEquiv (sourceSLocalComplexPlace K hζ v) (x.1 v)))
      (sourceComplexUnitLogNorm (sourceComplexPlaceUnitsEquiv (sourceSLocalComplexPlace K hζ v) (x.1 v))) *
      ((∏ w : {w : InfinitePlace K // w ≠ v},
        sourceThetaBesselCompletedFactor K hζ w.val (c w.val) (m w.val) (x.1 w.val)) *
          ∏ p, fFinite p (x.2 p)) = _
  rw [← sourceThetaBesselComplexFactor_eq_log (hc v)]
  change sourceThetaBesselCompletedFactor K hζ v (c v) (m v) (x.1 v) * _ = _
  rw [Fintype.prod_eq_mul_prod_subtype_ne (fun w : InfinitePlace K =>
    sourceThetaBesselCompletedFactor K hζ w (c w) (m w) (x.1 w)) v, mul_assoc]

end
end ArtinMatthews.SourceReflection

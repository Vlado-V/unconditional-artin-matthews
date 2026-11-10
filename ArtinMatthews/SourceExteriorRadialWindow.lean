module

public import ArtinMatthews.SourceAdelicOrbitHeightTopology
public import ArtinMatthews.SourceExteriorCompactMargin
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

namespace ArtinMatthews
open NumberField Set Filter
open scoped NumberField Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAutomorphic_radial_threshold_window (T : ℝ) (hT : 1 < T)
    {f : SourceKPAutomorphicLevel K hζ → ℂ} (hc : HasCompactSupport f)
    (hsupp : tsupport f ⊆ {x | T < sourceKPAutomorphicOrbitHeight K hζ x}) :
    ∀ᶠ t : ℝ in 𝓝 0,
      1 < Real.exp (2 * (InfinitePlace.nrComplexPlaces K : ℝ) * t) * T ∧
      tsupport f ⊆ {x | Real.exp (2 * (InfinitePlace.nrComplexPlaces K : ℝ) * t) * T <
        sourceKPAutomorphicOrbitHeight K hζ x} := by
  have hlim : Tendsto (fun t : ℝ => Real.exp (2 * (InfinitePlace.nrComplexPlaces K : ℝ) * t) * T)
      (𝓝 0) (𝓝 T) := by
    have hh : Continuous (fun t : ℝ => Real.exp (2 * (InfinitePlace.nrComplexPlaces K : ℝ) * t) * T) := by
      fun_prop
    simpa only [mul_zero, Real.exp_zero, one_mul] using hh.continuousAt.tendsto (x := (0 : ℝ))
  filter_upwards [hlim.eventually (eventually_gt_nhds hT),
    sourceKPAutomorphic_radial_threshold_support K hζ T hc hsupp] with t ht hs
  exact ⟨ht, fun x hx => hs x hx⟩

end
end ArtinMatthews

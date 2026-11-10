module

public import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace
public import ArtinMatthews.SpectralKLTestLimit
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

/-! Positive-spectrum distributional KL orthogonality for a smooth spectral
test on the open positive half-line. This is not an inversion, Plancherel,
or completeness assertion. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein
open scoped Topology ContDiff

namespace ArtinMatthews

theorem schlafliBesselK_product_mellin_smooth_test_limit (t : ℝ) (ht : 0 < t)
    (f : ℝ → ℂ) (hf : ContDiffOn ℝ ∞ f (Ioi (0 : ℝ)))
    (hfc : HasCompactSupport f) (hpos : tsupport f ⊆ Ioi (0 : ℝ)) :
    Tendsto (fun ε : ℝ => ∫ v in Ioi (0 : ℝ), f v *
      (∫ x in Ioi (0 : ℝ), (x : ℂ)^((ε : ℂ)-1)*
        schlafliBesselK ((t : ℂ)*Complex.I) x*schlafliBesselK ((v : ℂ)*Complex.I) x))
      (𝓝[>] (0 : ℝ)) (𝓝 ((Real.pi^2/(2*t*Real.sinh (Real.pi*t)) : ℝ) • f t)) := by
  exact schlafliBesselK_product_mellin_test_limit t ht f
    (hf.continuousOn.continuous_of_tsupport_subset isOpen_Ioi hpos) hfc hpos

end ArtinMatthews

module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Weak.Elliptic.L2
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import OAI.Analysis.PDE.Weak.Elliptic.Pairing
public import OAI.Analysis.PDE.Weak.Elliptic.TestSupport


set_option backward.privateInPublic true
@[expose] public section

noncomputable section
open Set _root_.MeasureTheory InnerProductSpace
namespace OAI.Analysis.PDE.Weak

variable {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem inner_differenceQuotientL2 (μ : Measure X) [μ.IsAddRightInvariant]
    (v : X) (h : ℝ) (u w : Lp V 2 μ) :
    inner ℝ (differenceQuotientL2 μ v h u) w =
      -inner ℝ u (differenceQuotientL2 μ v (-h) w) := by
  calc
    _ = ∫ x, inner ℝ (differenceQuotient v h u x) (w x) ∂μ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [coe_differenceQuotientL2 μ v h u] with x hx
      rw [hx]
    _ = -(∫ x, inner ℝ (u x) (differenceQuotient v (-h) w x) ∂μ) := by
      apply integral_differenceQuotient_inner
      · exact integrable_inner_of_memLp (Lp.memLp u) (Lp.memLp w)
      · exact integrable_inner_of_memLp
          ((Lp.memLp u).comp_measurePreserving (measurePreserving_add_right μ (h • v)))
          (Lp.memLp w)
    _ = _ := by
      rw [L2.inner_def]
      congr 1
      apply integral_congr_ae
      filter_upwards [coe_differenceQuotientL2 μ v (-h) w] with x hx
      rw [hx]

end OAI.Analysis.PDE.Weak

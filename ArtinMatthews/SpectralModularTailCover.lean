module

public import ArtinMatthews.SpectralCuspMass
public import Mathlib.NumberTheory.Modular
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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


set_option backward.privateInPublic true
@[expose] public section

/-! The two literal cusp strips covering a modular tail. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups

namespace ArtinMatthews

theorem modular_tail_two_strip_cover (N : ℕ) [NeZero N] (Y : ℝ) :
    {z : UpperHalfPlane | z ∈ ModularGroup.fd ∧ Y < z.im} ⊆
      hyperbolicCuspStrip (N : ℝ) Y ∪
        (fun z : UpperHalfPlane => ModularGroup.T • z) ⁻¹' hyperbolicCuspStrip (N : ℝ) Y := by
  intro z hz
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast (NeZero.one_le : 1 ≤ N)
  have hx := abs_le.mp hz.1.2
  by_cases hp : 0 < z.re
  · exact Or.inl ⟨⟨hp,by linarith [hx.2]⟩,hz.2⟩
  · right
    change (ModularGroup.T • z).re ∈ Ioc 0 (N : ℝ) ∧ Y < (ModularGroup.T • z).im
    rw [ModularGroup.re_T_smul,ModularGroup.im_T_smul]
    exact ⟨⟨by linarith [hx.1],by linarith [le_of_not_gt hp]⟩,hz.2⟩

end ArtinMatthews

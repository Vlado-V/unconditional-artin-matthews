module

public import ArtinMatthews.TameQuadraticGauss
public import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic
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
public import OAI.NumberTheory.DirichletL.FiniteFourier


set_option backward.privateInPublic true
@[expose] public section

/-! Exact phase of a finite quadratic sum, with its genuine sqrt(card)
Gauss normalization. -/

namespace ArtinMatthews.QuadraticWeil

open ArtinMatthews.QuadraticGauss
open OAI.SevenEighths OAI.SevenEighths.FiniteFourier
open OAI.RepresentationTheory.Weil.Local
open scoped Classical
noncomputable section

variable (F : Type) [Field F] [Fintype F]

theorem finite_quadratic_phase (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) :
    FunctionsMetaplectic.Construction.phase (∑ x : F, ψ (x ^ 2)) = residueIndex F ψ := by
  rw [square_sum_eq_gauss hF ψ hψ]
  have hn := primitive_gaussSum_norm (residueCharacter F)
    (primitiveOnIdeals_of_field _ (residueCharacter_nontrivial hF)) ψ
    (AddChar.IsPrimitive.of_ne_one hψ)
  rw [FunctionsMetaplectic.Construction.phase, hn]
  rfl

end

end ArtinMatthews.QuadraticWeil

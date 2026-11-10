module

public import ArtinMatthews.AnalyticWeilSquareClasses
public import ArtinMatthews.AdelicCharacterData
public import OAI.RepresentationTheory.Weil.AdelicSplitting.LocalCompact
public import ArtinMatthews.CompletionNondiscrete
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
public import OAI.RepresentationTheory.Weil.Local.Analytic


set_option backward.privateInPublic true
@[expose] public section

/-! Actual normalized analytic Weil indices of rational scalars at every
completion. Square invariance and nonvanishing are derived analytically. -/

namespace ArtinMatthews.QuadraticWeil

open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField Classical

noncomputable section

variable (F : Type) [Field F] [NumberField F]
  (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)
  (d : AdelicCharacterData F ψ)

def adelicNormalizedWeil (x : Fˣ) (v : ArchimedeanAdeles.Construction.Places F) : ℂ :=
  OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex
      (ArchimedeanAdeles.Construction.Completion F v)
      (Characters.Construction.localAdditiveCharacter F ψ v)
      (2 * ArchimedeanAdeles.Construction.rationalScalar F v (x : F)) /
    OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex
      (ArchimedeanAdeles.Construction.Completion F v)
      (Characters.Construction.localAdditiveCharacter F ψ v) 2

theorem adelicNormalizedWeil_eq_local (x : Fˣ)
    (v : ArchimedeanAdeles.Construction.Places F) :
    adelicNormalizedWeil F ψ x v =
      analyticNormalizedWeil (Characters.Construction.localAdditiveCharacter F ψ v)
        (Units.map (ArchimedeanAdeles.Construction.rationalScalar F v).toMonoidHom x) := rfl

include d in
theorem adelicNormalizedWeil_square_mul (x y : Fˣ)
    (v : ArchimedeanAdeles.Construction.Places F) :
    adelicNormalizedWeil F ψ (x * y ^ 2) v = adelicNormalizedWeil F ψ x v := by
  simpa only [adelicNormalizedWeil_eq_local, map_mul, map_pow] using
    analyticNormalizedWeil_square_mul (completion_nondiscrete F v)
      (Characters.Construction.localAdditiveCharacter F ψ v)
      (AdelicCharacterData.local_continuous F ψ d v)
      (AdelicCharacterData.local_unitary F ψ d v) (d.local_nontrivial v)
      (Units.map (ArchimedeanAdeles.Construction.rationalScalar F v).toMonoidHom x)
      (Units.map (ArchimedeanAdeles.Construction.rationalScalar F v).toMonoidHom y)

include d in
theorem adelicNormalizedWeil_eighth (x : Fˣ)
    (v : ArchimedeanAdeles.Construction.Places F) :
    adelicNormalizedWeil F ψ x v ^ 8 = 1 := by
  rw [adelicNormalizedWeil_eq_local]
  exact analyticNormalizedWeil_eighth (completion_nondiscrete F v)
    (Characters.Construction.localAdditiveCharacter F ψ v)
    (AdelicCharacterData.local_continuous F ψ d v)
    (AdelicCharacterData.local_unitary F ψ d v) (d.local_nontrivial v) _

include d in
theorem adelicNormalizedWeil_ne_zero (x : Fˣ)
    (v : ArchimedeanAdeles.Construction.Places F) :
    adelicNormalizedWeil F ψ x v ≠ 0 := by
  intro h
  have hh := adelicNormalizedWeil_eighth F ψ d x v
  rw [h, zero_pow (by decide)] at hh
  exact zero_ne_one hh

include d in
theorem adelicNormalizedWeil_one (v : ArchimedeanAdeles.Construction.Places F) :
    adelicNormalizedWeil F ψ 1 v = 1 := by
  have h := ((OAI.RepresentationTheory.Weil.Local.Analytic.Construction.localField_analytic_normalization
    (completion_nondiscrete F v) (Characters.Construction.localAdditiveCharacter F ψ v)
    (AdelicCharacterData.local_continuous F ψ d v)
    (AdelicCharacterData.local_unitary F ψ d v) (d.local_nontrivial v) 1).2.2.1 2
    (by norm_num)).2.2
  have hn : OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex
      (ArchimedeanAdeles.Construction.Completion F v)
      (Characters.Construction.localAdditiveCharacter F ψ v) 2 ≠ 0 := by
    intro hh
    rw [hh, zero_pow (by decide)] at h
    exact zero_ne_one h
  simpa only [adelicNormalizedWeil, Units.val_one, map_one, mul_one] using div_self hn

end

end ArtinMatthews.QuadraticWeil

module

public import ArtinMatthews.StandardLocalSquareWeil
public import ArtinMatthews.SLocalWeakApproximation
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

/-! The actual finite S-product of normalized analytic Weil indices,
defined on the genuine local square-class space, without a character premise. -/

namespace ArtinMatthews.QuadraticWeil

open NumberField IsDedekindDomain ClassFieldTheory
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField Classical

noncomputable section

variable (F : Type) [Field F] [NumberField F]
  (S : Finset (HeightOneSpectrum (𝓞 F)))

def sLocalAnalyticWeil (x : SLocalPowerClasses F 2 S) : ℂ :=
  ∏ v : S, standardLocalSquareWeil F v.1 (x v)

theorem sLocalAnalyticWeil_eighth (x : SLocalPowerClasses F 2 S) :
    sLocalAnalyticWeil F S x ^ 8 = 1 := by
  rw [sLocalAnalyticWeil, ← Finset.prod_pow]
  exact Finset.prod_eq_one (fun v _ => standardLocalSquareWeil_eighth F v.1 (x v))

theorem sLocalAnalyticWeil_ne_zero (x : SLocalPowerClasses F 2 S) :
    sLocalAnalyticWeil F S x ≠ 0 := by
  intro he
  have h := sLocalAnalyticWeil_eighth F S x
  rw [he, zero_pow (by decide)] at h
  exact zero_ne_one h

theorem sLocalAnalyticWeil_one : sLocalAnalyticWeil F S 1 = 1 := by
  apply Finset.prod_eq_one
  intro v _
  exact standardLocalSquareWeil_one F v.1

theorem sLocalAnalyticWeil_globalClass (a : Fˣ) :
    sLocalAnalyticWeil F S (sLocalGlobalClassMap F 2 S a) =
      ∏ v : S, standardNormalizedWeil F a (.inr v.1) := by
  apply Finset.prod_congr rfl
  intro v _
  rfl

end

end ArtinMatthews.QuadraticWeil

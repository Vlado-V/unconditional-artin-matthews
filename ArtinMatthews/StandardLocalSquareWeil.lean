module

public import ArtinMatthews.StandardAdelicWeilIndex
public import ClassFieldTheory.Definitions.HilbertSymbols.PowerClass
public import ArtinMatthews.CompletionNondiscrete
public import ArtinMatthews.StandardAdelicLocalNontrivial
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


set_option backward.privateInPublic true
@[expose] public section

/-! The actual local analytic Weil factor descends to the genuine square
class quotient at every finite place, including the wild places. -/

namespace ArtinMatthews.QuadraticWeil

open NumberField IsDedekindDomain ClassFieldTheory
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField Classical

noncomputable section

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local instance standardLocalCompletionCharZero : CharZero (v.adicCompletion F) :=
  ArchimedeanAdeles.Construction.completionCharZero F (.inr v)
local instance standardLocalCompletionMeasurable : MeasurableSpace (v.adicCompletion F) := borel (v.adicCompletion F)
local instance standardLocalCompletionBorel : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

def standardLocalWeil (x : (v.adicCompletion F)ˣ) : ℂ :=
  analyticNormalizedWeil (StandardAdelic.localFiniteCharacter F v) x

theorem standardLocalWeil_square_mul (x y : (v.adicCompletion F)ˣ) :
    standardLocalWeil F v (x * y ^ 2) = standardLocalWeil F v x :=
  analyticNormalizedWeil_square_mul (completion_nondiscrete F (.inr v))
    (StandardAdelic.localFiniteCharacter F v) (StandardAdelic.localFiniteCharacter_continuous F v)
    (StandardAdelic.localFiniteCharacter_unitary F v) (StandardAdelic.localFiniteCharacter_nontrivial F v) x y

theorem standardLocalWeil_eighth (x : (v.adicCompletion F)ˣ) : standardLocalWeil F v x ^ 8 = 1 :=
  analyticNormalizedWeil_eighth (completion_nondiscrete F (.inr v))
    (StandardAdelic.localFiniteCharacter F v) (StandardAdelic.localFiniteCharacter_continuous F v)
    (StandardAdelic.localFiniteCharacter_unitary F v) (StandardAdelic.localFiniteCharacter_nontrivial F v) x

theorem standardLocalWeil_one : standardLocalWeil F v 1 = 1 := by
  simpa only [standardNormalizedWeil, adelicNormalizedWeil, standardLocalWeil,
    analyticNormalizedWeil, StandardAdelic.localFiniteCharacter, Units.val_one, map_one, mul_one] using standardNormalizedWeil_one F (.inr v)

def standardLocalSquareWeil : PowerClassGroup (v.adicCompletion F) 2 → ℂ := by
  unfold PowerClassGroup
  refine Quotient.lift (standardLocalWeil F v) ?_
  intro a b hab
  obtain ⟨y, hy⟩ := QuotientGroup.leftRel_apply.mp hab
  have hy' : y ^ 2 = a⁻¹ * b := hy
  have hb : b = a * y ^ 2 := by rw [hy', mul_inv_cancel_left]
  rw [hb, standardLocalWeil_square_mul]

theorem standardLocalSquareWeil_powerClass (x : (v.adicCompletion F)ˣ) :
    standardLocalSquareWeil F v (powerClass (v.adicCompletion F) 2 x) = standardLocalWeil F v x := rfl

theorem standardLocalSquareWeil_eighth (x : PowerClassGroup (v.adicCompletion F) 2) :
    standardLocalSquareWeil F v x ^ 8 = 1 := by
  induction x using Quotient.inductionOn with
  | h x => exact standardLocalWeil_eighth F v x

theorem standardLocalSquareWeil_ne_zero (x : PowerClassGroup (v.adicCompletion F) 2) :
    standardLocalSquareWeil F v x ≠ 0 := by
  intro he
  have h := standardLocalSquareWeil_eighth F v x
  rw [he, zero_pow (by decide)] at h
  exact zero_ne_one h

theorem standardLocalSquareWeil_one : standardLocalSquareWeil F v 1 = 1 :=
  standardLocalWeil_one F v

end

end ArtinMatthews.QuadraticWeil

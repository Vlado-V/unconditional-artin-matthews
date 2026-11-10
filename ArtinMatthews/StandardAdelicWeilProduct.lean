module

public import ArtinMatthews.StandardAdelicWeilIndex
public import ArtinMatthews.AdelicWeilProduct
public import ArtinMatthews.StandardAdelicCharacterData
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


set_option backward.privateInPublic true
@[expose] public section

/-! Weil reciprocity for the actual standard adelic additive character.
Continuity, principal triviality, local nontriviality, and the conductor tail
are all derived for that character; no product or Fourier-family premise remains. -/

namespace ArtinMatthews.QuadraticWeil

open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField Classical

noncomputable section

variable (F : Type) [Field F] [NumberField F]

theorem standardGaussianIndex_hasProd (b : F) (hb : b ≠ 0) :
    HasProd (fun v : ArchimedeanAdeles.Construction.Places F =>
      OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex
        (ArchimedeanAdeles.Construction.Completion F v)
        (Characters.Construction.localAdditiveCharacter F (StandardAdelic.character F) v)
        (ArchimedeanAdeles.Construction.rationalScalar F v b)) 1 :=
  adelicGaussianIndex_hasProd F (StandardAdelic.character F) (StandardAdelic.character_data F) b hb

theorem standardNormalizedWeil_hasProd (x : Fˣ) : HasProd (standardNormalizedWeil F x) 1 :=
  adelicNormalizedWeil_hasProd F (StandardAdelic.character F) (StandardAdelic.character_data F) x


end

end ArtinMatthews.QuadraticWeil

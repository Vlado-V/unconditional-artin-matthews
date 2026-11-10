module

public import ArtinMatthews.AdelicWeilIndex
public import ArtinMatthews.BareRationalFourier
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
public import OAI.RepresentationTheory.Weil.AdelicSplitting.WeightedGaussianReciprocity


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine adelic quadratic Weil product, from the constructed bare
rational Fourier family and the actual adelic Poisson proof. -/

namespace ArtinMatthews.QuadraticWeil

open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField Classical

noncomputable section

variable (F : Type) [Field F] [NumberField F]
  (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)
  (d : AdelicCharacterData F ψ)

include d in
theorem adelicGaussianIndex_hasProd (b : F) (hb : b ≠ 0) :
    HasProd (fun v : ArchimedeanAdeles.Construction.Places F =>
      OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex
        (ArchimedeanAdeles.Construction.Completion F v)
        (Characters.Construction.localAdditiveCharacter F ψ v)
        (ArchimedeanAdeles.Construction.rationalScalar F v b)) 1 := by
  have h := WeightedGaussianReciprocity.Construction.gaussianIndex_rational_power_hasProd
    F 1 ψ d.continuous d.unitary d.principal d.local_nontrivial
    (character_positionHaar F ψ d 1) b hb
    (bareRationalFourierFamily F ψ d 1) (bareRationalFourierFamily_spec F ψ d 1)
  simpa only [pow_one] using h

include d in
theorem adelicNormalizedWeil_hasProd (x : Fˣ) : HasProd (adelicNormalizedWeil F ψ x) 1 := by
  have hnum := adelicGaussianIndex_hasProd F ψ d (2 * (x : F))
    (mul_ne_zero (by norm_num) x.ne_zero)
  have hden := adelicGaussianIndex_hasProd F ψ d 2 (by norm_num)
  have h := hnum.mul (hden.inv₀ one_ne_zero)
  change HasProd (fun v => adelicNormalizedWeil F ψ x v) 1
  simpa only [adelicNormalizedWeil, map_mul, map_ofNat, inv_one, mul_one, div_eq_mul_inv] using h

end

end ArtinMatthews.QuadraticWeil

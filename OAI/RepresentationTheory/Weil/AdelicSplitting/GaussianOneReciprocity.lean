module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.AdelicSplitting.FresnelOperators
public import OAI.RepresentationTheory.Weil.AdelicSplitting.TestFamilyAction
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import OAI.RepresentationTheory.Weil.AdelicSplitting.PositiveScalarProduct
public import OAI.RepresentationTheory.Weil.AdelicSplitting.ThetaFourierPositive
public import OAI.RepresentationTheory.Weil.AdelicSplitting.ThetaQuadratic


set_option backward.privateInPublic true
@[expose] public section

/-! # Gaussian One Reciprocity -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.GaussianOneReciprocity.Construction

noncomputable section

/-! Gaussian reciprocity for the standard scalar quadratic form, obtained
from actual Fourier-quadratic words and adelic Poisson positivity. -/

open scoped Classical
open _root_.MeasureTheory

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
variable (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ x, ‖ψ x‖ = 1)
variable (hp : ∀ q : F, ψ (algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q) = 1)
variable (hn : ∀ v : ArchimedeanAdeles.Construction.Places F, ∃ t : ArchimedeanAdeles.Construction.Completion F v, Characters.Construction.localAdditiveCharacter F ψ v t ≠ 1)
variable (hμ : ∀ v : ArchimedeanAdeles.Construction.Places F,
  (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v)).IsAddHaarMeasure)

include hp in
theorem rationalQuadratic_mem_positiveThetaSubgroup (B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F N) :
    QuadraticGenerators.Construction.rationalQuadraticFamily F N ψ hu hc B ∈ TestFamilyAction.Construction.positiveThetaSubgroup F N ψ := by
  intro f
  refine ⟨1, zero_lt_one, ?_⟩
  simpa only [Complex.ofReal_one, one_mul] using f.theta_rational_quadratic F N ψ hc hp B
    (QuadraticGenerators.Construction.rationalQuadraticFamily F N ψ hu hc B) (QuadraticGenerators.Construction.rationalQuadraticFamily_spec F N ψ hu hc B)

include hp hμ in
theorem gaussianPowerCircle_principal_hasProd (a : Rational.Construction.RestrictedCover F N ψ)
    (ha : Rational.Construction.IsRationalFourier F N ψ a) :
    HasProd (FresnelOperators.Construction.gaussianPowerCircle F N ψ hc hu hn) 1 := by
  let A := FresnelOperators.Construction.fresnelFirstWord F N ψ hc hu a
  let B := FresnelOperators.Construction.fresnelSecondWord F N ψ hc hu a
  let s := A * B⁻¹
  let P := TestFamilyAction.Construction.positiveThetaSubgroup F N ψ
  have hW : a ∈ P := ThetaFourierPositive.Construction.rationalFourier_mem_positiveThetaSubgroup F N ψ hc hu hp
    (fun v => hn (.inl v)) (fun v => hμ (.inr v)) (fun v => hμ (.inl v)) a ha
  have hQ : FresnelOperators.Construction.unitQuadraticFamily F N ψ hc hu ∈ P :=
    rationalQuadratic_mem_positiveThetaSubgroup F N ψ hc hu hp (FresnelAlgebra.Construction.unitSymmetricMatrix F N)
  have hQm : FresnelOperators.Construction.negativeUnitQuadraticFamily F N ψ hc hu ∈ P :=
    rationalQuadratic_mem_positiveThetaSubgroup F N ψ hc hu hp (FresnelAlgebra.Construction.negativeUnitSymmetricMatrix F N)
  have hA : A ∈ P := P.mul_mem (P.mul_mem hW hQ) hW
  have hB : B ∈ P := P.mul_mem (P.mul_mem hQm hW) hQm
  have hs : s ∈ P := P.mul_mem hA (P.inv_mem hB)
  apply PositiveScalarProduct.Construction.restricted_scalar_positive_hasProd_one F N ψ s hs (FresnelOperators.Construction.gaussianPowerCircle F N ψ hc hu hn)
  intro v
  change FresnelOperators.Construction.fresnelFirstWord F N ψ hc hu a v * (FresnelOperators.Construction.fresnelSecondWord F N ψ hc hu a v)⁻¹ = _
  rw [FresnelOperators.Construction.fresnel_words_scalar F N ψ hc hu hn a ha v, mul_inv_cancel_right]

include hc hu hp hn hμ in
theorem gaussianIndex_one_power_principal_hasProd (a : Rational.Construction.RestrictedCover F N ψ)
    (ha : Rational.Construction.IsRationalFourier F N ψ a) :
    HasProd (fun v : ArchimedeanAdeles.Construction.Places F => Local.FunctionsMetaplectic.Construction.gaussianIndex (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F ψ v) 1 ^ N) 1 := by
  have h := (gaussianPowerCircle_principal_hasProd F N ψ hc hu hp hn hμ a ha).map
    Circle.coeHom continuous_subtype_val
  exact h

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.GaussianOneReciprocity.Construction

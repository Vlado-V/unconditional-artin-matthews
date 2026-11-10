module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.AdelicSplitting.WeightedFresnelOperators
public import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedGeneratorKernels
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
public import Mathlib.Tactic.ENatToNat
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
public import OAI.RepresentationTheory.Weil.AdelicSplitting.GaussianOneReciprocity
public import OAI.RepresentationTheory.Weil.AdelicSplitting.PositiveScalarProduct
public import OAI.RepresentationTheory.Weil.AdelicSplitting.ThetaFourierPositive


set_option backward.privateInPublic true
@[expose] public section

/-! # Weighted Gaussian Reciprocity -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.WeightedGaussianReciprocity.Construction

noncomputable section

/-! Gaussian reciprocity for every nonzero rational coefficient, proved
from actual weighted Fourier-quadratic words and adelic Poisson positivity. -/

open scoped Classical
open _root_.MeasureTheory

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
variable (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ x, ‖ψ x‖ = 1)
variable (hp : ∀ q : F, ψ (algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q) = 1)
variable (hn : ∀ v : ArchimedeanAdeles.Construction.Places F, ∃ t : ArchimedeanAdeles.Construction.Completion F v, Characters.Construction.localAdditiveCharacter F ψ v t ≠ 1)
variable (hμ : ∀ v : ArchimedeanAdeles.Construction.Places F,
  (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v)).IsAddHaarMeasure)

include hp hμ in
theorem weightedGaussianPowerCircle_principal_hasProd (b : F) (hb : b ≠ 0)
    (a : Rational.Construction.RestrictedCover F N ψ) (ha : Rational.Construction.IsRationalFourier F N ψ a) :
    HasProd (WeightedFresnelOperators.Construction.weightedGaussianPowerCircle F N ψ hc hu hn b hb) 1 := by
  let A := WeightedFresnelOperators.Construction.weightedFresnelFirstWord F N ψ hc hu b a
  let B := WeightedFresnelOperators.Construction.weightedFresnelSecondWord F N ψ hc hu b hb a
  let s := A * B⁻¹
  let P := TestFamilyAction.Construction.positiveThetaSubgroup F N ψ
  have hW : a ∈ P := ThetaFourierPositive.Construction.rationalFourier_mem_positiveThetaSubgroup F N ψ hc hu hp
    (fun v => hn (.inl v)) (fun v => hμ (.inr v)) (fun v => hμ (.inl v)) a ha
  have hQ : WeightedFresnelOperators.Construction.scalarQuadraticFamily F N ψ hc hu b ∈ P :=
    GaussianOneReciprocity.Construction.rationalQuadratic_mem_positiveThetaSubgroup F N ψ hc hu hp (WeightedFresnelMatrices.Construction.scalarSymmetricMatrix F N b)
  have hQm : WeightedFresnelOperators.Construction.scalarQuadraticFamily F N ψ hc hu (-b⁻¹) ∈ P :=
    GaussianOneReciprocity.Construction.rationalQuadratic_mem_positiveThetaSubgroup F N ψ hc hu hp (WeightedFresnelMatrices.Construction.scalarSymmetricMatrix F N (-b⁻¹))
  have hL : WeightedFresnelOperators.Construction.scalarLeviFamily F N ψ b hb ∈ P := by
    obtain ⟨c, hc, ht⟩ := ThetaTest.Construction.theta_rational_levi_positive F N ψ (ScalarLeviNormalization.LocalAnalysis.scalarLinearMatrix N b hb)
      (WeightedFresnelOperators.Construction.scalarLeviFamily F N ψ b hb) (RationalLevi.Construction.rationalLeviFamily_spec F N ψ (ScalarLeviNormalization.LocalAnalysis.scalarLinearMatrix N b hb))
    exact fun f => ⟨c, hc, ht f⟩
  have hA : A ∈ P := P.mul_mem (P.mul_mem hW hQ) hW
  have hB : B ∈ P := P.mul_mem (P.mul_mem (P.mul_mem hQm hL) hW) hQm
  have hs : s ∈ P := P.mul_mem hA (P.inv_mem hB)
  apply PositiveScalarProduct.Construction.restricted_scalar_positive_hasProd_one F N ψ s hs (WeightedFresnelOperators.Construction.weightedGaussianPowerCircle F N ψ hc hu hn b hb)
  intro v
  change WeightedFresnelOperators.Construction.weightedFresnelFirstWord F N ψ hc hu b a v * (WeightedFresnelOperators.Construction.weightedFresnelSecondWord F N ψ hc hu b hb a v)⁻¹ = _
  rw [WeightedFresnelOperators.Construction.weighted_fresnel_words_scalar F N ψ hc hu hn b hb a ha v, mul_inv_cancel_right]

include hc hu hp hn hμ in
theorem gaussianIndex_rational_power_hasProd (b : F) (hb : b ≠ 0)
    (a : Rational.Construction.RestrictedCover F N ψ) (ha : Rational.Construction.IsRationalFourier F N ψ a) :
    HasProd (fun v : ArchimedeanAdeles.Construction.Places F => Local.FunctionsMetaplectic.Construction.gaussianIndex (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F ψ v) (ArchimedeanAdeles.Construction.rationalScalar F v b) ^ N) 1 :=
  (weightedGaussianPowerCircle_principal_hasProd F N ψ hc hu hp hn hμ b hb a ha).map
    Circle.coeHom continuous_subtype_val

include hc hu hp hn hμ in
theorem schrodingerWeil_rational_power_hasProd (d : F) (hd : d ≠ 0)
    (a : Rational.Construction.RestrictedCover F N ψ) (ha : Rational.Construction.IsRationalFourier F N ψ a) :
    HasProd (fun v : ArchimedeanAdeles.Construction.Places F =>
      CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F ψ v) (ArchimedeanAdeles.Construction.rationalScalar F v d) ^ N) 1 := by
  have h := (gaussianIndex_rational_power_hasProd F N ψ hc hu hp hn hμ (-1) (by simp) a ha).mul
    (gaussianIndex_rational_power_hasProd F N ψ hc hu hp hn hμ d hd a ha)
  simpa only [CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant, mul_pow, map_neg, map_one, one_mul] using! h

include hc hu hp hn hμ in
theorem schrodingerWeil_rational_inverse_power_hasProd (d : F) (hd : d ≠ 0)
    (a : Rational.Construction.RestrictedCover F N ψ) (ha : Rational.Construction.IsRationalFourier F N ψ a) :
    HasProd (fun v : ArchimedeanAdeles.Construction.Places F =>
      (CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F ψ v) (ArchimedeanAdeles.Construction.rationalScalar F v d))⁻¹ ^ N) 1 := by
  have h := (schrodingerWeil_rational_power_hasProd F N ψ hc hu hp hn hμ d hd a ha).inv₀ one_ne_zero
  simpa only [inv_one, inv_pow] using! h

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.WeightedGaussianReciprocity.Construction

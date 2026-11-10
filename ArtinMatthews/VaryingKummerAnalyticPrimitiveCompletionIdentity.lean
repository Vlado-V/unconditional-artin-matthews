module

public import ArtinMatthews.VaryingKummerAnalyticPrimitiveCompletion
public import ArtinMatthews.VaryingKummerAnalyticMixedGammaAnalytic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Convex.Contractible
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Global removal of the genuine Gamma and conductor factors from the
proper completion, with its exact positive-half-plane zero correspondence. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Set
open scoped NumberField nonZeroDivisors Classical
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥) (hMt : M ≠ ⊤)
variable (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
variable (hnp : ψ.IsNonprincipal)
include hnp

theorem primitiveContinued_eq_properCompleted_inverseGamma (s : ℂ) :
    ψ.primitiveContinued hM hprim s =
      (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^(-s) *
        mixedInverseGammaFactor K s * ψ.properCompleted hM hMt s := by
  have hA : (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mixedConductorScale_pos K (integralIdealFractionalUnit M hM)).ne'
  have hf : Differentiable ℂ (fun s : ℂ =>
      (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^(-s) *
        mixedInverseGammaFactor K s * ψ.properCompleted hM hMt s) :=
    (((differentiable_id.neg).const_cpow (Or.inl hA)).mul
      (mixedInverseGammaFactor_entire K)).mul (ψ.properCompleted_entire hM hMt hprim)
  have he : ψ.primitiveContinued hM hprim = fun s =>
      (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^(-s) *
        mixedInverseGammaFactor K s * ψ.properCompleted hM hMt s := by
    apply ((ψ.primitiveContinued_entire hM hprim).differentiableOn.analyticOnNhd
      isOpen_univ).eq_of_eventuallyEq (hf.differentiableOn.analyticOnNhd isOpen_univ) (z₀ := (2:ℂ))
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show 1 < (2:ℂ).re by norm_num)] with z hz
    rw [ψ.properCompleted_eq_gamma_primitive hM hMt hprim hnp hz,
      mixedInverseGammaFactor,Complex.cpow_neg]
    have hp : (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^z ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hA)
    have hg := mixedGammaFactor_ne_zero K (zero_lt_one.trans hz)
    field_simp
  exact congrFun he s

theorem properCompleted_eq_gamma_primitive_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    ψ.properCompleted hM hMt s =
      (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^s *
        mixedGammaFactor K s * ψ.primitiveContinued hM hprim s := by
  rw [ψ.primitiveContinued_eq_properCompleted_inverseGamma hM hMt hprim hnp s,
    mixedInverseGammaFactor,Complex.cpow_neg]
  have hp : (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr
      (mixedConductorScale_pos K (integralIdealFractionalUnit M hM)).ne'))
  have hg := mixedGammaFactor_ne_zero K hs
  field_simp

theorem properCompleted_zero_iff_primitive {s : ℂ} (hs : 0 < s.re) :
    ψ.properCompleted hM hMt s = 0 ↔ ψ.primitiveContinued hM hprim s = 0 := by
  rw [ψ.properCompleted_eq_gamma_primitive_of_re_pos hM hMt hprim hnp hs]
  have hp : (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr
      (mixedConductorScale_pos K (integralIdealFractionalUnit M hM)).ne'))
  simp only [mul_eq_zero,hp,mixedGammaFactor_ne_zero K hs,false_or]

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic

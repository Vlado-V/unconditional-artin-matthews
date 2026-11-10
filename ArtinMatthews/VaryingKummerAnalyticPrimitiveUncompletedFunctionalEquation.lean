module

public import ArtinMatthews.VaryingKummerAnalyticPrimitiveCompletedUnified
public import ArtinMatthews.VaryingKummerAnalyticRayIdealInverseNonprincipal
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


set_option backward.privateInPublic true
@[expose] public section

/-! The actual uncompleted primitive functional equation on the left
half-plane. The global inverse-Gamma identity is proved by analytic
continuation from the genuine positive-half-plane normalization. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Set
open scoped NumberField nonZeroDivisors Classical
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
variable (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
variable (hnp : ψ.IsNonprincipal)
include hnp

theorem primitiveContinued_eq_unified_inverseGamma (s : ℂ) :
    ψ.primitiveContinued hM hprim s =
      (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^(-s) *
        mixedInverseGammaFactor K s * ψ.primitiveCompletedUnified hM s := by
  have hA : (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mixedConductorScale_pos K (integralIdealFractionalUnit M hM)).ne'
  have hf : Differentiable ℂ (fun s : ℂ =>
      (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^(-s) *
        mixedInverseGammaFactor K s * ψ.primitiveCompletedUnified hM s) :=
    (((differentiable_id.neg).const_cpow (Or.inl hA)).mul
      (mixedInverseGammaFactor_entire K)).mul (ψ.primitiveCompletedUnified_entire hM hprim)
  have he : ψ.primitiveContinued hM hprim = fun s =>
      (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^(-s) *
        mixedInverseGammaFactor K s * ψ.primitiveCompletedUnified hM s := by
    apply ((ψ.primitiveContinued_entire hM hprim).differentiableOn.analyticOnNhd
      isOpen_univ).eq_of_eventuallyEq (hf.differentiableOn.analyticOnNhd isOpen_univ) (z₀ := (2:ℂ))
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show 0 < (2:ℂ).re by norm_num)] with z hz
    rw [ψ.primitiveCompletedUnified_eq_gamma_primitive hM hprim hnp hz,
      mixedInverseGammaFactor,Complex.cpow_neg]
    have hp : (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^z ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hA)
    have hg := mixedGammaFactor_ne_zero K hz
    field_simp
  exact congrFun he s

theorem primitiveContinued_left_functionalEquation :
    ∃ W : ℂ, ‖W‖=1 ∧ ∀ s : ℂ, s.re < 1 →
      ψ.primitiveContinued hM hprim s = W *
        ((mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^(1-2*s) *
          mixedGammaFactor K (1-s) * mixedInverseGammaFactor K s *
            ψ.inverse.primitiveContinued hM
              (ψ.inverse_isPrimitive hM hprim) (1-s)) := by
  obtain ⟨W,hW,hfe⟩ := ψ.primitiveCompletedUnified_functionalEquation hM hprim hnp
  refine ⟨W,hW,?_⟩
  intro s hs
  have hA : (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mixedConductorScale_pos K (integralIdealFractionalUnit M hM)).ne'
  have hi : 0 < (1-s).re := by simp only [Complex.sub_re,Complex.one_re]; linarith
  rw [ψ.primitiveContinued_eq_unified_inverseGamma hM hprim hnp s,hfe,
    ψ.inverse.primitiveCompletedUnified_eq_gamma_primitive hM
      (ψ.inverse_isPrimitive hM hprim) (ψ.inverse_isNonprincipal hnp) hi]
  have hp : (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^(-s) *
      (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^(1-s) =
      (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^(1-2*s) := by
    rw [← Complex.cpow_add _ _ hA]
    congr 1
    ring
  calc
    _ = W * (((mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^(-s) *
        (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^(1-s)) *
          mixedGammaFactor K (1-s) * mixedInverseGammaFactor K s *
            ψ.inverse.primitiveContinued hM
              (ψ.inverse_isPrimitive hM hprim) (1-s)) := by ring
    _ = _ := by rw [hp]

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic

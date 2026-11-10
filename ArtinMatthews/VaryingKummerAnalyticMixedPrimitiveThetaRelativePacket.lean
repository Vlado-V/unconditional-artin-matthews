module

public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveThetaCosets
public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveThetaDualComparison
public import ArtinMatthews.VaryingKummerAnalyticRayIdealInverse
public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveThetaDualRayCoefficients
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! The dual coefficient comparison on literal relative ideals. This removes
the auxiliary principal-product premise from the class-packet comparison. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)

def mixedPrimitiveDualRelativeIdeal
    (β : (mixedPrimitiveDualFractionalIdeal K I M).val) (hβ : (β : K) ≠ 0) :
    integralFractionalIdeals K :=
  ⟨relativeElementIdeal (mixedTraceDualIdeal K (mixedConductorIdeal K I M hI hM))
    (Units.mk0 (β : K) hβ),
    (relativeElementIdeal_le_one_iff _ _).mpr β.property⟩

theorem mixedPrimitiveDualIntegral_principal_product
    (β : (mixedPrimitiveDualFractionalIdeal K I M).val) (hβ : (β : K) ≠ 0) :
    Ideal.span {(mixedPrimitiveDualIntegralEquiv K I M β : 𝓞 K)} =
      mixedPrimitiveDualIntegralIdeal K I M *
        EvenRayCharacter.underlyingIdeal (mixedPrimitiveDualRelativeIdeal K I M hI hM β hβ) := by
  apply FractionalIdeal.coeIdeal_injective (K := K)
  change (Ideal.span {(mixedPrimitiveDualIntegralEquiv K I M β : 𝓞 K)} :
      FractionalIdeal (𝓞 K)⁰ K) =
    ((mixedPrimitiveDualIntegralIdeal K I M *
      EvenRayCharacter.underlyingIdeal (mixedPrimitiveDualRelativeIdeal K I M hI hM β hβ) :
        Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
  rw [FractionalIdeal.coeIdeal_span_singleton,FractionalIdeal.coeIdeal_mul]
  have he : algebraMap (𝓞 K) K (mixedPrimitiveDualIntegralEquiv K I M β : 𝓞 K) =
      (((mixedPrimitiveDualFractionalIdeal K I M).den : 𝓞 K) : K) * (β : K) :=
    mixedPrimitiveDualIntegralEquiv_coe K I M β
  rw [he,EvenRayCharacter.underlyingIdeal_coe]
  rw [show (mixedPrimitiveDualIntegralIdeal K I M : FractionalIdeal (𝓞 K)⁰ K) =
    spanSingleton (𝓞 K)⁰ (((mixedPrimitiveDualFractionalIdeal K I M).den : 𝓞 K) : K) *
      mixedPrimitiveDualFractionalIdeal K I M from
        (mixedPrimitiveDualFractionalIdeal K I M).den_mul_self_eq_num'.symm]
  change spanSingleton (𝓞 K)⁰ (_ * (β : K)) =
    (spanSingleton (𝓞 K)⁰ _ * (mixedTraceDualIdeal K (mixedConductorIdeal K I M hI hM)).val) *
      (relativeElementIdeal (mixedTraceDualIdeal K (mixedConductorIdeal K I M hI hM))
        (Units.mk0 (β : K) hβ)).val
  rw [← spanSingleton_mul_spanSingleton]
  simp only [relativeElementIdeal,Units.val_mul,coe_toPrincipalIdeal,Units.val_mk0]
  rw [mul_mul_mul_comm,Units.mul_inv,mul_one]

/-- A single actual inverse-character coefficient formula for every nonzero
dual lattice element, with no supplied principal-product equality. -/
theorem mixedPrimitiveDualRay_relativeCoefficient_exists_scalar
    (ψ : EvenIdealRayCharacter K M) :
    ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ (β : (mixedPrimitiveDualFractionalIdeal K I M).val)
      (hβ : (β : K) ≠ 0),
      ψ.inverse.coefficient (mixedPrimitiveDualRelativeIdeal K I M hI hM β hβ) =
        κ * ψ.residue⁻¹ (idealModuleDualResidue K I M hI hM β β.property) := by
  obtain ⟨κ,hκ,H⟩ := mixedPrimitiveDualRay_coefficient_exists_scalar K I M hI hM ψ
  refine ⟨κ,hκ,fun β hβ => ?_⟩
  have H' := H (EvenRayCharacter.underlyingIdeal (mixedPrimitiveDualRelativeIdeal K I M hI hM β hβ))
    (EvenRayCharacter.underlyingIdeal_ne_bot _) β hβ
    (mixedPrimitiveDualIntegral_principal_product K I M hI hM β hβ)
  rw [EvenRayCharacter.underlyingIdeal_unit] at H'
  exact H'

end
end ArtinMatthews.VaryingKummerAnalytic

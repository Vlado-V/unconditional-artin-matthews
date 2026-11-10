module

public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveRayPoisson
public import ArtinMatthews.VaryingKummerAnalyticMixedDualShift
public import ArtinMatthews.VaryingKummerAnalyticMixedUnitAverageSymmetry
public import ArtinMatthews.VaryingKummerAnalyticUnitUnfolding
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

/-! Genuine unit periodicity and reflection of the ray-weighted ideal theta.
The factor two at complex places becomes its exact radial scale, not an
assumed symmetry of a chosen fundamental parallelotope. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal MeasureTheory
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def idealElementUnitEquiv (F : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (z : (𝓞 K)ˣ) :
    nonzeroIdealElements F ≃ nonzeroIdealElements F where
  toFun := idealElementUnitAction F z
  invFun := idealElementUnitAction F z⁻¹
  left_inv a := by
    apply Subtype.ext
    simp only [idealElementUnitAction,map_inv,inv_mul_cancel_left]
  right_inv a := by
    apply Subtype.ext
    simp only [idealElementUnitAction,map_inv,mul_inv_cancel_left]

theorem mixedComplexArchGaussian_unit_translate (a : K) (z : (𝓞 K)ˣ) (t : ℝ)
    (u : logSpace K) :
    mixedComplexArchGaussian K ((z : K)*a) t u =
      mixedComplexArchGaussian K a t (logEmbedding K (Additive.ofMul z)+u) := by
  unfold mixedComplexArchGaussian mixedArchEnergy
  simp only [map_mul,mixedPlaceWeight_add,mixedPlaceWeight_unit]
  congr 4
  apply Finset.sum_congr rfl
  intro w _
  ring

variable {M : Ideal (𝓞 K)}

def mixedRayClassTheta (ψ : EvenIdealRayCharacter K M)
    (F : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (u : logSpace K) (t : ℝ) : ℂ :=
  ∑' a : nonzeroIdealElements F,
    ψ.coefficient ⟨relativeElementIdeal F a.val,(relativeElementIdeal_le_one_iff _ _).mpr a.property⟩ *
      mixedComplexArchGaussian K (a.val : K) t u

theorem mixedRayClassTheta_unit_periodic (ψ : EvenIdealRayCharacter K M)
    (F : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (z : (𝓞 K)ˣ) (u : logSpace K) (t : ℝ) :
    mixedRayClassTheta K ψ F (logEmbedding K (Additive.ofMul z)+u) t =
      mixedRayClassTheta K ψ F u t := by
  unfold mixedRayClassTheta
  conv_rhs => rw [← (idealElementUnitEquiv K F z).tsum_eq]
  apply tsum_congr
  intro a
  have hw : (⟨relativeElementIdeal F (idealElementUnitAction F z a).val,
      (relativeElementIdeal_le_one_iff _ _).mpr (idealElementUnitAction F z a).property⟩ :
        integralFractionalIdeals K) =
      ⟨relativeElementIdeal F a.val,(relativeElementIdeal_le_one_iff _ _).mpr a.property⟩ := by
    apply Subtype.ext
    exact congrArg (fun J : integralIdealClassFiber F => J.val)
      (relativeElementClassMap_unitAction F z a)
  change _ = ψ.coefficient
    (⟨relativeElementIdeal F (idealElementUnitAction F z a).val,
      (relativeElementIdeal_le_one_iff _ _).mpr (idealElementUnitAction F z a).property⟩ :
        integralFractionalIdeals K) *
    mixedComplexArchGaussian K ((idealElementUnitAction F z a).val : K) t u
  rw [hw]
  congr 1
  exact (mixedComplexArchGaussian_unit_translate K (a.val : K) z t u).symm

theorem mixedRayClassTheta_reflection (ψ : EvenIdealRayCharacter K M)
    (F : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (c : logSpace K) (t : ℝ) :
    (∫ u in mixedUnitLogDomain K, mixedRayClassTheta K ψ F (c-u) t) =
      ∫ u in mixedUnitLogDomain K, mixedRayClassTheta K ψ F u t := by
  refine mixedUnitLogDomain_integral_reflection K
    (fun u => mixedRayClassTheta K ψ F u t) ?_ c
  intro g u
  obtain ⟨z,hz⟩ := mixedUnitLogOnto_surjective K g
  have hg : logEmbedding K z = (g : logSpace K) := congrArg Subtype.val hz
  rw [← hg]
  exact mixedRayClassTheta_unit_periodic K ψ F z.toMul u t

variable (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)

theorem mixedPrimitiveRayDualTheta_rescale (ψ : EvenIdealRayCharacter K M)
    (u : logSpace K) (t : ℝ) :
    mixedPrimitiveRayDualTheta K I M hI hM ψ (-u) t =
      mixedRayClassTheta K ψ.inverse (mixedTraceDualIdeal K (mixedConductorIdeal K I M hI hM))
        (mixedDualLogShift K-u) ((mixedDualRadialScale K)^2*t) := by
  unfold mixedPrimitiveRayDualTheta mixedRayClassTheta
  apply tsum_congr
  intro a
  congr 1
  simp_rw [mixedDualGaussian_weight]
  have H : (∑ w : InfinitePlace K,
      (mixedDualRadialScale K * mixedPlaceWeight K (mixedDualLogShift K-u) w * w (a.val : K))^2) =
      (mixedDualRadialScale K)^2 * ∑ w : InfinitePlace K,
        (mixedPlaceWeight K (mixedDualLogShift K-u) w * w (a.val : K))^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    ring
  rw [H]
  unfold mixedComplexArchGaussian mixedArchEnergy
  congr 1
  push_cast
  ring

/-- Exact unit-average reflection of the inverse ray-character theta,
retaining the signature-dependent radial dilation. -/
theorem mixedPrimitiveRayDualTheta_average (ψ : EvenIdealRayCharacter K M) (t : ℝ) :
    (∫ u in mixedUnitLogDomain K, mixedPrimitiveRayDualTheta K I M hI hM ψ (-u) t) =
      ∫ u in mixedUnitLogDomain K,
        mixedRayClassTheta K ψ.inverse (mixedTraceDualIdeal K (mixedConductorIdeal K I M hI hM))
          u ((mixedDualRadialScale K)^2*t) := by
  simp_rw [mixedPrimitiveRayDualTheta_rescale]
  exact mixedRayClassTheta_reflection K ψ.inverse _ _ _

end
end ArtinMatthews.VaryingKummerAnalytic

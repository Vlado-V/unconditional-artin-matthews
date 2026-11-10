module

public import ArtinMatthews.VaryingKummerAnalyticIdealModuleFrequencyBalanced
public import ArtinMatthews.VaryingKummerAnalyticMixedPartialDedekind
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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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

/-! Literal finite-support geometry of the chosen balanced ideal elements.
The fixed-I coordinate map is injective and has a proved squared-radius bound. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def idealModuleBalancedElement (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (J : integralIdealClassFiber (integralIdealFractionalUnit I hI)) : I :=
  idealModuleIntegerElement K I hI (idealModuleBalancedRepresentative K I hI J)

theorem idealModuleBalancedElement_coe (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (J : integralIdealClassFiber (integralIdealFractionalUnit I hI)) :
    ((idealModuleBalancedElement K I hI J).val : K) =
      ((idealModuleBalancedRepresentative K I hI J).val : K) :=
  idealModuleIntegerElement_coe K I hI _

theorem idealModuleBalancedElement_ne_zero (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (J : integralIdealClassFiber (integralIdealFractionalUnit I hI)) :
    (idealModuleBalancedElement K I hI J).val ≠ 0 := by
  intro h
  have he := idealModuleBalancedElement_coe K I hI J
  rw [h] at he
  change (0 : K) = ((idealModuleBalancedRepresentative K I hI J).val : K) at he
  exact (idealModuleBalancedRepresentative K I hI J).val.ne_zero he.symm

theorem idealModuleBalancedElement_injective (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    Function.Injective (idealModuleBalancedElement K I hI) := by
  intro J J' h
  apply idealModuleBalancedIntegerCoordinates_injective K I hI
  exact congrArg (idealModuleIntegerCoordinates K I hI) h

theorem idealModuleBalancedElement_coordinates (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (J : integralIdealClassFiber (integralIdealFractionalUnit I hI)) :
    idealModuleIntegerCoordinates K I hI (idealModuleBalancedElement K I hI J) =
      idealModuleBalancedIntegerCoordinates K I hI J := rfl

/-- Its constants depend only on the field and the fixed ideal. -/
def idealModuleBalancedSupportRadius (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (X : ℝ) : ℝ :=
  Real.sqrt (Module.finrank ℚ K : ℝ) * idealModuleBalancedCoordinateConstant K I hI *
    X ^ (1 / (Module.finrank ℚ K : ℝ))

theorem idealModuleBalancedSupportRadius_pos (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    {X : ℝ} (hX : 0 < X) : 0 < idealModuleBalancedSupportRadius K I hI X := by
  have hn : 0 < (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)
  exact mul_pos (mul_pos (Real.sqrt_pos.mpr hn) (idealModuleBalancedCoordinateConstant_pos K I hI))
    (Real.rpow_pos_of_pos hX _)

theorem idealModuleBalancedElement_squared_support (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (J : integralIdealClassFiber (integralIdealFractionalUnit I hI)) {X : ℝ}
    (hJ : (FractionalIdeal.absNorm J.val.val : ℝ) ≤ X) :
    (∑ j, (idealModuleIntegerCoordinates K I hI (idealModuleBalancedElement K I hI J) j : ℝ)^2) ≤
      (idealModuleBalancedSupportRadius K I hI X)^2 := by
  have hC := idealModuleBalancedCoordinateConstant_pos K I hI
  have hN : 0 ≤ (FractionalIdeal.absNorm J.val.val : ℝ) := (fractionalIdeal_absNorm_pos J.val).le
  have hX : 0 ≤ X := hN.trans hJ
  have hnorm := (idealModuleBalancedIntegerCoordinates_norm_le K I hI J).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hN hJ (one_div_nonneg.mpr (Nat.cast_nonneg (Module.finrank ℚ K)))) hC.le)
  have hsq : ∀ j : IdealModuleFrequencyIndex K I hI,
      (idealModuleBalancedIntegerCoordinates K I hI J j : ℝ)^2 ≤
        (idealModuleBalancedCoordinateConstant K I hI * X ^ (1 / (Module.finrank ℚ K : ℝ)))^2 := by
    intro j
    have hj := (norm_le_pi_norm
      (fun j => (idealModuleBalancedIntegerCoordinates K I hI J j : ℝ)) j).trans hnorm
    simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hj 2
  rw [idealModuleBalancedElement_coordinates]
  calc
    _ ≤ ∑ _j : IdealModuleFrequencyIndex K I hI,
        (idealModuleBalancedCoordinateConstant K I hI * X ^ (1 / (Module.finrank ℚ K : ℝ)))^2 :=
      Finset.sum_le_sum fun j _ => hsq j
    _ = (Module.finrank ℚ K : ℝ) *
        (idealModuleBalancedCoordinateConstant K I hI * X ^ (1 / (Module.finrank ℚ K : ℝ)))^2 := by
      simp only [Finset.sum_const, Finset.card_univ, idealModuleFrequencyIndex_card, nsmul_eq_mul]
    _ = _ := by
      unfold idealModuleBalancedSupportRadius
      simp only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg (Module.finrank ℚ K))]
      ring

end
end ArtinMatthews.VaryingKummerAnalytic

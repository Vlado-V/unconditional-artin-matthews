module

public import ArtinMatthews.VaryingKummerAnalyticIdealModuleConductorSieve
public import ArtinMatthews.VaryingKummerAnalyticIdealModuleSieveScale
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! The actual fixed-ideal conductor sieve with its X + U² scale.
No additive-sieve, support, or coefficient-transport premise is assumed. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal OAI.SevenEighths.FiniteFourier
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def idealModuleBalancedSieveConstant (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) : ℝ :=
  idealModuleSieveScaleConstant K I hI
    (Real.sqrt (Module.finrank ℚ K : ℝ) * idealModuleBalancedCoordinateConstant K I hI)

theorem idealModuleBalancedSieveConstant_pos (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    0 < idealModuleBalancedSieveConstant K I hI :=
  idealModuleSieveScaleConstant_pos K I hI
    (mul_nonneg (Real.sqrt_nonneg _) (idealModuleBalancedCoordinateConstant_pos K I hI).le)

theorem idealModuleConductorSieveBound_le (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    {U X : ℝ} (hU : 1 ≤ U) (hX : 1 ≤ X) :
    idealModuleConductorSieveBound K I hI U X ≤
      idealModuleBalancedSieveConstant K I hI * (X + U^2) := by
  simpa only [idealModuleConductorSieveBound,idealModuleBalancedSieveConstant,
    idealModuleBalancedSupportRadius,one_div] using
    idealModuleSieveScale_bound K I hI
      (mul_nonneg (Real.sqrt_nonneg _) (idealModuleBalancedCoordinateConstant_pos K I hI).le)
      hX hU

theorem idealModule_weighted_conductor_sieve_norm_scale (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    {U X : ℝ} (hU : 1 ≤ U) (hX : 1 ≤ X) (T : Finset (IdealConductorModulus K))
    (hT : ∀ M ∈ T, (Ideal.absNorm M.val : ℝ) ≤ U)
    (S : ∀ M : IdealConductorModulus K, Finset (MulChar ((𝓞 K) ⧸ M.val) ℂ))
    (hS : ∀ M ∈ T, ∀ χ ∈ S M, IsPrimitiveOnIdeals χ)
    (B : Finset (integralIdealClassFiber (integralIdealFractionalUnit I hI)))
    (hB : ∀ J ∈ B, (FractionalIdeal.absNorm J.val.val : ℝ) ≤ X)
    (v : integralIdealClassFiber (integralIdealFractionalUnit I hI) → ℂ) :
    (∑ M ∈ T, idealModuleConductorWeight K M *
      ∑ χ ∈ S M, ‖∑ J ∈ B, v J * χ
        (idealResidueCoordinate I M.val hI M.property (idealModuleBalancedElement K I hI J))‖^2) ≤
      (idealModuleBalancedSieveConstant K I hI * (X+U^2)) * ∑ J ∈ B, ‖v J‖^2 := by
  apply (idealModule_weighted_conductor_sieve K I hI (lt_of_lt_of_le zero_lt_one hU)
    (lt_of_lt_of_le zero_lt_one hX) T hT S hS B hB v).trans
  exact mul_le_mul_of_nonneg_right (idealModuleConductorSieveBound_le K I hI hU hX)
    (Finset.sum_nonneg fun J _ => sq_nonneg _)

theorem idealModule_unweighted_conductor_sieve_norm_scale (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    {U X : ℝ} (hU : 1 ≤ U) (hX : 1 ≤ X) (T : Finset (IdealConductorModulus K))
    (hT : ∀ M ∈ T, (Ideal.absNorm M.val : ℝ) ≤ U)
    (S : ∀ M : IdealConductorModulus K, Finset (MulChar ((𝓞 K) ⧸ M.val) ℂ))
    (hS : ∀ M ∈ T, ∀ χ ∈ S M, IsPrimitiveOnIdeals χ)
    (B : Finset (integralIdealClassFiber (integralIdealFractionalUnit I hI)))
    (hB : ∀ J ∈ B, (FractionalIdeal.absNorm J.val.val : ℝ) ≤ X)
    (v : integralIdealClassFiber (integralIdealFractionalUnit I hI) → ℂ) :
    (∑ M ∈ T, ∑ χ ∈ S M, ‖∑ J ∈ B, v J * χ
      (idealResidueCoordinate I M.val hI M.property (idealModuleBalancedElement K I hI J))‖^2) ≤
      (idealModuleBalancedSieveConstant K I hI * (X+U^2)) * ∑ J ∈ B, ‖v J‖^2 := by
  apply (idealModule_unweighted_conductor_sieve K I hI (lt_of_lt_of_le zero_lt_one hU)
    (lt_of_lt_of_le zero_lt_one hX) T hT S hS B hB v).trans
  exact mul_le_mul_of_nonneg_right (idealModuleConductorSieveBound_le K I hI hU hX)
    (Finset.sum_nonneg fun J _ => sq_nonneg _)

end
end ArtinMatthews.VaryingKummerAnalytic

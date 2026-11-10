module

public import ArtinMatthews.QuadraticHeckeFieldNormalization
public import ArtinMatthews.VaryingKummerAnalyticRayIdealInverseNonprincipal
public import ArtinMatthews.VaryingKummerAnalyticRayIdealPrimitiveContinuation
public import ArtinMatthews.VaryingKummerAnalyticMixedFunctionalNormalization
public import ArtinMatthews.VaryingKummerAnalyticPrimitiveUncompletedFunctionalEquation
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

namespace ArtinMatthews
open NumberField VaryingKummerAnalytic OAI.SevenEighths.FiniteFourier
open scoped NumberField Classical nonZeroDivisors
noncomputable section

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
local notation "r" => InfinitePlace.nrComplexPlaces K

private theorem sqrt_cpow_recenter {Q : ℝ} (hQ : 0 < Q) (s : ℂ) :
    (Real.sqrt Q : ℂ) ^ (2 * s - 1) = (Q : ℂ) ^ (s - 1 / 2) := by
  rw [positiveReal_cpow_eq_exp (Real.sqrt_pos.mpr hQ), positiveReal_cpow_eq_exp hQ,
    Real.log_sqrt hQ.le]
  push_cast
  congr 1
  ring

/-- The actual primitive Hecke functional equation in the source quadratic
Mellin normalization. The root number remains the actual functional-equation phase. -/
theorem quadraticHeckePrimitiveReflection {M : Ideal (𝓞 K)}
    (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
    (hprim : IsPrimitiveOnIdeals ψ.residue) (hnp : ψ.IsNonprincipal) :
    ∃ W : ℂ, ‖W‖ = 1 ∧ ∀ s : ℂ, 0 < s.re →
      ψ.primitiveContinued hM hprim (1 - s) =
        W * (Ideal.absNorm M : ℂ) ^ (s - 1 / 2) *
          quadraticHeckeDualGamma (quadraticHeckeFieldScale K) r s *
            ψ.inverse.primitiveContinued hM (ψ.inverse_isPrimitive hM hprim) s := by
  obtain ⟨W, hW, hfe⟩ := ψ.primitiveContinued_left_functionalEquation hM hprim hnp
  refine ⟨W, hW, fun s hs => ?_⟩
  have hlt : (1 - s).re < 1 := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have h := hfe (1 - s) hlt
  have hz : (1 : ℂ) - (1 - s) = s := by ring
  have hp : (1 : ℂ) - 2 * (1 - s) = 2 * s - 1 := by ring
  rw [hz, hp] at h
  have hNorm :
      (FractionalIdeal.absNorm (integralIdealFractionalUnit M hM).val : ℝ) =
        (Ideal.absNorm M : ℝ) := by
    simp only [integralIdealFractionalUnit, Units.val_mk0,
      FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast]
  have hQ : 0 < (Ideal.absNorm M : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hM))
  rw [mixedConductorScale, hNorm, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg
    (mixedDiscriminantScale_pos K).le (Real.sqrt_nonneg _), sqrt_cpow_recenter hQ] at h
  rw [h, quadraticHeckeDualGamma_eq_mixed K]
  push_cast
  ring

end
end ArtinMatthews

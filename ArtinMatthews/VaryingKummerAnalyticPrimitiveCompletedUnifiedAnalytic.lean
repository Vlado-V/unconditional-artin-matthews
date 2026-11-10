module

public import ArtinMatthews.VaryingKummerAnalyticPrimitiveCompletedUnified
public import ArtinMatthews.VaryingKummerAnalyticGrowth
public import ArtinMatthews.VaryingKummerAnalyticMixedConductorOneConjugation
public import ArtinMatthews.VaryingKummerAnalyticMixedConductorOneGrowth
public import ArtinMatthews.VaryingKummerAnalyticMixedGammaAnalytic
public import ArtinMatthews.VaryingKummerAnalyticPrimitiveCompletionGrowth
public import ArtinMatthews.VaryingKummerAnalyticPrimitiveCompletionZeros
public import ArtinMatthews.VaryingKummerAnalyticRayIdealEuler
public import ArtinMatthews.VaryingKummerAnalyticRayIdealInverseNonprincipal
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Analytic facts for the genuine unified primitive completion. The
normalization is shared by inverse characters, and all assertions follow from
the actual branch completions or their genuine completed functional equation. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Set ArtinMatthews.ReusedGrowth
open scoped NumberField nonZeroDivisors Classical ComplexConjugate
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)

theorem primitiveCompletedUnified_hasSubquadraticGrowth
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue) :
    HasSubquadraticGrowth (ψ.primitiveCompletedUnified hM) := by
  by_cases hMtop : M = ⊤
  · rw [ψ.primitiveCompletedUnified_of_top hM hMtop]
    exact (hasSubquadraticGrowth_const _).mul
      (ψ.conductorOneCompleted_hasSubquadraticGrowth hMtop)
  · rw [ψ.primitiveCompletedUnified_of_ne_top hM hMtop]
    exact ψ.properCompleted_hasSubquadraticGrowth hM hMtop hprim

variable (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
variable (hnp : ψ.IsNonprincipal)
include hprim hnp

theorem primitiveCompletedUnified_zero_iff_primitive {s : ℂ} (hs : 0 < s.re) :
    ψ.primitiveCompletedUnified hM s = 0 ↔ ψ.primitiveContinued hM hprim s = 0 := by
  rw [ψ.primitiveCompletedUnified_eq_gamma_primitive hM hprim hnp hs]
  have hA : (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr
      (mixedConductorScale_pos K (integralIdealFractionalUnit M hM)).ne'))
  simp only [mul_eq_zero,hA,mixedGammaFactor_ne_zero K hs,false_or]

theorem primitiveCompletedUnified_ne_zero_right {s : ℂ} (hs : 1 < s.re) :
    ψ.primitiveCompletedUnified hM s ≠ 0 := by
  rw [ψ.primitiveCompletedUnified_eq_gamma_primitive hM hprim hnp (zero_lt_one.trans hs),
    ψ.primitiveContinued_eq_dirichlet hM hprim hnp hs]
  exact mul_ne_zero (mul_ne_zero
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr
      (mixedConductorScale_pos K (integralIdealFractionalUnit M hM)).ne')))
    (mixedGammaFactor_ne_zero K (zero_lt_one.trans hs))) (ψ.dirichlet_ne_zero hs)

theorem primitiveCompletedUnified_ne_zero : ψ.primitiveCompletedUnified hM ≠ 0 := by
  intro h
  exact ψ.primitiveCompletedUnified_ne_zero_right hM hprim hnp (s := 2) (by norm_num)
    (congrFun h 2)

theorem primitiveCompletedUnified_zero_strip {s : ℂ}
    (hs : ψ.primitiveCompletedUnified hM s = 0) : 0 ≤ s.re ∧ s.re ≤ 1 := by
  constructor
  · by_contra h
    have hr : 1 < (1-s).re := by simp only [Complex.sub_re,Complex.one_re]; linarith
    obtain ⟨W,hW,HW⟩ := ψ.primitiveCompletedUnified_functionalEquation hM hprim hnp
    have hW0 : W ≠ 0 := fun h => by simp [h] at hW
    exact (mul_ne_zero hW0 (ψ.inverse.primitiveCompletedUnified_ne_zero_right hM
      (ψ.inverse_isPrimitive hM hprim) (ψ.inverse_isNonprincipal hnp) hr))
      ((HW s).symm.trans hs)
  · by_contra h
    exact ψ.primitiveCompletedUnified_ne_zero_right hM hprim hnp (lt_of_not_ge h) hs

theorem primitiveCompletedUnified_inverse_conj (s : ℂ) :
    ψ.inverse.primitiveCompletedUnified hM (conj s) =
      conj (ψ.primitiveCompletedUnified hM s) := by
  by_cases hMtop : M = ⊤
  · rw [ψ.inverse.primitiveCompletedUnified_of_top hM hMtop,
      ψ.primitiveCompletedUnified_of_top hM hMtop]
    dsimp only
    rw [map_mul,map_inv₀,Complex.conj_ofReal,
      ψ.conductorOneCompleted_inverse_conj hMtop hM hprim hnp]
  · rw [ψ.inverse.primitiveCompletedUnified_of_ne_top hM hMtop,
      ψ.primitiveCompletedUnified_of_ne_top hM hMtop]
    exact ψ.properCompleted_inverse_conj hM hMtop hprim s

theorem primitiveCompletedUnified_inverse_zero_iff (s : ℂ) :
    ψ.inverse.primitiveCompletedUnified hM (conj s) = 0 ↔
      ψ.primitiveCompletedUnified hM s = 0 := by
  rw [ψ.primitiveCompletedUnified_inverse_conj hM hprim hnp]
  exact map_eq_zero_iff _ (starRingEnd ℂ).injective

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic

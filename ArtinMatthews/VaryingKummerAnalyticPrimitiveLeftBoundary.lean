module

public import ArtinMatthews.VaryingKummerAnalyticMixedGammaRatioGlobal
public import ArtinMatthews.VaryingKummerAnalyticPrimitiveReciprocal
public import ArtinMatthews.VaryingKummerAnalyticMixedConductorNormalization
public import ArtinMatthews.VaryingKummerAnalyticRayIdealInverseNonprincipal
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine conductor-uniform polynomial growth on Re(s)=-1/4.
The exact conductor factor comes from the proved inverse-character
functional equation, the Gamma ratio from its actual logarithmic derivative,
and the right-hand L bound from the actual ideal Euler logarithm. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex
open scoped NumberField nonZeroDivisors Classical
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M)

theorem dirichlet_norm_le_primitiveReciprocalBound {s : ℂ} (hs : 5/4 ≤ s.re) :
    ‖ψ.dirichlet s‖ ≤ primitiveReciprocalBound K := by
  rw [← ψ.exp_eulerLog_eq_dirichlet (show 1 < s.re by linarith),Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  exact (Complex.re_le_norm _).trans (ψ.eulerLog_norm_le hs)

theorem primitiveContinued_norm_le_right (hM : M ≠ ⊥)
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
    (hnp : ψ.IsNonprincipal) {s : ℂ} (hs : 5/4 ≤ s.re) :
    ‖ψ.primitiveContinued hM hprim s‖ ≤ primitiveReciprocalBound K := by
  rw [ψ.primitiveContinued_eq_dirichlet hM hprim hnp (by linarith : 1 < s.re)]
  exact ψ.dirichlet_norm_le_primitiveReciprocalBound hs

theorem primitiveContinued_left_line_norm (hM : M ≠ ⊥)
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
    (hnp : ψ.IsNonprincipal) (t : ℝ) :
    ‖ψ.primitiveContinued hM hprim ((-1/4 : ℂ)+(t : ℂ)*I)‖ =
      (mixedConductorScale K (integralIdealFractionalUnit M hM))^(3/2 : ℝ) *
        ‖mixedGammaLeftRatio K t‖ *
          ‖ψ.inverse.primitiveContinued hM (ψ.inverse_isPrimitive hM hprim)
            ((5/4 : ℂ)-(t : ℂ)*I)‖ := by
  obtain ⟨W,hW,hfe⟩ := ψ.primitiveContinued_left_functionalEquation hM hprim hnp
  have hA := mixedConductorScale_pos K (integralIdealFractionalUnit M hM)
  have ha : 1-((-1/4 : ℂ)+(t : ℂ)*I) = (5/4 : ℂ)-(t : ℂ)*I := by ring
  have hr : (1-2*((-1/4 : ℂ)+(t : ℂ)*I)).re = (3/2 : ℝ) := by norm_num
  rw [hfe _ (by norm_num),ha]
  simp only [norm_mul,hW,one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hA,mixedGammaLeftRatio,hr]
  ring

end EvenIdealRayCharacter

theorem exists_primitiveContinued_left_boundary_bound
    (K : Type*) [Field K] [NumberField K] :
    ∃ (C : ℝ) (m : ℕ), 0 < C ∧
      ∀ {M : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
        (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
        (_hnp : ψ.IsNonprincipal) (t : ℝ),
        ‖ψ.primitiveContinued hM hprim ((-1/4 : ℂ)+(t : ℂ)*I)‖ ≤
          C * (mixedConductorScale K (integralIdealFractionalUnit M hM))^(3/2 : ℝ) *
            (|t|+2)^m := by
  obtain ⟨C,m,hC,hbound⟩ := exists_mixedGammaLeftRatio_polynomial_bound K
  refine ⟨C*primitiveReciprocalBound K,m,mul_pos hC (primitiveReciprocalBound_pos K),?_⟩
  intro M ψ hM hprim hnp t
  rw [ψ.primitiveContinued_left_line_norm hM hprim hnp]
  have hright := ψ.inverse.primitiveContinued_norm_le_right hM (ψ.inverse_isPrimitive hM hprim)
    (ψ.inverse_isNonprincipal hnp) (s := (5/4 : ℂ)-(t : ℂ)*I) (by norm_num)
  have H := mul_le_mul (hbound t) hright (norm_nonneg _)
    (mul_nonneg hC.le (by positivity : 0 ≤ (|t|+2)^m))
  have HA := mul_le_mul_of_nonneg_left H
    (Real.rpow_nonneg (mixedConductorScale_pos K (integralIdealFractionalUnit M hM)).le (3/2 : ℝ))
  convert HA using 1 <;> ring

end
end ArtinMatthews.VaryingKummerAnalytic

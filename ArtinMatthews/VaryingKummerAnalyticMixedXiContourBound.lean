module

public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindCompletion
public import ArtinMatthews.VaryingKummerAnalyticLogDerivDifference
public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindFunctionalEquation
public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindGrowth
public import ArtinMatthews.VaryingKummerAnalyticMixedXiBoundary
public import ArtinMatthews.VaryingKummerAnalyticMixedXiNormBound
public import ArtinMatthews.VaryingKummerAnalyticMixedXiZeroStrip
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Full complex logarithmic-derivative bounds in the horizontal contour
strip, obtained from actual separation from the zeros. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex Set
open OAI.PrimeDegreePackets.AnalyticGrowth
noncomputable section
universe u

theorem mixedCompletedDedekindXi_horizontal_norm_le
    (K : Type u) [Field K] [NumberField K] {t σ δ : ℝ}
    (hσ : -(1/2 : ℝ) ≤ σ) (hσ' : σ ≤ 2) (hδ : 0 < δ)
    (havoid : ∀ ρ : ℂ, mixedCompletedDedekindXi K ρ = 0 → δ ≤ |t-ρ.im|) :
    ‖logDeriv (mixedCompletedDedekindXi K) (⟨σ,t⟩ : ℂ)‖ ≤
      (4+9/δ)*‖logDeriv (mixedCompletedDedekindXi K) (⟨2,t⟩ : ℂ)‖ := by
  let b : ℂ := ⟨2,t⟩
  let s : ℂ := ⟨σ,t⟩
  have hd : ‖b-s‖ ≤ 3 := by
    have heq : b-s = ((2-σ : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [b,s]
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hdiff := norm_logDeriv_sub_le_of_zero_distance
    (mixedCompletedDedekindXi_entire K) (mixedCompletedDedekindXi_zero_ne_zero K)
    (mixedCompletedDedekindXi_hasSubquadraticGrowth K)
    (fun z => (mixedCompletedDedekindXi_functional_equation K z).symm)
    (fun ρ hρ => (mixedCompletedDedekindXi_zeros_in_strip K ρ hρ).2)
    (b := b) (s := s) rfl hδ
    (fun ρ hρ => (havoid ρ hρ).trans (by simpa [s] using Complex.abs_im_le_norm (s-ρ)))
  have hfactor : ‖b-s‖*(1+‖b-s‖/δ) ≤ 3+9/δ := by
    have hd0 := norm_nonneg (b-s)
    have hi : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
    simp only [div_eq_mul_inv]
    nlinarith [mul_nonneg (by nlinarith : 0 ≤ 9-‖b-s‖^2) hi]
  have hre := Complex.re_le_norm (logDeriv (mixedCompletedDedekindXi K) b)
  have hfactor0 : 0 ≤ ‖b-s‖*(1+‖b-s‖/δ) := by positivity
  calc
    _ ≤ ‖logDeriv (mixedCompletedDedekindXi K) s - logDeriv (mixedCompletedDedekindXi K) b‖ +
        ‖logDeriv (mixedCompletedDedekindXi K) b‖ := norm_le_norm_sub_add _ _
    _ ≤ (‖b-s‖*(1+‖b-s‖/δ))*‖logDeriv (mixedCompletedDedekindXi K) b‖ +
        ‖logDeriv (mixedCompletedDedekindXi K) b‖ := by
      have h := hdiff.trans (mul_le_mul_of_nonneg_left hre hfactor0)
      linarith
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_right hfactor
        (norm_nonneg (logDeriv (mixedCompletedDedekindXi K) b))
      change _ ≤ (4+9/δ)*‖logDeriv (mixedCompletedDedekindXi K) b‖
      nlinarith

theorem exists_mixedCompletedDedekindXi_horizontal_norm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type u) [Field K] [NumberField K], ∀ t σ δ : ℝ,
      -(1/2 : ℝ) ≤ σ → σ ≤ 2 → 0 < δ →
      (∀ ρ : ℂ, mixedCompletedDedekindXi K ρ = 0 → δ ≤ |t-ρ.im|) →
      ‖logDeriv (mixedCompletedDedekindXi K) (⟨σ,t⟩ : ℂ)‖ ≤
        C*(4+9/δ)*(Real.log |(discr K : ℝ)| +
          (Module.finrank ℚ K : ℝ)*Real.log (|t|+2)) := by
  obtain ⟨C,hC,hbase⟩ := exists_mixedCompletedDedekindXi_height_norm_bound.{u}
  refine ⟨C,hC,?_⟩
  intro K _ _ t σ δ hσ hσ' hδ havoid
  exact (mixedCompletedDedekindXi_horizontal_norm_le K hσ hσ' hδ havoid).trans
    (by simpa only [mul_assoc, mul_left_comm] using
      mul_le_mul_of_nonneg_left (hbase K t) (show 0 ≤ 4+9/δ by positivity))

end
end ArtinMatthews.VaryingKummerAnalytic

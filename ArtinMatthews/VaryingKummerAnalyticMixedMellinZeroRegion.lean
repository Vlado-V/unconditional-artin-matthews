module

public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindCompletion
public import OAI.NumberTheory.PrimePackets.AnalyticLogarithms
public import ArtinMatthews.VaryingKummerAnalyticMixedMellinZeroUniform
public import ArtinMatthews.VaryingKummerAnalyticMixedXiBoundary
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

/-! Quantitative dependence of the genuine Mellin zero sum on an explicit
zero-location theorem.  No fixed-width zero-free region is asserted here:
that arithmetic input remains a hypothesis visible in the theorem statement. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex MeasureTheory Set
open OAI.PrimeDegreePackets.AnalyticGrowth
open scoped ContDiff BigOperators
noncomputable section
universe u

theorem mixedCompletedDedekindXi_mellin_power_zero_region
    (f : ℝ → ℂ) (hcompact : HasCompactSupport f)
    (hpositive : tsupport f ⊆ Ioi 0) (hsmooth : ContDiff ℝ ∞ f) :
    ∃ C : ℝ,0 < C ∧ ∀ (K : Type u) [Field K] [NumberField K],
      ∀ (x β : ℝ),1 ≤ x →
      (∀ ρ : ℂ,mixedCompletedDedekindXi K ρ = 0 → ρ.re ≤ β) →
      (∑' ρ,‖(zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*
        mellin f ρ*(x : ℂ)^ρ‖) ≤
        C*x^β*(Real.log |(discr K : ℝ)|+(Module.finrank ℚ K : ℝ)) := by
  obtain ⟨C,hC,huniform⟩ := mixedCompletedDedekindXi_mellin_power_zero_uniform f hcompact hpositive hsmooth
  refine ⟨C,hC,?_⟩
  intro K _ _ x β hx hregion
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hun : Summable (fun ρ => (zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*mellin f ρ) := by
    simpa only [Complex.ofReal_one,one_cpow,mul_one] using (huniform K 1 zero_lt_one).1
  have hub : (∑' ρ,‖(zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*mellin f ρ‖) ≤
      C*(Real.log |(discr K : ℝ)|+(Module.finrank ℚ K : ℝ)) := by
    simpa only [Complex.ofReal_one,one_cpow,mul_one,max_self] using (huniform K 1 zero_lt_one).2
  have hs := (huniform K x hxpos).1.norm
  have hmajor := hun.norm.mul_left (x^β)
  have hpoint (ρ : ℂ) : ‖(zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*
      mellin f ρ*(x : ℂ)^ρ‖ ≤
      x^β*‖(zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*mellin f ρ‖ := by
    by_cases hm : zeroMultiplicity (mixedCompletedDedekindXi K) ρ = 0
    · simp [hm]
    have hρ := (zeroMultiplicity_ne_zero_iff (mixedCompletedDedekindXi_entire K)
      (mixedCompletedDedekindXi_zero_ne_zero K) ρ).mp hm
    rw [norm_mul,mul_comm (x^β)]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    exact Real.rpow_le_rpow_of_exponent_le hx (hregion ρ hρ)
  calc
    _ ≤ ∑' ρ,x^β*‖(zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*mellin f ρ‖ :=
      hs.tsum_le_tsum hpoint hmajor
    _ = x^β*(∑' ρ,‖(zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*mellin f ρ‖) := tsum_mul_left
    _ ≤ x^β*(C*(Real.log |(discr K : ℝ)|+(Module.finrank ℚ K : ℝ))) :=
      mul_le_mul_of_nonneg_left hub (Real.rpow_nonneg hxpos.le _)
    _ = _ := by ring

end
end ArtinMatthews.VaryingKummerAnalytic

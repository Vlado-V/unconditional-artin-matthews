module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import ArtinMatthews.SpectralCuspWeakRegularityLocal
public import ArtinMatthews.SpectralPositiveTestPrimitive
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Covering.Besicovitch
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


set_option backward.privateInPublic true
@[expose] public section

/-! Weak derivative zero on the positive half-line implies actual almost
everywhere constancy, also for complex-valued locally integrable functions.
The proof uses genuine compact primitives of zero-mean scalar tests. -/
namespace ArtinMatthews.SpectralCuspWeakRegularity
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff

theorem positive_weak_zero_ae_const {f : ℝ → ℂ}
    (hf : LocallyIntegrableOn f (Ioi (0 : ℝ)) volume)
    (hw : ∀ (ρ : ℝ → ℝ), ContDiff ℝ ∞ ρ → HasCompactSupport ρ →
      tsupport ρ ⊆ Ioi (0 : ℝ) → (∫ x, deriv ρ x • f x) = 0) :
    ∃ z : ℂ, f =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun _ => z := by
  let b : ContDiffBump (1 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  let η : ℝ → ℝ := b.normed volume
  have hη : ContDiff ℝ ∞ η := b.contDiff_normed
  have hηc : HasCompactSupport η := b.hasCompactSupport_normed
  have hηs : tsupport η ⊆ Ioi (0 : ℝ) := by
    intro x hx
    change x ∈ tsupport (b.normed volume) at hx
    rw [b.tsupport_normed_eq] at hx
    have H : |x - 1| ≤ 1 / 2 := by simpa only [Metric.mem_closedBall, Real.dist_eq, b] using hx
    have h := (abs_le.mp H).1
    change (0 : ℝ) < x
    linarith
  have hη1 : (∫ x, η x) = 1 := b.integral_normed
  have hηi : Integrable η volume := hη.continuous.integrable_of_hasCompactSupport hηc
  have hηf := integrable_positive_test_smul hf hη.continuous hηc hηs
  let z : ℂ := ∫ x, η x • f x
  have htest (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
      (hψs : tsupport ψ ⊆ Ioi (0 : ℝ)) : (∫ x, ψ x • (f x - z)) = 0 := by
    let r : ℝ := ∫ x, ψ x
    let σ : ℝ → ℝ := fun x => ψ x - r * η x
    have hσ : ContDiff ℝ ∞ σ := hψ.sub (contDiff_const.mul hη)
    have hσc : HasCompactSupport σ := hψc.sub (hηc.mul_left (f := fun _ => r))
    have hσs : tsupport σ ⊆ Ioi (0 : ℝ) :=
      (tsupport_sub _ _).trans (union_subset hψs (tsupport_mul_subset_right.trans hηs))
    have hψi : Integrable ψ volume := hψ.continuous.integrable_of_hasCompactSupport hψc
    have hmean : (∫ x, σ x) = 0 := by
      dsimp only [σ]
      rw [integral_sub hψi (hηi.const_mul r), integral_const_mul, hη1, mul_one, sub_self]
    obtain ⟨ρ, hρ, hρc, hρs, hderiv⟩ :=
      spectralPositiveTestPrimitive_exists σ hσ hσc hσs hmean
    have H := hw ρ hρ hρc hρs
    rw [hderiv] at H
    have hψf := integrable_positive_test_smul hf hψ.continuous hψc hψs
    change (∫ x, (ψ x - r * η x) • f x) = 0 at H
    simp_rw [sub_smul, mul_smul] at H
    have hrηf : Integrable (fun x => r • (η x • f x)) volume := hηf.smul r
    rw [integral_sub hψf hrηf, integral_smul] at H
    have hψz : Integrable (fun x => ψ x • z) volume := hψi.smul_const z
    simp_rw [smul_sub]
    rw [integral_sub hψf hψz, integral_smul_const]
    exact H
  have hlocal : LocallyIntegrableOn (fun x => f x - z) (Ioi (0 : ℝ)) volume :=
    hf.sub (locallyIntegrableOn_const z)
  have hz := isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero hlocal htest
  refine ⟨z, ?_⟩
  filter_upwards [ae_restrict_of_ae hz, ae_restrict_mem measurableSet_Ioi] with x hx hxS
  exact sub_eq_zero.mp (hx hxS)

end
end ArtinMatthews.SpectralCuspWeakRegularity

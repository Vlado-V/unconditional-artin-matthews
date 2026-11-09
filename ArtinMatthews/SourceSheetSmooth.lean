module

public import ArtinMatthews.SourceSheetDifferentiation
public import Mathlib.Analysis.Calculus.ContDiff.Deriv


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open MeasureTheory
open ArtinMatthews.VaryingKummerAnalytic
open scoped SchwartzMap ContDiff
noncomputable section
variable {Y : Type*} [MeasurableSpace Y]

/-- The actual sheet convolution is C∞ in total logarithmic norm. -/
theorem sourceSheetLogProfile_contDiff (ν : Measure Y) [SFinite ν]
    (N : Y → ℝ) (hN : ∀ y, 0 < N y) (hNm : Measurable N)
    (g : 𝓢(ℂ, ℂ)) (G : Y → ℂ) (hG : Measurable G) (σ : ℝ) (hσ : 0 < σ)
    (hInt : Integrable (fun y => ‖G y‖ * (N y) ^ σ) ν) :
    ContDiff ℝ ∞ (sourceSheetLogProfile ν N g G) := by
  have hd (g' : 𝓢(ℂ, ℂ)) (t : ℝ) :=
    sourceSheetLogProfile_hasDerivAt ν N hN hNm g' G hG σ hσ hInt t
  apply contDiff_infty.mpr
  intro n
  induction n generalizing g with
  | zero =>
    exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun t => (hd g t).continuousAt)
  | succ n ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun t => (hd g t).differentiableAt, by simp, ?_⟩
    rw [show deriv (sourceSheetLogProfile ν N g G) = fun t =>
      (1 / 2 : ℝ) • sourceSheetLogProfile ν N (sourceComplexEulerSchwartz g) G t from
      funext fun t => (hd g t).deriv]
    exact (ih (sourceComplexEulerSchwartz g)).const_smul (1 / 2 : ℝ)

end
end ArtinMatthews.SourcePhysical

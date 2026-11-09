module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs


set_option backward.privateInPublic true
@[expose] public section

/-! Dominated derivatives of the logarithmic sheet and smoothing
integrals. The common bound is placed on the actual derivative integrand. -/
namespace ArtinMatthews.SourceReflection

open MeasureTheory Set Filter
open scoped ContDiff
noncomputable section

theorem sourceThetaIntegral_hasDerivAt {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    (F F' : ℝ → Y → ℂ)
    (hF : ∀ t, Integrable (F t) μ) (hF' : ∀ t, AEStronglyMeasurable (F' t) μ)
    (hd : ∀ t y, HasDerivAt (fun x => F x y) (F' t y) t)
    (B : Y → ℝ) (hB : Integrable B μ) (hb : ∀ t y, ‖F' t y‖ ≤ B y) (t : ℝ) :
    HasDerivAt (fun x => ∫ y, F x y ∂μ) (∫ y, F' t y ∂μ) t :=
  (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := F) (F' := F') (bound := B) (s := univ) univ_mem
    (Eventually.of_forall fun x => (hF x).aestronglyMeasurable) (hF t) (hF' t)
    (Eventually.of_forall fun y x _ => hb x y) hB
    (Eventually.of_forall fun y x _ => hd x y)).2

theorem sourceThetaDerivativeFamily_contDiff (H : ℕ → ℝ → ℂ)
    (hd : ∀ n t, HasDerivAt (H n) (H (n + 1) t) t) : ContDiff ℝ ∞ (H 0) := by
  have h (m n : ℕ) : ContDiff ℝ m (H n) := by
    induction m generalizing n with
    | zero => exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun t => (hd n t).continuousAt)
    | succ m ih =>
      rw [Nat.cast_succ, contDiff_succ_iff_deriv]
      refine ⟨fun t => (hd n t).differentiableAt, by simp, ?_⟩
      rw [show deriv (H n) = H (n + 1) from funext fun t => (hd n t).deriv]
      exact ih (n + 1)
  exact contDiff_infty.mpr fun m => h m 0

theorem sourceThetaDerivativeFamily_iteratedDeriv (H : ℕ → ℝ → ℂ)
    (hd : ∀ n t, HasDerivAt (H n) (H (n + 1) t) t) (n : ℕ) :
    iteratedDeriv n (H 0) = H n := by
  induction n with
  | zero => exact iteratedDeriv_zero
  | succ n ih => rw [iteratedDeriv_succ, ih]; exact funext fun t => (hd n t).deriv

end
end ArtinMatthews.SourceReflection

module

public import ArtinMatthews.ShiftedVoronoiAdditiveContinuation
public import ArtinMatthews.ShiftedVoronoiGammaGrowth
public import Mathlib.Analysis.Real.Pi.Bounds


set_option backward.privateInPublic true
@[expose] public section

/-!
# Exponential strip growth of the actual additive L-function

The completed cusp Mellin transform is bounded on every closed strip. Combining
this with the proved reciprocal-Gamma estimate gives the growth required by
OAI's Gaussian-regulated contour shift; no Phragmén–Lindelöf input is needed.
-/

noncomputable section
open Complex UpperHalfPlane Set

namespace ArtinMatthews

/-- A genuine strip-growth bound, with all analytic premises discharged for
an actual cusp form at a rational additive twist. -/
theorem cuspAdditiveL_strip_exponential_bound
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 1) (x : ℚ) (a b : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, s.re ∈ Icc a b →
      ‖cuspAdditiveL f (x : ℝ) s‖ ≤ B * Real.exp (Real.pi * |s.im|) := by
  obtain ⟨C, hC, hcb⟩ := cuspVerticalRestriction_mellin_strip_bound f x a b
  obtain ⟨D, hD, hdb⟩ := reciprocalGamma_strip_exponential_bound a b
  refine ⟨(2 * Real.pi) ^ b * D * C, by positivity, ?_⟩
  intro s hs
  have hp : ‖((2 * Real.pi : ℝ) : ℂ) ^ s‖ ≤ (2 * Real.pi) ^ b := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) hs.2
  simp only [cuspAdditiveL, norm_mul]
  calc
    _ ≤ (2 * Real.pi) ^ b * (D * Real.exp (Real.pi * |s.im|)) * C := by
      gcongr
      · exact hdb s hs
      · exact hcb s hs.1 hs.2
    _ = _ := by ring

end ArtinMatthews

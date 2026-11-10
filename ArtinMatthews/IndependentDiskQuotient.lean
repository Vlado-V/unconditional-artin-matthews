module

public import ArtinMatthews.IndependentDiskFactors
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Complex.AbsMax

/-! The finite Blaschke quotient is extended at each selected zero by its
local analytic factor. This gives actual analytic values at the zeros and
preserves the boundary norm. -/

@[expose] public section

namespace ArtinMatthews

open Complex Filter Metric Set
open scoped BigOperators Classical Topology

noncomputable def independentDiskQuotient (R : ℝ) (S : Finset ℂ) (m : ℂ → ℕ)
    (f : ℂ → ℂ) (h : ℂ → ℂ → ℂ) (z : ℂ) : ℂ :=
  if z ∈ S then
    h z z * independentDiskDenominator R S m z / independentDiskVanishing (S.erase z) m z
  else
    f z * independentDiskDenominator R S m z / independentDiskVanishing S m z

private theorem diskEventually_outside {S : Finset ℂ} {z : ℂ} (hz : z ∉ S) :
    ∀ᶠ w in 𝓝 z, w ∉ S :=
  S.finite_toSet.isClosed.isOpen_compl.mem_nhds hz

private theorem diskQuotient_eventuallyEq {R : ℝ} {S : Finset ℂ} {m : ℂ → ℕ}
    {f : ℂ → ℂ} {h : ℂ → ℂ → ℂ} {z : ℂ} (hz : z ∉ S) :
    independentDiskQuotient R S m f h =ᶠ[𝓝 z] fun w =>
      f w * independentDiskDenominator R S m w / independentDiskVanishing S m w := by
  filter_upwards [diskEventually_outside hz] with w hw
  simp only [independentDiskQuotient, ite_eq_right hw]

theorem independentDiskQuotient_analytic {R : ℝ} {S : Finset ℂ} {m : ℂ → ℕ}
    {f : ℂ → ℂ} {h : ℂ → ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R))
    (hlocal : ∀ a ∈ S, AnalyticAt ℂ (h a) a ∧
      ∀ᶠ w in 𝓝 a, f w = (w - a) ^ m a * h a w) :
    AnalyticOnNhd ℂ (independentDiskQuotient R S m f h) (closedBall 0 R) := by
  intro z hz
  by_cases hzS : z ∈ S
  · let A := S.erase z
    let g : ℂ → ℂ := fun w =>
      h z w * independentDiskDenominator R S m w / independentDiskVanishing A m w
    have hzA : z ∉ A := Finset.notMem_erase _ _
    have hg : AnalyticAt ℂ g z := ((hlocal z hzS).1.mul
      (independentDiskDenominator_analytic R S m z)).div
      (independentDiskVanishing_analytic A m z) (independentDiskVanishing_ne_zero m hzA)
    refine hg.congr ?_
    filter_upwards [(hlocal z hzS).2, diskEventually_outside hzA] with w hw hwa
    by_cases he : w = z
    · subst w
      simp only [g, A, independentDiskQuotient, ite_eq_left hzS]
    · have hwS : w ∉ S := fun hh => hwa (Finset.mem_erase.mpr ⟨he, hh⟩)
      have hprod : independentDiskVanishing S m w =
          (w - z) ^ m z * independentDiskVanishing A m w :=
        (Finset.mul_prod_erase S (fun a => (w - a) ^ m a) hzS).symm
      rw [independentDiskQuotient, ite_eq_right hwS, hw, hprod]
      simp only [g, mul_assoc, mul_div_mul_left _ _ (pow_ne_zero _ (sub_ne_zero.mpr he))]
  · exact (((hf z hz).mul (independentDiskDenominator_analytic R S m z)).div
      (independentDiskVanishing_analytic S m z)
      (independentDiskVanishing_ne_zero m hzS)).congr (diskQuotient_eventuallyEq hzS).symm

theorem independentDiskQuotient_ne_zero {R R1 : ℝ} (hR1 : 0 < R1) (hR1R : R1 < R)
    {S : Finset ℂ} {m : ℂ → ℕ} {f : ℂ → ℂ} {h : ℂ → ℂ → ℂ}
    (hS : ∀ a, a ∈ S ↔ a ∈ closedBall (0 : ℂ) R1 ∧ f a = 0)
    (hlocal : ∀ a ∈ S, h a a ≠ 0)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) R1) :
    independentDiskQuotient R S m f h z ≠ 0 := by
  have hD := independentDiskDenominator_ne_zero (hR1.trans hR1R) m
    (fun a ha => (mem_closedBall_zero_iff.mp ((hS a).mp ha).1).trans_lt hR1R)
    ((mem_closedBall_zero_iff.mp hz).trans hR1R.le)
  by_cases hzS : z ∈ S
  · rw [independentDiskQuotient, ite_eq_left hzS]
    exact div_ne_zero (mul_ne_zero (hlocal z hzS) hD)
      (independentDiskVanishing_ne_zero m (Finset.notMem_erase z S))
  · rw [independentDiskQuotient, ite_eq_right hzS]
    exact div_ne_zero (mul_ne_zero (fun hf => hzS ((hS z).mpr ⟨hz, hf⟩)) hD)
      (independentDiskVanishing_ne_zero m hzS)

theorem independentDiskQuotient_norm_zero {R : ℝ} (hR : 0 < R)
    {S : Finset ℂ} {m : ℂ → ℕ} {f : ℂ → ℂ} {h : ℂ → ℂ → ℂ}
    (hS : ∀ a ∈ S, ‖a‖ ≤ R) (h0 : 0 ∉ S) (hf0 : f 0 = 1) :
    1 ≤ ‖independentDiskQuotient R S m f h 0‖ := by
  rw [independentDiskQuotient, ite_eq_right h0, hf0, one_mul, norm_div]
  exact (one_le_div₀ (norm_pos_iff.mpr (independentDiskVanishing_ne_zero m h0))).mpr
    (independentDiskVanishing_norm_zero_le hR m hS)

theorem independentDiskQuotient_norm_le {R B : ℝ} (hR : 0 < R)
    {S : Finset ℂ} {m : ℂ → ℕ} {f : ℂ → ℂ} {h : ℂ → ℂ → ℂ}
    (hS : ∀ a ∈ S, ‖a‖ < R)
    (hg : AnalyticOnNhd ℂ (independentDiskQuotient R S m f h) (closedBall 0 R))
    (hb : ∀ w ∈ closedBall 0 R, ‖f w‖ ≤ B)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) R) :
    ‖independentDiskQuotient R S m f h z‖ ≤ B := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) R)
    Metric.isBounded_ball (hg.differentiableOn.diffContOnCl_ball Subset.rfl)
  · intro w hw
    rw [frontier_ball _ hR.ne'] at hw
    have hws : w ∉ S := fun hh => (hS w hh).ne (mem_sphere_zero_iff_norm.mp hw)
    have hP := norm_ne_zero_iff.mpr (independentDiskVanishing_ne_zero m hws)
    rw [independentDiskQuotient, ite_eq_right hws, norm_div, norm_mul,
      independentDiskDenominator_norm_circle hR m hS hw, mul_div_cancel_right₀ _ hP]
    exact hb w (sphere_subset_closedBall hw)
  · rwa [closure_ball _ hR.ne']

theorem independentDiskQuotient_logDeriv {R : ℝ} (hR : 0 < R)
    {S : Finset ℂ} {m : ℂ → ℕ} {f : ℂ → ℂ} {h : ℂ → ℂ → ℂ}
    (hS : ∀ a ∈ S, ‖a‖ < R)
    {z : ℂ} (hz : ‖z‖ ≤ R) (hzS : z ∉ S) (hf : DifferentiableAt ℂ f z)
    (hfz : f z ≠ 0) :
    logDeriv (independentDiskQuotient R S m f h) z =
      logDeriv f z + logDeriv (independentDiskDenominator R S m) z -
        ∑ a ∈ S, (m a : ℂ) / (z - a) := by
  have he := (logDeriv_congr_nhds (diskQuotient_eventuallyEq
    (R := R) (m := m) (f := f) (h := h) hzS)).self_of_nhds
  rw [he]
  have hD := independentDiskDenominator_ne_zero hR m hS hz
  have hDd := (independentDiskDenominator_analytic R S m z).differentiableAt
  rw [logDeriv_fun_div (f := fun w => f w * independentDiskDenominator R S m w)
    (g := independentDiskVanishing S m) z (mul_ne_zero hfz hD)
    (independentDiskVanishing_ne_zero m hzS) (hf.mul hDd)
    (independentDiskVanishing_analytic S m z).differentiableAt,
    logDeriv_fun_mul (f := f) (g := independentDiskDenominator R S m) z hfz hD hf hDd,
    independentDiskVanishing_logDeriv m hzS]

end ArtinMatthews

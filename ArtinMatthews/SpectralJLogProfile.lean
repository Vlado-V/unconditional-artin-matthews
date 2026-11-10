module

public import ArtinMatthews.SourceSturmCore
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Covering.Besicovitch


set_option backward.privateInPublic true
@[expose] public section

/-! Actual compact positive profiles obtained from a fixed logarithmic
profile, with the ordinary real derivative and positive support. -/
namespace ArtinMatthews
open Set Filter
open scoped Topology ContDiff
noncomputable section

def spectralJLogProfile (g : ℝ → ℂ) (a x : ℝ) : ℂ :=
  if 0 < x then g (Real.log (x/a)) else 0

theorem spectralJLogProfile_tsupport {g : ℝ → ℂ} {a α β : ℝ}
    (ha : 0 < a) (hs : tsupport g ⊆ Icc α β) :
    tsupport (spectralJLogProfile g a) ⊆ Icc (a*Real.exp α) (a*Real.exp β) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hx0 : 0 < x := by
    by_contra hn
    exact hx (by simp only [spectralJLogProfile, if_neg hn])
  have hval : g (Real.log (x/a)) ≠ 0 := by
    change spectralJLogProfile g a x ≠ 0 at hx
    simpa only [spectralJLogProfile, if_pos hx0] using hx
  have hlog := hs (subset_closure hval)
  have he : a*Real.exp (Real.log (x/a)) = x := by
    rw [Real.exp_log (div_pos hx0 ha)]
    field_simp [ha.ne']
  constructor
  · have h := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hlog.1) ha.le
    rwa [he] at h
  · have h := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hlog.2) ha.le
    rwa [he] at h

theorem spectralJLogProfile_positive_tsupport {g : ℝ → ℂ} {a α β : ℝ}
    (ha : 0 < a) (hs : tsupport g ⊆ Icc α β) :
    tsupport (spectralJLogProfile g a) ⊆ Ioi 0 :=
  fun _ hx => lt_of_lt_of_le (mul_pos ha (Real.exp_pos α)) (spectralJLogProfile_tsupport ha hs hx).1

theorem spectralJLogProfile_hasCompactSupport {g : ℝ → ℂ} {a α β : ℝ}
    (ha : 0 < a) (hs : tsupport g ⊆ Icc α β) :
    HasCompactSupport (spectralJLogProfile g a) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (spectralJLogProfile_tsupport ha hs)

theorem spectralJLogProfile_contDiffAt_pos {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    ContDiffAt ℝ ∞ (spectralJLogProfile g a) x := by
  have hlog : ContDiffAt ℝ ∞ (fun y : ℝ => Real.log (y/a)) x :=
    (contDiffAt_id.div_const a).log (div_ne_zero hx.ne' ha.ne')
  apply (hg.contDiffAt.comp x hlog).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact if_pos hy

theorem spectralJLogProfile_contDiff {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) {a α β : ℝ}
    (ha : 0 < a) (hs : tsupport g ⊆ Icc α β) :
    ContDiff ℝ ∞ (spectralJLogProfile g a) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport (spectralJLogProfile g a)
  · exact spectralJLogProfile_contDiffAt_pos hg ha (spectralJLogProfile_positive_tsupport ha hs hx)
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hx)

private theorem spectralJLogCoordinate_hasDerivAt {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => Real.log (y/a)) x⁻¹ x := by
  have h := ((hasDerivAt_id x).div_const a).log (div_ne_zero hx.ne' ha.ne')
  have he : (1 : ℝ)/a/(x/a) = x⁻¹ := by field_simp [ha.ne',hx.ne']
  simpa only [id_eq, he] using h

theorem spectralJLogProfile_hasDerivAt {g : ℝ → ℂ} {a x : ℝ}
    (ha : 0 < a) (hx : 0 < x) (hg : DifferentiableAt ℝ g (Real.log (x/a))) :
    HasDerivAt (spectralJLogProfile g a)
      ((x : ℂ)⁻¹*deriv g (Real.log (x/a))) x := by
  have h := hg.hasDerivAt.scomp x (spectralJLogCoordinate_hasDerivAt ha hx)
  have hc : HasDerivAt (fun y : ℝ => g (Real.log (y/a)))
      ((x : ℂ)⁻¹*deriv g (Real.log (x/a))) x := by
    simpa only [Function.comp_def, Complex.real_smul, Complex.ofReal_inv] using h
  apply hc.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact if_pos hy

theorem spectralJLogProfile_deriv {g : ℝ → ℂ} {a x : ℝ}
    (ha : 0 < a) (hx : 0 < x) (hg : DifferentiableAt ℝ g (Real.log (x/a))) :
    deriv (spectralJLogProfile g a) x = (x : ℂ)⁻¹*deriv g (Real.log (x/a)) :=
  (spectralJLogProfile_hasDerivAt ha hx hg).deriv

theorem spectralJLogProfile_flux {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    SourceSturm.sturmFlux (spectralJLogProfile g a) x = deriv g (Real.log (x/a)) := by
  unfold SourceSturm.sturmFlux
  rw [spectralJLogProfile_deriv ha hx (hg.differentiable (by simp) _),
    ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hx.ne'), one_mul]

theorem spectralJLogProfile_flux_deriv {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    deriv (SourceSturm.sturmFlux (spectralJLogProfile g a)) x =
      (x : ℂ)⁻¹*deriv (deriv g) (Real.log (x/a)) := by
  have hdg : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hg).2
  have h := spectralJLogProfile_hasDerivAt ha hx (hdg.differentiable (by simp) _)
  have he : SourceSturm.sturmFlux (spectralJLogProfile g a) =ᶠ[𝓝 x]
      spectralJLogProfile (deriv g) a := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    change 0 < y at hy
    rw [spectralJLogProfile_flux hg ha hy, spectralJLogProfile, if_pos hy]
  exact (h.congr_of_eventuallyEq he).deriv

theorem spectralJLogProfile_exp {g : ℝ → ℂ} {a : ℝ} (ha : 0 < a) (v : ℝ) :
    spectralJLogProfile g a (a*Real.exp v) = g v := by
  rw [spectralJLogProfile, if_pos (mul_pos ha (Real.exp_pos v)),
    mul_div_cancel_left₀ _ ha.ne', Real.log_exp]

end
end ArtinMatthews

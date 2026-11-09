module

public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv


set_option backward.privateInPublic true
@[expose] public section

/-! Logarithmic compactification and the two ordinary derivatives of its pullback. -/
namespace ArtinMatthews
open Set Filter
open scoped Topology ContDiff
noncomputable section

def spectralLogCompactProfile (g : ℝ → ℂ) (u : ℝ) : ℂ :=
  if 0 < u then g (-Real.log u) / (u : ℂ) else 0

def spectralExpPullback (h : ℝ → ℂ) (s : ℝ) : ℂ :=
  (Real.exp (-s) : ℂ) * h (Real.exp (-s))

theorem spectralExpPullback_logCompactProfile (g : ℝ → ℂ) :
    spectralExpPullback (spectralLogCompactProfile g) = g := by
  funext s
  rw [spectralExpPullback, spectralLogCompactProfile, ite_eq_left (Real.exp_pos _),
    Real.log_exp, neg_neg, mul_div_cancel₀]
  exact_mod_cast (Real.exp_pos (-s)).ne'

theorem spectralLogCompactProfile_contDiff
    {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    ContDiff ℝ ∞ (spectralLogCompactProfile g) := by
  change IsCompact (tsupport g) at hc
  obtain ⟨R, hR⟩ := hc.bddAbove
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : 0 < u
  · have hlog₀ : ContDiffAt ℝ ∞ Real.log u := Real.contDiffAt_log.mpr hu.ne'
    have hlog : ContDiffAt ℝ ∞ (fun v : ℝ => -Real.log v) u := hlog₀.neg
    have hInv : ContDiffAt ℝ ∞ (fun v : ℝ => v⁻¹) u :=
      (contDiffAt_id : ContDiffAt ℝ ∞ (id : ℝ → ℝ) u).inv hu.ne'
    have hcast : ContDiffAt ℝ ∞ (fun v : ℝ => ((v⁻¹ : ℝ) : ℂ)) u :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp u hInv
    have hnum : ContDiffAt ℝ ∞ (fun v : ℝ => g (-Real.log v)) u :=
      (hg.contDiffAt (x := -Real.log u)).comp u hlog
    have hcomp : ContDiffAt ℝ ∞ (fun v : ℝ => g (-Real.log v) * ((v⁻¹ : ℝ) : ℂ)) u :=
      hnum.mul hcast
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hu] with v hv
    have hv' : 0 < v := hv
    rw [spectralLogCompactProfile, ite_eq_left hv', Complex.ofReal_inv, div_eq_mul_inv]
  · have hU : u < Real.exp (-R) := (le_of_not_gt hu).trans_lt (Real.exp_pos _)
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℂ)) u).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hU] with v hv
    unfold spectralLogCompactProfile
    by_cases hvpos : 0 < v
    · have hl := Real.log_lt_log hvpos hv
      rw [Real.log_exp] at hl
      have hz : g (-Real.log v) = 0 := image_eq_zero_of_notMem_tsupport (fun hm =>
        (not_le_of_gt (by linarith : R < -Real.log v)) (hR hm))
      rw [ite_eq_left hvpos, hz, zero_div]
    · exact ite_eq_right hvpos

theorem spectralExpPullback_hasDerivAt {h : ℝ → ℂ} {s : ℝ}
    (hh : DifferentiableAt ℝ h (Real.exp (-s))) :
    HasDerivAt (spectralExpPullback h)
      (-(Real.exp (-s) : ℂ) *
        (h (Real.exp (-s)) + (Real.exp (-s) : ℂ) * deriv h (Real.exp (-s)))) s := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-s)) s := by
    simpa only [mul_neg, mul_one] using (hasDerivAt_neg' s).exp
  have hc : HasDerivAt (fun t : ℝ => h (Real.exp (-t)))
      (-(Real.exp (-s) : ℂ) * deriv h (Real.exp (-s))) s := by
    simpa only [Function.comp_def, Complex.real_smul, Complex.ofReal_neg] using!
      hh.hasDerivAt.scomp s he
  have hp := he.ofReal_comp.fun_mul hc
  change HasDerivAt (fun t : ℝ => (Real.exp (-t) : ℂ) * h (Real.exp (-t))) _ s
  convert hp using 1 <;> simp only [Complex.ofReal_neg] <;> ring

theorem spectralExpPullback_deriv
    {h : ℝ → ℂ} (hh : Differentiable ℝ h) (s : ℝ) :
    deriv (spectralExpPullback h) s =
      -(Real.exp (-s) : ℂ) *
        (h (Real.exp (-s)) + (Real.exp (-s) : ℂ) * deriv h (Real.exp (-s))) :=
  (spectralExpPullback_hasDerivAt (hh _)).deriv

theorem spectralExpPullback_deriv_two
    {h : ℝ → ℂ} (hh : Differentiable ℝ h) (hh' : Differentiable ℝ (deriv h)) (s : ℝ) :
    deriv (deriv (spectralExpPullback h)) s =
      (Real.exp (-s) : ℂ) *
        (h (Real.exp (-s)) + 3 * (Real.exp (-s) : ℂ) * deriv h (Real.exp (-s)) +
          (Real.exp (-s) : ℂ)^2 * deriv (deriv h) (Real.exp (-s))) := by
  let b (u : ℝ) := h u + (u : ℂ) * deriv h u
  have hb (u : ℝ) : HasDerivAt b
      (2 * deriv h u + (u : ℂ) * deriv (deriv h) u) u := by
    have hm : HasDerivAt (fun t : ℝ => (t : ℂ) * deriv h t)
        (deriv h u + (u : ℂ) * deriv (deriv h) u) u := by
      simpa only [id_eq, Complex.ofReal_one, one_mul] using
        (hasDerivAt_id u).ofReal_comp.fun_mul (hh' u).hasDerivAt
    change HasDerivAt (fun t : ℝ => h t + (t : ℂ) * deriv h t) _ u
    convert (hh u).hasDerivAt.fun_add hm using 1 <;> ring
  have hd : deriv (spectralExpPullback h) = fun t => -spectralExpPullback b t := by
    funext t
    rw [spectralExpPullback_deriv hh]
    change -(Real.exp (-t) : ℂ) * b (Real.exp (-t)) =
      -((Real.exp (-t) : ℂ) * b (Real.exp (-t)))
    rw [neg_mul]
  rw [hd, (spectralExpPullback_hasDerivAt (hb (Real.exp (-s))).differentiableAt).fun_neg.deriv,
    (hb (Real.exp (-s))).deriv]
  dsimp only [b]
  ring

end
end ArtinMatthews

module

public import ArtinMatthews.VaryingKummerAnalyticLogarithmicResidue


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine local principal parts for a meromorphic logarithmic derivative.
The weighted dslope construction generalizes the proof in OpenAI's
Ostmann/ZeroDensity/SmoothContourRegularPart to arbitrary meromorphic order. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open Complex Set Filter
open scoped Topology
noncomputable section

theorem meromorphic_logDeriv_local_split {f : ℂ → ℂ} {x : ℂ} {n : ℤ}
    (hf : MeromorphicAt f x) (ho : meromorphicOrderAt f x = n) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g x ∧ g x ≠ 0 ∧
      logDeriv f =ᶠ[𝓝[≠] x] (fun z => (n : ℂ)/(z-x)+logDeriv g z) := by
  obtain ⟨g,hga,hgn,hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp ho
  refine ⟨g,hga,hgn,?_⟩
  filter_upwards [logDeriv_congr_nhdsNE hfg,
    hga.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    hga.continuousAt.eventually_ne hgn |>.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hgz hgnz hzx
  have hzx' : z-x ≠ 0 := sub_ne_zero.mpr (by simpa using hzx)
  rw [hz]
  change logDeriv (fun z => (z-x)^n*g z) z = _
  rw [logDeriv_fun_mul (f := fun z => (z-x)^n) (g := g) z
    (zpow_ne_zero _ hzx') hgnz
    ((differentiableAt_id.sub_const x).zpow (Or.inl hzx')) hgz.differentiableAt,
    logDeriv_fun_zpow (f := fun w : ℂ => w-x) (x := z) (by fun_prop) n]
  have hsub : logDeriv (fun z : ℂ => z-x) z = 1/(z-x) := by
    rw [logDeriv_apply, ((hasDerivAt_id' z).sub_const x).deriv]
  rw [hsub]
  ring

/-- Removing the actual weighted logarithmic principal part gives an analytic
function. This holds for zeros and poles, with their signed integer orders. -/
theorem meromorphic_weighted_logDeriv_regular_part {f W : ℂ → ℂ} {x : ℂ} {n : ℤ}
    (hf : MeromorphicAt f x) (ho : meromorphicOrderAt f x = n) (hW : AnalyticAt ℂ W x) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R x ∧
      (fun s => -logDeriv f s*W s+(n : ℂ)*W x/(s-x)) =ᶠ[𝓝[≠] x] R := by
  obtain ⟨g,hg,hgne,hsplit⟩ := meromorphic_logDeriv_local_split hf ho
  have hds : AnalyticAt ℂ (dslope W x) x := by
    obtain ⟨p,hp⟩ := hW
    exact ⟨p.fslope,hp.has_fpower_series_dslope_fslope⟩
  have hlog : AnalyticAt ℂ (logDeriv g) x := hg.deriv.div hg hgne
  let R : ℂ → ℂ := fun s => -(n : ℂ)*dslope W x s-logDeriv g s*W s
  refine ⟨R,(analyticAt_const.mul hds).sub (hlog.mul hW),?_⟩
  filter_upwards [hsplit,self_mem_nhdsWithin] with s hs hsz
  rw [hs]
  dsimp only [R]
  rw [dslope_of_ne W hsz]
  simp only [slope,smul_eq_mul,vsub_eq_sub]
  ring

end
end ArtinMatthews.VaryingKummerAnalytic

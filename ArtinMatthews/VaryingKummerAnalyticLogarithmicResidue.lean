module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.Complex.CauchyIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! The exact logarithmic residue attached to a genuine meromorphic order.
This generic local analytic fact is used for the actual Dedekind pole and zeros. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open Complex Set Filter
open scoped Topology
noncomputable section

theorem meromorphic_logDeriv_residue {f : ℂ → ℂ} {x : ℂ} {n : ℤ}
    (hf : MeromorphicAt f x) (ho : meromorphicOrderAt f x = n) :
    Tendsto (fun z => (z-x)*logDeriv f z) (𝓝[≠] x) (𝓝 (n : ℂ)) := by
  obtain ⟨g,hga,hgn,hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp ho
  have hlog := logDeriv_congr_nhdsNE hfg
  have hc : ContinuousAt (logDeriv g) x :=
    hga.deriv.continuousAt.div hga.continuousAt hgn
  have HL : Tendsto (fun z => (n : ℂ)+(z-x)*logDeriv g z) (𝓝[≠] x) (𝓝 (n : ℂ)) := by
    have hx : ContinuousAt (fun z : ℂ => z-x) x := by fun_prop
    have H : Tendsto (fun z : ℂ => (n : ℂ)+(z-x)*logDeriv g z) (𝓝 x)
        (𝓝 ((n : ℂ)+(x-x)*logDeriv g x)) :=
      tendsto_const_nhds.add (hx.tendsto.mul hc.tendsto)
    simpa using H.mono_left nhdsWithin_le_nhds
  apply HL.congr'
  filter_upwards [hlog,hga.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    hga.continuousAt.eventually_ne hgn |>.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hgz hgnz hzx
  have hzx' : z-x ≠ 0 := sub_ne_zero.mpr (by simpa using hzx)
  rw [hz]
  change (n : ℂ)+(z-x)*logDeriv g z = (z-x)*logDeriv (fun z => (z-x)^n*g z) z
  rw [logDeriv_fun_mul (f := fun z => (z-x)^n) (g := g) z
    (zpow_ne_zero _ hzx') hgnz
    ((differentiableAt_id.sub_const x).zpow (Or.inl hzx')) hgz.differentiableAt,
    logDeriv_fun_zpow (f := fun w : ℂ => w-x) (x := z)
      (by fun_prop) n]
  have hsub : logDeriv (fun z : ℂ => z-x) z = 1/(z-x) := by
    rw [logDeriv_apply, ((hasDerivAt_id' z).sub_const x).deriv]
  rw [hsub]
  field_simp

/-- Multiplying by an analytic Mellin weight multiplies the logarithmic
residue by its actual value at the pole. -/
theorem meromorphic_weighted_logDeriv_residue {f w : ℂ → ℂ} {x : ℂ} {n : ℤ}
    (hf : MeromorphicAt f x) (ho : meromorphicOrderAt f x = n)
    (hw : ContinuousAt w x) :
    Tendsto (fun z => (z-x)*(w z*logDeriv f z)) (𝓝[≠] x) (𝓝 (w x*(n : ℂ))) := by
  have H := (hw.tendsto.mono_left nhdsWithin_le_nhds).mul (meromorphic_logDeriv_residue hf ho)
  convert H using 1
  ext z
  ring

end
end ArtinMatthews.VaryingKummerAnalytic

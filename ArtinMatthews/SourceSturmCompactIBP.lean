module

public import ArtinMatthews.SourceSturmCore
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper


set_option backward.privateInPublic true
@[expose] public section

/-! Bilinear Sturm integration by parts with the literal positive dx/x weight. -/
namespace ArtinMatthews.SourceSturm
open MeasureTheory Set Filter
open scoped Topology ContDiff
noncomputable section

theorem sturmFlux_contDiffAt {f : ℝ → ℂ} {x : ℝ} (hf : ContDiffAt ℝ 2 f x) :
    ContDiffAt ℝ 1 (sturmFlux f) x := by
  have hcast : ContDiffAt ℝ 1 (fun y : ℝ => (y : ℂ)) x := Complex.ofRealCLM.contDiff.contDiffAt
  exact hcast.mul (hf.derivWithin (m := 1) (by norm_num))

theorem sturmFlux_deriv {f : ℝ → ℂ} {x : ℝ} (hf : ContDiffAt ℝ 2 f x) :
    deriv (sturmFlux f) x = deriv f x + (x : ℂ) * deriv (deriv f) x := by
  have hcast : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := (hasDerivAt_id x).ofReal_comp
  have hD := (hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  change deriv ((fun y : ℝ => (y : ℂ)) * deriv f) x = _
  simpa only [one_mul] using (hcast.mul hD.hasDerivAt).deriv

theorem sturmD_div_eq {f : ℝ → ℂ} {x : ℝ} (hf : ContDiffAt ℝ 2 f x) (hx : 0 < x) :
    sturmD f x / (x : ℂ) = deriv (sturmFlux f) x + (x : ℂ) * f x := by
  rw [sturmD,sturmFlux_deriv hf]
  field_simp [Complex.ofReal_ne_zero.mpr hx.ne'] <;> ring

theorem sturm_compact_first_order_ibp {f J : ℝ → ℂ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi (0 : ℝ))
    (hJ : ∀ x ∈ Ioi (0 : ℝ), ContDiffAt ℝ 1 J x) :
    (∫ x, f x * deriv J x) = -(∫ x, deriv f x * J x) := by
  have hJ' (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) : ContinuousAt (deriv J) x :=
    ((hJ x hx).derivWithin (m := 0) (by norm_num)).continuousAt
  have hI : Integrable (fun x => f x * deriv J x) :=
    sturm_compact_mul_integrable hf.continuous hc (fun x hx => hJ' x (hs hx))
  have hK : Integrable (fun x => deriv f x * J x) :=
    sturm_compact_mul_integrable hf.continuous_deriv_one hc.deriv
      (fun x hx => (hJ x (hs (tsupport_deriv_subset hx))).continuousAt)
  have hL : Integrable (fun x => f x * J x) :=
    sturm_compact_mul_integrable hf.continuous hc (fun x hx => (hJ x (hs hx)).continuousAt)
  exact integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => ((hf.differentiable (by norm_num)) x).hasDerivAt)
    (fun x hx => ((hJ x (hs hx)).differentiableAt (by norm_num)).hasDerivAt) hI hK hL

theorem sturm_compact_flux_ibp {f J : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi (0 : ℝ))
    (hJ : ∀ x ∈ Ioi (0 : ℝ), ContDiffAt ℝ 2 J x) :
    (∫ x, f x * deriv (sturmFlux J) x) = ∫ x, deriv (sturmFlux f) x * J x := by
  have hF := sturmFlux_smooth hf
  have hFc : HasCompactSupport (sturmFlux f) :=
    hc.of_isClosed_subset isClosed_closure (sturmFlux_tsupport f)
  have h₁ := sturm_compact_first_order_ibp (hf.of_le (by simp)) hc hs
    (fun x hx => sturmFlux_contDiffAt (hJ x hx))
  have h₂ := sturm_compact_first_order_ibp (hF.of_le (by simp)) hFc
    ((sturmFlux_tsupport f).trans hs) (fun x hx => (hJ x hx).of_le (by norm_num))
  have he : (∫ x, deriv f x * sturmFlux J x) = ∫ x, sturmFlux f x * deriv J x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by unfold sturmFlux; ring
  rw [h₁,he,h₂,neg_neg]

theorem sturmPair_ibp {f J : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi (0 : ℝ))
    (hJ : ContDiffOn ℝ 2 J (Ioi (0 : ℝ))) :
    sturmPair f (sturmD J) = sturmPair (sturmD f) J := by
  have hJAt (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) : ContDiffAt ℝ 2 J x :=
    (hJ x hx).contDiffAt (isOpen_Ioi.mem_nhds hx)
  let L : ℝ → ℂ := fun x => f x * deriv (sturmFlux J) x
  let R : ℝ → ℂ := fun x => deriv (sturmFlux f) x * J x
  let Q : ℝ → ℂ := fun x => (x : ℂ) * f x * J x
  have hL : Integrable L := sturm_compact_mul_integrable hf.continuous hc (fun x hx =>
    ((sturmFlux_contDiffAt (hJAt x (hs hx))).derivWithin (m := 0) (by norm_num)).continuousAt)
  have hFc : HasCompactSupport (sturmFlux f) :=
    hc.of_isClosed_subset isClosed_closure (sturmFlux_tsupport f)
  have hR : Integrable R := sturm_compact_mul_integrable
    ((contDiff_infty_iff_deriv.mp (sturmFlux_smooth hf)).2.continuous) hFc.deriv
    (fun x hx => (hJAt x (hs (sturmFlux_tsupport f (tsupport_deriv_subset hx)))).continuousAt)
  have hQ : Integrable Q := by
    have h : Integrable (fun x => f x * ((x : ℂ) * J x)) :=
      sturm_compact_mul_integrable hf.continuous hc
        (fun x hx => Complex.continuous_ofReal.continuousAt.mul (hJAt x (hs hx)).continuousAt)
    apply h.congr
    exact Eventually.of_forall fun x => by dsimp only [Q]; ring
  have hleft : sturmPair f (sturmD J) = (∫ x, L x) + ∫ x, Q x := by
    unfold sturmPair
    calc
      _ = ∫ x in Ioi (0 : ℝ), L x + Q x := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hx0 : 0 < x := hx
        rw [mul_div_assoc,sturmD_div_eq (hJAt x hx) hx0]
        dsimp only [L,Q]
        ring
      _ = ∫ x, L x + Q x := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        have hz : f x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
        simp only [L,Q,hz,zero_mul,mul_zero,add_zero]
      _ = _ := integral_add hL hQ
  have hright : sturmPair (sturmD f) J = (∫ x, R x) + ∫ x, Q x := by
    unfold sturmPair
    calc
      _ = ∫ x in Ioi (0 : ℝ), R x + Q x := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hx0 : 0 < x := hx
        rw [← div_mul_eq_mul_div,sturmD_div_eq ((hf.of_le (by simp)).contDiffAt) hx0]
        dsimp only [R,Q]
        ring
      _ = ∫ x, R x + Q x := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        have hno : x ∉ tsupport f := fun h => hx (hs h)
        have hz : f x = 0 := image_eq_zero_of_notMem_tsupport hno
        have hd : deriv (sturmFlux f) x = 0 :=
          deriv_of_notMem_tsupport (fun h => hno (sturmFlux_tsupport f h))
        simp only [R,Q,hz,hd,zero_mul,mul_zero,add_zero]
      _ = _ := integral_add hR hQ
  rw [hleft,hright]
  exact congrArg (· + ∫ x, Q x) (sturm_compact_flux_ibp hf hc hs hJAt)

end
end ArtinMatthews.SourceSturm

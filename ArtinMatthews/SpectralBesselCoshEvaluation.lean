module

public import ArtinMatthews.SpectralBesselHyperbolicEvaluation
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

/-! The usual half-line cosh representation evaluates the actual arbitrary-
order Schläfli K.  Its absolute integrability is proved, not assumed. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

theorem integral_positive_negative_pair (F : ℝ → ℂ) (hF : Integrable F) :
    (∫ u : ℝ, F u) = ∫ u in Ioi (0 : ℝ), F (-u)+F u := by
  have hm : Integrable (fun u : ℝ => F (-u)) :=
    ((Measure.measurePreserving_neg volume).integrable_comp_emb
      (Homeomorph.neg ℝ).measurableEmbedding).mpr hF
  have hn : (∫ u in Iic (0 : ℝ), F u) = ∫ u in Ioi (0 : ℝ), F (-u) := by
    simpa only [neg_zero] using (integral_comp_neg_Ioi (0 : ℝ) F).symm
  rw [← intervalIntegral.integral_Iic_add_Ioi hF.restrict hF.restrict,hn,
    ← integral_add hm.restrict hF.restrict]

def spectralKCoshKernel (ν : ℂ) (x u : ℝ) : ℂ :=
  Complex.exp (-(x*Real.cosh u) : ℝ) * Complex.cosh (ν*(u : ℂ))

theorem spectralKLogKernel_pair (ν : ℂ) (x u : ℝ) :
    spectralKLogKernel ν x (-u)+spectralKLogKernel ν x u =
      2*spectralKCoshKernel ν x u := by
  unfold spectralKLogKernel spectralKCoshKernel
  simp only [Real.cosh_neg,Complex.ofReal_neg,mul_neg]
  rw [Complex.exp_add,Complex.exp_add]
  linear_combination -(Complex.exp (-((x*Real.cosh u : ℝ) : ℂ))) * Complex.two_cosh (ν*(u : ℂ))

theorem schlafliBesselK_cosh_integral (ν : ℂ) {x : ℝ} (hx : 0 < x) :
    OAI.CubicEisenstein.schlafliBesselK ν x =
      ∫ u in Ioi (0 : ℝ), spectralKCoshKernel ν x u := by
  rw [schlafliBesselK_hyperbolic_integral ν hx,
    integral_positive_negative_pair _ (spectralKLogKernel_integrable ν hx)]
  simp_rw [spectralKLogKernel_pair]
  rw [integral_const_mul]
  ring

theorem spectralKCoshKernel_integrable (ν : ℂ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (spectralKCoshKernel ν x) (Ioi (0 : ℝ)) := by
  have hI := spectralKLogKernel_integrable ν hx
  have hm : Integrable (fun u : ℝ => spectralKLogKernel ν x (-u)) :=
    ((Measure.measurePreserving_neg volume).integrable_comp_emb
      (Homeomorph.neg ℝ).measurableEmbedding).mpr hI
  have hh : IntegrableOn (fun u => spectralKLogKernel ν x (-u)+spectralKLogKernel ν x u)
      (Ioi (0 : ℝ)) := hm.restrict.add hI.restrict
  have h := hh.const_mul (1/2 : ℂ)
  apply h.congr
  filter_upwards [] with u
  rw [spectralKLogKernel_pair]
  ring

end ArtinMatthews

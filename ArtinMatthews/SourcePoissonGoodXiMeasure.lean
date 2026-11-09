module

public import ArtinMatthews.SourcePoissonGoodHeightMajorants


set_option backward.privateInPublic true
@[expose] public section

/-! Restricted product measures for the exact finite ξ rectangle and
its original right tail. All Bochner integrals are identified by
absolute Fubini before their individual norms are estimated. -/
namespace ArtinMatthews.SourcePhysical
open Set MeasureTheory VaryingKummerAnalytic
noncomputable section

local notation "μwt" => Measure.prod (volume : Measure ℝ) (volume : Measure ℝ)

def sourcePoissonHeightRestrict (s : Set ℝ) : Measure SourcePoissonHeights :=
  Measure.prod μwt (volume.restrict s)

theorem sourcePoissonHeightRestrict_eq (s : Set ℝ) :
    sourcePoissonHeightRestrict s = sourcePoissonHeightMeasure.restrict (univ ×ˢ s) := by
  simpa only [sourcePoissonHeightRestrict, sourcePoissonHeightMeasure, Measure.restrict_univ] using
    (Measure.prod_restrict (μ := μwt) (ν := (volume : Measure ℝ)) (univ : Set (ℝ×ℝ)) s)

theorem sourcePoissonHeightRestrict_integrable_of_majorant
    (s : Set ℝ) (hs : MeasurableSet s) (f : SourcePoissonHeights → ℂ) (g : SourcePoissonHeights → ℝ)
    (hf : ContinuousOn f (univ ×ˢ s)) (hg : Integrable g (sourcePoissonHeightRestrict s))
    (h : ∀ p, p.2 ∈ s → ‖f p‖ ≤ g p) : Integrable f (sourcePoissonHeightRestrict s) := by
  rw [sourcePoissonHeightRestrict_eq] at hg ⊢
  have hset : MeasurableSet ((univ : Set (ℝ×ℝ)) ×ˢ s) := MeasurableSet.univ.prod hs
  apply hg.mono' (hf.aestronglyMeasurable hset)
  filter_upwards [ae_restrict_mem hset] with p hp using h p hp.2

theorem sourcePoissonHeightRestrict_integral_norm_le
    (s : Set ℝ) (hs : MeasurableSet s) (f : SourcePoissonHeights → ℂ) (g : SourcePoissonHeights → ℝ)
    (hg : Integrable g (sourcePoissonHeightRestrict s)) (h : ∀ p, p.2 ∈ s → ‖f p‖ ≤ g p) :
    ‖∫ p, f p ∂sourcePoissonHeightRestrict s‖ ≤ ∫ p, g p ∂sourcePoissonHeightRestrict s := by
  rw [sourcePoissonHeightRestrict_eq] at hg ⊢
  apply norm_integral_le_of_norm_le hg
  filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod hs)] with p hp using h p hp.2

theorem sourcePoissonHeightRestrict_integral_le_full
    (s : Set ℝ) (g : SourcePoissonHeights → ℝ)
    (hg : Integrable g sourcePoissonHeightMeasure) (h : ∀ p, 0 ≤ g p) :
    (∫ p, g p ∂sourcePoissonHeightRestrict s) ≤ ∫ p, g p ∂sourcePoissonHeightMeasure := by
  rw [sourcePoissonHeightRestrict_eq]
  exact setIntegral_le_integral hg (ae_of_all _ h)

theorem sourcePoissonHeightRestrict_Ioc_fst_integrable {a b : ℝ}
    (g : (ℝ × ℝ) → ℝ) (hg : Integrable g μwt) :
    Integrable (fun p : SourcePoissonHeights => g p.1) (sourcePoissonHeightRestrict (Ioc a b)) := by
  let : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  exact hg.comp_fst _

theorem sourcePoissonHeightRestrict_Ioc_fst_mass {a b : ℝ} (hab : a ≤ b) (g : (ℝ × ℝ) → ℝ) :
    (∫ p : SourcePoissonHeights, g p.1 ∂sourcePoissonHeightRestrict (Ioc a b)) =
      (∫ wt : ℝ × ℝ, g wt ∂μwt)*(b-a) := by
  have h : (∫ p : SourcePoissonHeights, g p.1 ∂sourcePoissonHeightRestrict (Ioc a b)) =
      (∫ wt : ℝ × ℝ, g wt ∂μwt)*(∫ _ : ℝ in Ioc a b, (1 : ℝ)) := by
    simpa only [sourcePoissonHeightRestrict, mul_one] using
      (integral_prod_mul (μ := μwt) (ν := (volume : Measure ℝ).restrict (Ioc a b)) g (fun _ : ℝ => (1 : ℝ)))
  rw [h, integral_const, measureReal_def, Measure.restrict_apply_univ, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab), smul_eq_mul, mul_one]

def sourcePoissonXiVerticalKernel (K : ℂ → (ℝ×ℝ) → ℂ) (a : ℝ) (p : SourcePoissonHeights) : ℂ :=
  K (sourcePoissonVertical a p.2) p.1

def sourcePoissonXiHorizontalKernel (K : ℂ → (ℝ×ℝ) → ℂ) (x : ℝ) (p : SourcePoissonHeights) : ℂ :=
  K (sourcePoissonVertical p.2 x) p.1

theorem sourcePoissonFiniteXi_parts_integral
    (K : ℂ → (ℝ×ℝ) → ℂ) {a b T : ℝ} (hab : a ≤ b) (hT : 0 ≤ T)
    (hL : Integrable (sourcePoissonXiVerticalKernel K a) (sourcePoissonHeightRestrict (Ioc (-T) T)))
    (hB : Integrable (sourcePoissonXiHorizontalKernel K (-T)) (sourcePoissonHeightRestrict (Ioc a b)))
    (hH : Integrable (sourcePoissonXiHorizontalKernel K T) (sourcePoissonHeightRestrict (Ioc a b)))
    (hR : Integrable (sourcePoissonXiVerticalKernel K b) (sourcePoissonHeightRestrict (Ioc (-T) T)ᶜ)) :
    (∫ wt : ℝ×ℝ, finiteVerticalIntegral (fun ξ => K ξ wt) a T +
      finiteHorizontalError (fun ξ => K ξ wt) a b T + rightVerticalTail (fun ξ => K ξ wt) b T ∂μwt) =
      (∫ p, sourcePoissonXiVerticalKernel K a p ∂sourcePoissonHeightRestrict (Ioc (-T) T)) +
      Complex.I*((∫ p, sourcePoissonXiHorizontalKernel K (-T) p ∂sourcePoissonHeightRestrict (Ioc a b)) -
        (∫ p, sourcePoissonXiHorizontalKernel K T p ∂sourcePoissonHeightRestrict (Ioc a b))) +
      (∫ p, sourcePoissonXiVerticalKernel K b p ∂sourcePoissonHeightRestrict (Ioc (-T) T)ᶜ) := by
  let L (wt : ℝ×ℝ) := ∫ x : ℝ in Ioc (-T) T, sourcePoissonXiVerticalKernel K a (wt,x)
  let B (wt : ℝ×ℝ) := ∫ x : ℝ in Ioc a b, sourcePoissonXiHorizontalKernel K (-T) (wt,x)
  let H (wt : ℝ×ℝ) := ∫ x : ℝ in Ioc a b, sourcePoissonXiHorizontalKernel K T (wt,x)
  let R (wt : ℝ×ℝ) := ∫ x : ℝ in (Ioc (-T) T)ᶜ, sourcePoissonXiVerticalKernel K b (wt,x)
  have hL' : Integrable L μwt := hL.integral_prod_left
  have hB' : Integrable B μwt := hB.integral_prod_left
  have hH' : Integrable H μwt := hH.integral_prod_left
  have hR' : Integrable R μwt := hR.integral_prod_left
  have heL (wt : ℝ×ℝ) : finiteVerticalIntegral (fun ξ => K ξ wt) a T = L wt := by
    rw [finiteVerticalIntegral, intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
    rfl
  have heH (wt : ℝ×ℝ) : finiteHorizontalError (fun ξ => K ξ wt) a b T = Complex.I*(B wt-H wt) := by
    rw [finiteHorizontalError, finiteHorizontalIntegral, finiteHorizontalIntegral,
      intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
    rfl
  have heR (wt : ℝ×ℝ) : rightVerticalTail (fun ξ => K ξ wt) b T = R wt := rfl
  simp_rw [heL, heH, heR]
  have hsum : (∫ wt : ℝ×ℝ, L wt+Complex.I*(B wt-H wt)+R wt ∂μwt) =
      (∫ wt : ℝ×ℝ, L wt+Complex.I*(B wt-H wt) ∂μwt)+(∫ wt : ℝ×ℝ, R wt ∂μwt) := by
    simpa only [Pi.add_apply, Pi.sub_apply] using
      integral_add (hL'.add ((hB'.sub hH').const_mul Complex.I)) hR'
  have hinner : (∫ wt : ℝ×ℝ, L wt+Complex.I*(B wt-H wt) ∂μwt) =
      (∫ wt : ℝ×ℝ, L wt ∂μwt)+(∫ wt : ℝ×ℝ, Complex.I*(B wt-H wt) ∂μwt) := by
    simpa only [Pi.add_apply, Pi.sub_apply] using integral_add hL' ((hB'.sub hH').const_mul Complex.I)
  have hsub : (∫ wt : ℝ×ℝ, B wt-H wt ∂μwt) = (∫ wt, B wt ∂μwt)-(∫ wt, H wt ∂μwt) :=
    integral_sub hB' hH'
  rw [hsum, hinner, integral_const_mul, hsub]
  rw [show (∫ wt : ℝ×ℝ, L wt ∂μwt) = _ from (integral_prod _ hL).symm,
    show (∫ wt : ℝ×ℝ, B wt ∂μwt) = _ from (integral_prod _ hB).symm,
    show (∫ wt : ℝ×ℝ, H wt ∂μwt) = _ from (integral_prod _ hH).symm,
    show (∫ wt : ℝ×ℝ, R wt ∂μwt) = _ from (integral_prod _ hR).symm]
  rfl

end
end ArtinMatthews.SourcePhysical

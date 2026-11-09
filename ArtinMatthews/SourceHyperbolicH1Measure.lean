module

public import ArtinMatthews.SourceHyperbolicProductMeasureGreen
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.InnerProductSpace.LinearPMap


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceHyperbolicGreen
open OAI.CubicEisenstein MeasureTheory Filter
open scoped Topology ContDiff BigOperators ENNReal Classical
noncomputable section

variable {ι : Type*} [Fintype ι]

def h1RealDensity (p : ProductSpace ι) : ℝ :=
  ∏ i, ((p i 2)^3)⁻¹

theorem h1RealDensity_continuousOn :
    ContinuousOn (h1RealDensity (ι := ι)) (productUpper ι) := by
  apply continuousOn_finsetProd
  intro i _
  apply ContinuousOn.inv₀
  · fun_prop
  · intro p hp
    exact pow_ne_zero 3 (productUpper_pos hp i).ne'

theorem productDensity_eq_ofReal {p : ProductSpace ι} (hp : p ∈ productUpper ι) :
    productDensity p = ENNReal.ofReal (h1RealDensity p) := by
  unfold productDensity h1RealDensity
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => inv_nonneg.mpr (pow_nonneg (productUpper_pos hp i).le 3))]
  rfl

theorem productVolume_ae_upper : ∀ᵐ p ∂productVolume ι, p ∈ productUpper ι := by
  rw [productVolume_eq_density]
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem (productUpper_isOpen ι).measurableSet)

theorem productVolume_compact_lt_top {s : Set (ProductSpace ι)}
    (hs : IsCompact s) (hsu : s ⊆ productUpper ι) : productVolume ι s < ⊤ := by
  obtain ⟨C,hC⟩ := hs.bddAbove_image (h1RealDensity_continuousOn.mono hsu)
  have he : productVolume ι s = ∫⁻ p in s, productDensity p := by
    rw [productVolume_eq_density, withDensity_apply _ hs.measurableSet,
      Measure.restrict_restrict hs.measurableSet, Set.inter_eq_left.mpr hsu]
  rw [he]
  calc
    _ ≤ ∫⁻ _p in s, ENNReal.ofReal C := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hs.measurableSet] with p hp
      rw [productDensity_eq_ofReal (hsu hp)]
      exact ENNReal.ofReal_le_ofReal (hC ⟨p,hp,rfl⟩)
    _ < ⊤ := by
      rw [lintegral_const, Measure.restrict_apply_univ]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hs.measure_lt_top

theorem h1_compact_memLp {F : Type*} [NormedAddCommGroup F] {f : ProductSpace ι → F}
    (hf : Continuous f) (hc : HasCompactSupport f) (hs : tsupport f ⊆ productUpper ι)
    (p : ℝ≥0∞) : MemLp f p (productVolume ι) := by
  have htop := hf.memLp_top_of_hasCompactSupport hc (productVolume ι)
  exact htop.mono_exponent_of_measure_support_ne_top
    (fun x => image_eq_zero_of_notMem_tsupport)
    (productVolume_compact_lt_top hc hs).ne le_top

theorem h1_memLp_locallyIntegrableOn {F : Type*} [NormedAddCommGroup F]
    {f : ProductSpace ι → F} (hf : MemLp f 2 (productVolume ι)) :
    LocallyIntegrableOn f (productUpper ι) (productVolume ι) := by
  rw [locallyIntegrableOn_iff (productUpper_isOpen ι).isLocallyClosed]
  intro s hsu hs
  let : IsFiniteMeasure ((productVolume ι).restrict s) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using productVolume_compact_lt_top hs hsu⟩
  exact (hf.restrict s).integrable (by norm_num)

end
end ArtinMatthews.SourceHyperbolicGreen

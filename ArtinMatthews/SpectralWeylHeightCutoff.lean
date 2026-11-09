module

public import ArtinMatthews.SpectralWeylPowerIntegrable
public import ArtinMatthews.SpectralHeightAnnularPartition
public import Mathlib.MeasureTheory.Integral.DominatedConvergence


set_option backward.privateInPublic true
@[expose] public section

/-! Literal dyadic height cutoffs pass through the genuine two-height
orbital integral by absolute dominated convergence. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ArtinMatthews

theorem spectralHeightAnnularPartial_continuous (K : ℕ) :
    Continuous (spectralHeightAnnularPartial K) := by
  unfold spectralHeightAnnularPartial
  apply continuous_finsetSum
  intro k _
  exact (spectralHeightAnnularBlock_contDiff _).continuous.add
    (spectralHeightAnnularBlock_contDiff _).continuous

def spectralWeylProfileCutoff (a : ℝ) (K : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (spectralHeightAnnularPartial K (a*x) : ℂ)*f x

theorem spectralWeylProfileCutoff_measurable (a : ℝ) (K : ℕ) (f : ℝ → ℂ)
    (hf : Measurable f) : Measurable (spectralWeylProfileCutoff a K f) :=
  ((Complex.continuous_ofReal.comp ((spectralHeightAnnularPartial_continuous K).comp
    (by fun_prop))).measurable).mul hf

theorem spectralWeylProfileCutoff_norm_le (a : ℝ) (K : ℕ) (f : ℝ → ℂ) (x : ℝ) :
    ‖spectralWeylProfileCutoff a K f x‖ ≤ ‖f x‖ := by
  rw [spectralWeylProfileCutoff,norm_mul,Complex.norm_real,Real.norm_of_nonneg
    (spectralHeightAnnularPartial_bounds K (a*x)).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (spectralHeightAnnularPartial_bounds K (a*x)).2

theorem spectralWeylFoldDensity_cutoff (a : ℝ) (K : ℕ) (s t X : ℝ)
    (f g : ℝ → ℂ) (q : ℝ × ℝ) :
    spectralWeylFoldDensity s t (spectralWeylProfileCutoff a K f) g X q =
      (spectralHeightAnnularPartial K
        (a*spectralWeylFoldHeight (X^2/(4*q.1)) q.2) : ℂ)*
        spectralWeylFoldDensity s t f g X q := by
  unfold spectralWeylFoldDensity spectralWeylProfileCutoff
  ring

theorem spectralWeylFoldDensity_cutoff_norm_le (a : ℝ) (K : ℕ) (s t X : ℝ)
    (f g : ℝ → ℂ) (q : ℝ × ℝ) :
    ‖spectralWeylFoldDensity s t (spectralWeylProfileCutoff a K f) g X q‖ ≤
      ‖spectralWeylFoldDensity s t f g X q‖ := by
  rw [spectralWeylFoldDensity_cutoff,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg (spectralHeightAnnularPartial_bounds _ _).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (spectralHeightAnnularPartial_bounds _ _).2

theorem spectralWeylFoldDensity_cutoff_tendsto {a X x u : ℝ} (ha : 0 < a)
    (hX : 0 < X) (hx : 0 < x) (hu : u ∈ Ioo (0 : ℝ) 1)
    (s t : ℝ) (f g : ℝ → ℂ) :
    Tendsto (fun K : ℕ => spectralWeylFoldDensity s t (spectralWeylProfileCutoff a K f) g X (x,u))
      atTop (𝓝 (spectralWeylFoldDensity s t f g X (x,u))) := by
  have hw : 0 < 1-u^2 := by
    nlinarith [mul_pos (sub_pos.mpr hu.2) (show 0 < 1+u by linarith [hu.1])]
  have hz : 0 < a*spectralWeylFoldHeight (X^2/(4*x)) u := by
    unfold spectralWeylFoldHeight
    positivity
  apply tendsto_const_nhds.congr'
  filter_upwards [spectralHeightAnnularPartial_eventually_one hz] with K hK
  rw [spectralWeylFoldDensity_cutoff,hK,Complex.ofReal_one,one_mul]

theorem spectralWeylFoldBilinear_cutoff_tendsto {a X B M : ℝ}
    (ha : 0 < a) (hX : 0 < X) (hB : 0 < B) (hB₁ : B ≤ 1) (hM : 0 ≤ M)
    (s t : ℝ) (f g : ℝ → ℂ) (hfm : Measurable f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ))
    (hf : ∀ z, 0 < z → ‖f z‖ ≤ M*z^B) :
    Tendsto (fun K : ℕ => spectralWeylFoldBilinear s t (spectralWeylProfileCutoff a K f) g X)
      atTop (𝓝 (spectralWeylFoldBilinear s t f g X)) := by
  have hi := spectralWeylFoldDensity_power_integrable hX hB hB₁ hM s t f g hfm hg hgc hgp hf
  apply tendsto_integral_of_dominated_convergence (fun q => ‖spectralWeylFoldDensity s t f g X q‖)
  · intro K
    exact (spectralWeylFoldDensity_measurable s t X _ g
      (spectralWeylProfileCutoff_measurable a K f hfm) hg.measurable).aestronglyMeasurable
  · exact hi.norm
  · intro K
    exact Eventually.of_forall (spectralWeylFoldDensity_cutoff_norm_le a K s t X f g)
  · have hp : ∀ᵐ q ∂spectralWeylFoldMeasure, 0 < q.1 ∧ q.2 ∈ Ioo (0 : ℝ) 1 := by
      unfold spectralWeylFoldMeasure
      apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
      filter_upwards [spectralKLPositiveWeightMeasure_ae_pos (fun x => x⁻¹)] with x hx
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      exact ⟨hx,hu⟩
    filter_upwards [hp] with q hq
    exact spectralWeylFoldDensity_cutoff_tendsto ha hX hq.1 hq.2 s t f g

theorem spectralWeylPhysicalBilinear_cutoff_tendsto {a X B M : ℝ}
    (ha : 0 < a) (hX : 0 < X) (hB : 0 < B) (hB₁ : B ≤ 1) (hM : 0 ≤ M)
    (s t : ℝ) (f g : ℝ → ℂ) (hfm : Measurable f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ))
    (hf : ∀ z, 0 < z → ‖f z‖ ≤ M*z^B) :
    Tendsto (fun K : ℕ => spectralWeylPhysicalBilinear s t (spectralWeylProfileCutoff a K f) g X)
      atTop (𝓝 (spectralWeylPhysicalBilinear s t f g X)) := by
  have hF := spectralWeylPhysicalBilinear_fold hX s t f g hfm hg.measurable
    (spectralWeylFoldDensity_power_integrable hX hB hB₁ hM s t f g hfm hg hgc hgp hf)
  have hK (K : ℕ) : spectralWeylPhysicalBilinear s t (spectralWeylProfileCutoff a K f) g X =
      spectralWeylFoldBilinear s t (spectralWeylProfileCutoff a K f) g X :=
    spectralWeylPhysicalBilinear_fold hX s t _ g (spectralWeylProfileCutoff_measurable a K f hfm) hg.measurable
      (spectralWeylFoldDensity_power_integrable hX hB hB₁ hM s t _ g
        (spectralWeylProfileCutoff_measurable a K f hfm) hg hgc hgp
        (fun z hz => (spectralWeylProfileCutoff_norm_le a K f z).trans (hf z hz)))
  rw [hF]
  convert spectralWeylFoldBilinear_cutoff_tendsto ha hX hB hB₁ hM s t f g hfm hg hgc hgp hf using 1
  funext K
  exact hK K

end ArtinMatthews

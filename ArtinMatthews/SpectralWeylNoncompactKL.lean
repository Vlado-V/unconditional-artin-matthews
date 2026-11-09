module

public import ArtinMatthews.SpectralKLCutoffCalibration
public import ArtinMatthews.SpectralKLBoundedPairing
public import ArtinMatthews.SpectralWeylUnregularized


set_option backward.privateInPublic true
@[expose] public section

/-! The actual noncompact two-height J/K identity follows from the same
literal compact cutoffs on both sides and uniqueness of their limits. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ArtinMatthews

theorem spectralWeylPhysicalBilinear_same_J_noncompact {a X B M : ℝ}
    (ha : 0 < a) (hX : 0 < X) (hB : 0 < B) (hB₁ : B ≤ 1) (hM : 0 ≤ M)
    (s t : ℝ) (hs : s^2 = 1) (ht : t^2 = 1) (hst : s*t = 1)
    (f g : ℝ → ℂ) (hfm : Measurable f) (hfc : ContinuousOn f (Ioi (0 : ℝ)))
    (hfL : MemLp f 2 spectralKLPhysicalMeasure)
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ))
    (hf : ∀ z, 0 < z → ‖f z‖ ≤ M*z^B) :
    spectralWeylPhysicalBilinear s t f g X =
      ∫ r, spectralWeylJMultiplier r X*(spectralKLAnalysis (hfL.toLp f)) r*
        star ((spectralKLAnalysis ((spectralKLPhysical_compact_memLp g hg hgc hgp).toLp g)) r)
          ∂spectralKLSpectralMeasure := by
  let G := spectralKLAnalysis ((spectralKLPhysical_compact_memLp g hg hgc hgp).toLp g)
  let F (K : ℕ) := spectralKLAnalysis (spectralWeylCutoffLp a K (hfL.toLp f))
  have hstep (K : ℕ) : spectralWeylPhysicalBilinear s t (spectralWeylProfileCutoff a K f) g X =
      ∫ r, spectralWeylJMultiplier r X*F K r*star (G r) ∂spectralKLSpectralMeasure := by
    rw [spectralWeylPhysicalBilinear_same_J hX s t hs ht hst _ g
      (spectralWeylProfileCutoff_continuous ha K f hfc)
      (spectralWeylProfileCutoff_compact ha K f)
      (spectralWeylProfileCutoff_positive ha K f) hg hgc hgp]
    apply integral_congr_ae
    filter_upwards [spectralKLAnalysis_height_cutoff_ae ha K f hfc hfL,
      spectralKLAnalysis_compact_ae g hg hgc hgp] with r hr hgr
    change _ = spectralWeylJMultiplier r X*
      (spectralKLAnalysis (spectralWeylCutoffLp a K (hfL.toLp f))) r*
        star ((spectralKLAnalysis ((spectralKLPhysical_compact_memLp g hg hgc hgp).toLp g)) r)
    rw [hr,hgr]
  have hleft := spectralWeylPhysicalBilinear_cutoff_tendsto ha hX hB hB₁ hM s t f g hfm hg hgc hgp hf
  have heq : (fun K => spectralWeylPhysicalBilinear s t (spectralWeylProfileCutoff a K f) g X) =
      (fun K => ∫ r, spectralWeylJMultiplier r X*F K r*star (G r) ∂spectralKLSpectralMeasure) := funext hstep
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft (spectralWeylJ_pair_tendsto hX F (spectralKLAnalysis (hfL.toLp f)) G
    (spectralKLAnalysis_cutoff_tendsto ha (hfL.toLp f)))

theorem spectralWeylPhysicalBilinear_opposite_K_noncompact {a X B M : ℝ}
    (ha : 0 < a) (hX : 0 < X) (hB : 0 < B) (hB₁ : B ≤ 1) (hM : 0 ≤ M)
    (s t : ℝ) (hs : s^2 = 1) (ht : t^2 = 1) (hst : s*t = -1)
    (f g : ℝ → ℂ) (hfm : Measurable f) (hfc : ContinuousOn f (Ioi (0 : ℝ)))
    (hfL : MemLp f 2 spectralKLPhysicalMeasure)
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ))
    (hf : ∀ z, 0 < z → ‖f z‖ ≤ M*z^B) :
    spectralWeylPhysicalBilinear s t f g X =
      ∫ r, spectralWeylKMultiplier r X*(spectralKLAnalysis (hfL.toLp f)) r*
        star ((spectralKLAnalysis ((spectralKLPhysical_compact_memLp g hg hgc hgp).toLp g)) r)
          ∂spectralKLSpectralMeasure := by
  let G := spectralKLAnalysis ((spectralKLPhysical_compact_memLp g hg hgc hgp).toLp g)
  let F (K : ℕ) := spectralKLAnalysis (spectralWeylCutoffLp a K (hfL.toLp f))
  have hstep (K : ℕ) : spectralWeylPhysicalBilinear s t (spectralWeylProfileCutoff a K f) g X =
      ∫ r, spectralWeylKMultiplier r X*F K r*star (G r) ∂spectralKLSpectralMeasure := by
    rw [spectralWeylPhysicalBilinear_opposite_K hX s t hs ht hst _ g
      (spectralWeylProfileCutoff_continuous ha K f hfc)
      (spectralWeylProfileCutoff_compact ha K f)
      (spectralWeylProfileCutoff_positive ha K f) hg hgc hgp]
    apply integral_congr_ae
    filter_upwards [spectralKLAnalysis_height_cutoff_ae ha K f hfc hfL,
      spectralKLAnalysis_compact_ae g hg hgc hgp] with r hr hgr
    change _ = spectralWeylKMultiplier r X*
      (spectralKLAnalysis (spectralWeylCutoffLp a K (hfL.toLp f))) r*
        star ((spectralKLAnalysis ((spectralKLPhysical_compact_memLp g hg hgc hgp).toLp g)) r)
    rw [hr,hgr]
  have hleft := spectralWeylPhysicalBilinear_cutoff_tendsto ha hX hB hB₁ hM s t f g hfm hg hgc hgp hf
  have heq : (fun K => spectralWeylPhysicalBilinear s t (spectralWeylProfileCutoff a K f) g X) =
      (fun K => ∫ r, spectralWeylKMultiplier r X*F K r*star (G r) ∂spectralKLSpectralMeasure) := funext hstep
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft (spectralWeylK_pair_tendsto hX F (spectralKLAnalysis (hfL.toLp f)) G
    (spectralKLAnalysis_cutoff_tendsto ha (hfL.toLp f)))

end ArtinMatthews

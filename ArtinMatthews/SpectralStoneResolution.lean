module

public import ArtinMatthews.SpectralStoneContinuousMeasure
public import ArtinMatthews.SpectralAmbientSpectralAtoms
public import Mathlib.MeasureTheory.Measure.Dirac.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Exact scalar resolution of the genuine compact forcing spectral
measure into its actual continuous density and all discrete eigenspace
atoms, including threshold and residual energies. -/
noncomputable section
open Set Filter MeasureTheory Function
open scoped ENNReal
namespace ArtinMatthews

def gamma0StoneDiscreteEnergies (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) : Set ℝ :=
  (gamma0StoneGoodEnergy N ψ Y)ᶜ∩Ici 0

theorem gamma0StoneDiscreteEnergies_countable (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) : (gamma0StoneDiscreteEnergies N ψ Y).Countable :=
  (gamma0StoneGoodEnergy_compl_countable N ψ Y).mono inter_subset_left

theorem gamma0AmbientSpectralMeasure_restrict_discrete (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (Y : Gamma0CompactResolventCutoff N ψ) :
    (gamma0AmbientSpectralMeasure N (gamma0SmoothSeedMass N ψ)).restrict (gamma0StoneGoodEnergy N ψ Y)ᶜ=
      Measure.sum (fun l : gamma0StoneDiscreteEnergies N ψ Y =>
        ENNReal.ofReal (‖gamma0AmbientSpectralAtomVector N (gamma0SmoothSeedMass N ψ) (l:ℝ)‖^2) •
          Measure.dirac (l:ℝ)) := by
  let F := gamma0SmoothSeedMass N ψ
  let μ := gamma0AmbientSpectralMeasure N F
  let U := gamma0StoneGoodEnergy N ψ Y
  let D := gamma0StoneDiscreteEnergies N ψ Y
  let _ : Countable D := (gamma0StoneDiscreteEnergies_countable N ψ Y).to_subtype
  have hAE : Uᶜ =ᵐ[μ] D := by
    filter_upwards [gamma0AmbientSpectralMeasure_ae_nonneg N F] with x hx
    change (x∈Uᶜ)=(x∈Uᶜ∩Ici 0)
    simp only [mem_inter_iff,mem_Ici,hx,and_true]
  have hD : (⋃ l : D,{(l:ℝ)})=D := by
    ext l
    constructor
    · intro hl
      obtain ⟨x,hx⟩ := mem_iUnion.mp hl
      rw [mem_singleton_iff] at hx
      exact hx ▸ x.property
    · intro hl
      exact mem_iUnion.mpr ⟨⟨l,hl⟩,rfl⟩
  have hPair : Pairwise (Disjoint on (fun l : D => ({(l:ℝ)}:Set ℝ))) := by
    intro l k h
    exact disjoint_singleton_right.mpr (by
      intro he
      exact h (Subtype.ext (mem_singleton_iff.mp he).symm))
  rw [Measure.restrict_congr_set hAE,← hD,
    Measure.restrict_iUnion hPair (fun l => measurableSet_singleton (l:ℝ))]
  congr 1
  funext l
  have hl : 0≤(l:ℝ) := l.property.2
  rw [Measure.restrict_singleton,gamma0AmbientSpectralMeasure_atom N F l hl]

theorem gamma0AmbientSpectralMeasure_resolved (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (Y : Gamma0CompactResolventCutoff N ψ) :
    gamma0AmbientSpectralMeasure N (gamma0SmoothSeedMass N ψ)=
      gamma0StoneContinuousMeasure N ψ Y+
      Measure.sum (fun l : gamma0StoneDiscreteEnergies N ψ Y =>
        ENNReal.ofReal (‖gamma0AmbientSpectralAtomVector N (gamma0SmoothSeedMass N ψ) (l:ℝ)‖^2) •
          Measure.dirac (l:ℝ)) := by
  have hU := (gamma0StoneGoodEnergy_open N ψ Y).measurableSet
  rw [← Measure.restrict_add_restrict_compl (μ:=gamma0AmbientSpectralMeasure N
      (gamma0SmoothSeedMass N ψ)) hU,
    gamma0AmbientSpectralMeasure_restrict_good N ψ Y,gamma0AmbientSpectralMeasure_restrict_discrete N ψ Y]

end ArtinMatthews

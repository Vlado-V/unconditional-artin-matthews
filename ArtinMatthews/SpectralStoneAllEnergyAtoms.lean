module

public import ArtinMatthews.SpectralStoneCompactPlancherel
public import ArtinMatthews.SpectralAmbientEnergyEigenspace


set_option backward.privateInPublic true
@[expose] public section

/-! The compact identity is indexed by actual energy, independently of
the auxiliary regularity cutoff used in its proof. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace ArtinMatthews

theorem gamma0CompactStoneAtom_zero_of_good (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) (l : ℝ) (hl : 0≤l) (hg : l∈gamma0StoneGoodEnergy N ψ Y) :
    gamma0AmbientSpectralAtomVector N (gamma0SmoothSeedMass N ψ) l=0 := by
  let μ := gamma0AmbientSpectralMeasure N (gamma0SmoothSeedMass N ψ)
  have hset : {l}∩gamma0StoneGoodEnergy N ψ Y=({l}:Set ℝ) :=
    inter_eq_left.mpr (singleton_subset_iff.mpr hg)
  have he : μ {l}=gamma0StoneContinuousMeasure N ψ Y {l} := by
    rw [← gamma0AmbientSpectralMeasure_restrict_good N ψ Y,
      Measure.restrict_apply (measurableSet_singleton l),hset]
  rw [gamma0AmbientSpectralMeasure_atom N (gamma0SmoothSeedMass N ψ) l hl,
    gamma0StoneContinuousMeasure_absolutelyContinuous N ψ Y (measure_singleton l)] at he
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp
    (le_antisymm (ENNReal.ofReal_eq_zero.mp he) (sq_nonneg _)))

theorem gamma0AmbientAtomNormSq_summable (N : ℕ) [NeZero N] (u : Gamma0RegionL2 N) :
    Summable (fun l : Ici (0:ℝ) => ‖gamma0AmbientSpectralAtomVector N u (l:ℝ)‖^2) := by
  let μ := gamma0AmbientSpectralMeasure N u
  let _ : IsFiniteMeasure μ :=
    ⟨by rw [show μ=gamma0AmbientSpectralMeasure N u from rfl,gamma0AmbientSpectralMeasure_univ];
        exact ENNReal.ofReal_lt_top⟩
  apply summable_of_sum_le (c:=‖u‖^2) (fun l => sq_nonneg _)
  intro s
  have hs : (↑s : Set (Ici (0:ℝ))).PairwiseDisjoint (fun l => ({(l:ℝ)}:Set ℝ)) := by
    intro a _ b _ h
    exact disjoint_singleton_right.mpr (fun he => h (Subtype.ext (mem_singleton_iff.mp he).symm))
  have h := sum_measureReal_le_measureReal_univ (μ:=μ) (s:=s)
    (fun l _ => measurableSet_singleton (l:ℝ)) hs
  have hnorm (l : Ici (0:ℝ)) : μ.real {l.val}=‖gamma0AmbientSpectralAtomVector N u (l:ℝ)‖^2 := by
    rw [measureReal_def,show μ=gamma0AmbientSpectralMeasure N u from rfl,
      gamma0AmbientSpectralMeasure_atom N u l l.property,ENNReal.toReal_ofReal (sq_nonneg _)]
  have htotal : μ.real univ=‖u‖^2 := by
    rw [measureReal_def,show μ=gamma0AmbientSpectralMeasure N u from rfl,
      gamma0AmbientSpectralMeasure_univ,ENNReal.toReal_ofReal (sq_nonneg _)]
  simpa only [hnorm,htotal] using h

theorem gamma0CompactStonePlancherel_all_atoms (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) :
    ‖gamma0SmoothSeedMass N ψ‖^2=
      (∫ t in Ioi 0,gamma0StoneFrequencyDensity N ψ t)+
      ∑' l : Ici (0:ℝ),‖gamma0AmbientSpectralAtomVector N (gamma0SmoothSeedMass N ψ) (l:ℝ)‖^2 := by
  let Y := gamma0CompactResolventCutoff N ψ
  let F := gamma0SmoothSeedMass N ψ
  let D := gamma0StoneDiscreteEnergies N ψ Y
  let U := gamma0StoneGoodEnergy N ψ Y
  let S : Set (Ici (0:ℝ)) := {l | (l:ℝ)∉U}
  let e : D ≃ S :=
    { toFun := fun l => ⟨⟨l.val,l.property.2⟩,l.property.1⟩
      invFun := fun l => ⟨l.val.val,⟨l.property,l.val.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [gamma0CompactStonePlancherel N ψ Y]
  congr 1
  let f : Ici (0:ℝ) → ℝ := fun l => ‖gamma0AmbientSpectralAtomVector N F (l:ℝ)‖^2
  calc
    _ = ∑' l : S,‖gamma0AmbientSpectralAtomVector N F (l.val:ℝ)‖^2 := e.tsum_eq _
    _ = ∑' l : Ici (0:ℝ),S.indicator f l := tsum_subtype S f
    _ = _ := by
      apply tsum_congr
      intro l
      by_cases hl : l∈S
      · exact indicator_of_mem hl _
      · have hg : (l:ℝ)∈U := by
          by_contra h
          exact hl h
        rw [indicator_of_notMem hl]
        change 0=‖gamma0AmbientSpectralAtomVector N F (l:ℝ)‖^2
        rw [gamma0CompactStoneAtom_zero_of_good N ψ Y l l.property hg,norm_zero,zero_pow (by decide)]

end ArtinMatthews

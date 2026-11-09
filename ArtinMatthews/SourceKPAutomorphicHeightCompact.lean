module

public import ArtinMatthews.SourceKPHeightBandCompact
public import ArtinMatthews.SourceAdelicOrbitHeightTopology
public import ArtinMatthews.SourceKPAdelicHeightReduction


set_option backward.privateInPublic true
@[expose] public section

/-! Compact sublevels of the actual rational-orbit height. Every geometric
input is supplied by the checked actual adelic constructions. -/

namespace ArtinMatthews
open NumberField Matrix Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAutomorphicOrbitHeight_sublevel_isCompact (T : ℝ) :
    IsCompact {x : SourceKPAutomorphicLevel K hζ | sourceKPAutomorphicOrbitHeight K hζ x ≤ T} := by
  obtain ⟨c,hc,hreduce⟩ := sourceKPAdelicCover_rational_height_lower K hζ
  let v₀ : InfinitePlace K := Classical.choice inferInstance
  apply (sourceKPHeightBand_automorphic_container_isCompact K hζ v₀ (Real.log c) (Real.log T)).of_isClosed_subset
    (sourceKPAutomorphicOrbitHeight_sublevel_closed K hζ T)
  intro x hx
  obtain ⟨q,rfl⟩ := sourceKPAutomorphicLevelMk_surjective K hζ x
  change sourceKPAdelicOrbitHeight K hζ q ≤ T at hx
  obtain ⟨γ,hγ⟩ := hreduce q
  let r := sourceKPAdelicProjectiveRationalLift K hζ γ*q
  have hupper : sourceKPAdelicCoverHeight K hζ r ≤ T :=
    (sourceKPAdelicCoverHeight_le_orbit K hζ r).trans (by
      simpa only [r,sourceKPAdelicOrbitHeight_rational] using hx)
  obtain ⟨g,hg⟩ := ProjGenLinGroup.mk_surjective (sourceKPAdelicProjectiveProjection K hζ r)
  have hheight : sourceKPAdelicHeight K hζ g = sourceKPAdelicCoverHeight K hζ r := by
    unfold sourceKPAdelicCoverHeight
    rw [← hg,sourceKPAdelicHeightOnProjective_mk]
  have hband : Real.log (sourceKPAdelicHeight K hζ g) ∈ Set.Icc (Real.log c) (Real.log T) := by
    rw [hheight]
    exact ⟨Real.log_le_log hc hγ,
      Real.log_le_log (sourceKPAdelicCoverHeight_pos K hζ r) hupper⟩
  have hm := sourceKPHeightBand_cover_reduction K hζ v₀ (Real.log c) (Real.log T) r g hg.symm hband
  simpa only [r,sourceKPAutomorphicLevelMk_rational] using hm

theorem sourceKPAutomorphicOrbitHeight_uniform_pos :
    ∃ c : ℝ, 0 < c ∧ ∀ x : SourceKPAutomorphicLevel K hζ,
      c ≤ sourceKPAutomorphicOrbitHeight K hζ x := by
  obtain ⟨c,hc,h⟩ := sourceKPAdelicOrbitHeight_uniform_pos K hζ
  refine ⟨c,hc,fun x => ?_⟩
  obtain ⟨q,rfl⟩ := sourceKPAutomorphicLevelMk_surjective K hζ x
  exact h q

theorem sourceKPAutomorphicOrbitHeight_exhaustion_covers :
    (⋃ n : ℕ, {x : SourceKPAutomorphicLevel K hζ |
      sourceKPAutomorphicOrbitHeight K hζ x ≤ (n : ℝ)}) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨n,hn⟩ := exists_nat_gt (sourceKPAutomorphicOrbitHeight K hζ x)
  exact Set.mem_iUnion.mpr ⟨n,hn.le⟩

end
end ArtinMatthews

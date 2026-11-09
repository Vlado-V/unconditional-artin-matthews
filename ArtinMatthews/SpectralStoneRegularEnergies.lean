module

public import ArtinMatthews.SpectralCompactResolventBoundary
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Topology.Compactness.Lindelof


set_option backward.privateInPublic true
@[expose] public section

/-! Regular real energies form a genuine open codiscrete set. Every
compact interval contains only finitely many excluded energies. -/
noncomputable section
open Set Filter Topology
namespace ArtinMatthews

theorem spectralContinuous_injective_tendsto_punctured {X Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Z] (f : X → Z) (hc : Continuous f)
    (hi : Function.Injective f) (x : X) :
    Tendsto f (𝓝[≠] x) (𝓝[≠] f x) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨hc.continuousAt.mono_left nhdsWithin_le_nhds,?_⟩
  filter_upwards [(self_mem_nhdsWithin : ({x}:Set X)ᶜ∈𝓝[≠] x)] with y hy
  intro h
  exact hy (mem_singleton_iff.mpr (hi (mem_singleton_iff.mp h)))

theorem spectralStoneUpperParameter_boundary_continuous :
    Continuous (fun x : ℝ => spectralStoneUpperParameter x 0) := by
  have h : Continuous (fun x : ℝ => (x,(0:ℝ))) := continuous_id.prodMk continuous_const
  exact spectralStoneUpperParameter_continuous.comp (f:=fun x : ℝ => (x,(0:ℝ))) h

theorem spectralStoneLowerParameter_boundary_continuous :
    Continuous (fun x : ℝ => spectralStoneLowerParameter x 0) :=
  Complex.continuous_conj.comp (f:=fun x : ℝ => spectralStoneUpperParameter x 0)
    spectralStoneUpperParameter_boundary_continuous

theorem spectralStoneUpperParameter_boundary_injective :
    Function.Injective (fun x : ℝ => spectralStoneUpperParameter x 0) := by
  intro x y h
  have he := congrArg (fun s : ℂ => s*(1-s)) h
  have hu (u : ℝ) : spectralStoneUpperParameter u 0*(1-spectralStoneUpperParameter u 0)=(u:ℂ) := by
    rw [spectralStoneUpperParameter_energy u 0 le_rfl]
    simp [spectralEnergyShift]
  change spectralStoneUpperParameter x 0*(1-spectralStoneUpperParameter x 0)=
    spectralStoneUpperParameter y 0*(1-spectralStoneUpperParameter y 0) at he
  rw [hu x,hu y] at he
  exact Complex.ofReal_injective he

theorem spectralStoneLowerParameter_boundary_injective :
    Function.Injective (fun x : ℝ => spectralStoneLowerParameter x 0) := by
  intro x y h
  apply spectralStoneUpperParameter_boundary_injective
  have he := congrArg (starRingEnd ℂ) h
  simpa only [spectralStoneLowerParameter,starRingEnd_self_apply] using he

def gamma0StoneGoodEnergy (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) : Set ℝ :=
  {x | x≠1/4 ∧
    gamma0HeightMatchingRegular N Y.height Y.pos (spectralStoneUpperParameter x 0) ∧
    gamma0HeightMatchingRegular N Y.height Y.pos (spectralStoneLowerParameter x 0) ∧
    gamma0EisensteinMatchingRegular N (spectralStoneLowerParameter x 0)}

theorem gamma0StoneGoodEnergy_eventually (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) (x : ℝ) :
    ∀ᶠ y in 𝓝[≠] x,y∈gamma0StoneGoodEnergy N ψ Y := by
  have hu := spectralContinuous_injective_tendsto_punctured (fun y => spectralStoneUpperParameter y 0)
    spectralStoneUpperParameter_boundary_continuous spectralStoneUpperParameter_boundary_injective x
  have hl := spectralContinuous_injective_tendsto_punctured (fun y => spectralStoneLowerParameter y 0)
    spectralStoneLowerParameter_boundary_continuous spectralStoneLowerParameter_boundary_injective x
  have hn : ∀ᶠ y in 𝓝[≠] x,y≠(1/4:ℝ) := by
    by_cases hx : x=(1/4:ℝ)
    · subst x
      exact self_mem_nhdsWithin
    · exact nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds
        (show x∈({(1/4:ℝ)}:Set ℝ)ᶜ from hx))
  filter_upwards [hn,hu.eventually (gamma0HeightMatchingRegular_eventually N Y.height Y.pos Y.matching_le _),
    hl.eventually (gamma0HeightMatchingRegular_eventually N Y.height Y.pos Y.matching_le _),
    hl.eventually (gamma0EisensteinMatchingRegular_eventually N _)] with y hy hu hl hr
  exact ⟨hy,hu,hl,hr⟩

theorem gamma0StoneGoodEnergy_mem_codiscrete (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) :
    gamma0StoneGoodEnergy N ψ Y∈Filter.codiscrete ℝ :=
  mem_codiscrete_iff_forall_mem_nhdsNE.mpr (gamma0StoneGoodEnergy_eventually N ψ Y)

theorem gamma0StoneGoodEnergy_open (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) : IsOpen (gamma0StoneGoodEnergy N ψ Y) :=
  (mem_codiscrete'.mp (gamma0StoneGoodEnergy_mem_codiscrete N ψ Y)).1

theorem gamma0StoneGoodEnergy_compl_countable (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) : (gamma0StoneGoodEnergy N ψ Y)ᶜ.Countable := by
  have hL : IsLindelof (gamma0StoneGoodEnergy N ψ Y)ᶜ := isLindelof_iff_lindelofSpace.mpr inferInstance
  exact hL.countable_of_isDiscrete (mem_codiscrete'.mp (gamma0StoneGoodEnergy_mem_codiscrete N ψ Y)).2

theorem gamma0StoneGoodEnergy_finite_compl_on_compact (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) {K : Set ℝ} (hK : IsCompact K) :
    (K\gamma0StoneGoodEnergy N ψ Y).Finite := by
  apply hK.finite_sdiff_of_mem_codiscreteWithin
  apply mem_codiscreteWithin_iff_forall_mem_nhdsNE.mpr
  intro x _
  exact Filter.mem_of_superset (gamma0StoneGoodEnergy_eventually N ψ Y x) (subset_union_left)

end ArtinMatthews

module

public import ArtinMatthews.SourceAdelicOrbitHeightTopology
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Set Filter
open scoped NumberField Topology Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAutomorphic_compact_height_margin (T : ℝ)
    {s : Set (SourceKPAutomorphicLevel K hζ)} (hs : IsCompact s)
    (hhigh : ∀ x ∈ s, T < sourceKPAutomorphicOrbitHeight K hζ x) :
    ∃ m : ℝ, T < m ∧ ∀ x ∈ s, m ≤ sourceKPAutomorphicOrbitHeight K hζ x := by
  by_cases hn : s.Nonempty
  · obtain ⟨a, ha, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hn hs
      ((sourceKPAutomorphicOrbitHeight_lowerSemicontinuous K hζ).lowerSemicontinuousOn s)
    exact ⟨sourceKPAutomorphicOrbitHeight K hζ a, hhigh a ha, fun x hx => hmin hx⟩
  · refine ⟨T+1, by linarith, ?_⟩
    intro x hx
    exact False.elim (hn ⟨x, hx⟩)

theorem sourceKPAutomorphic_tsupport_height_margin (T : ℝ)
    {f : SourceKPAutomorphicLevel K hζ → ℂ} (hc : HasCompactSupport f)
    (hsupp : tsupport f ⊆ {x | T < sourceKPAutomorphicOrbitHeight K hζ x}) :
    ∃ m : ℝ, T < m ∧ ∀ x ∈ tsupport f, m ≤ sourceKPAutomorphicOrbitHeight K hζ x :=
  sourceKPAutomorphic_compact_height_margin K hζ T hc (fun _ hx => hsupp hx)

theorem sourceKPAutomorphic_radial_threshold_support (T : ℝ)
    {f : SourceKPAutomorphicLevel K hζ → ℂ} (hc : HasCompactSupport f)
    (hsupp : tsupport f ⊆ {x | T < sourceKPAutomorphicOrbitHeight K hζ x}) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ x ∈ tsupport f,
      Real.exp (2 * (InfinitePlace.nrComplexPlaces K : ℝ) * t) * T <
        sourceKPAutomorphicOrbitHeight K hζ x := by
  obtain ⟨m, hm, hbound⟩ := sourceKPAutomorphic_tsupport_height_margin K hζ T hc hsupp
  have hlim : Tendsto (fun t : ℝ => Real.exp (2 * (InfinitePlace.nrComplexPlaces K : ℝ) * t) * T)
      (𝓝 0) (𝓝 T) := by
    have hh : Continuous (fun t : ℝ => Real.exp (2 * (InfinitePlace.nrComplexPlaces K : ℝ) * t) * T) := by
      fun_prop
    simpa only [mul_zero, Real.exp_zero, one_mul] using hh.continuousAt.tendsto (x := (0 : ℝ))
  filter_upwards [hlim.eventually (eventually_lt_nhds hm)] with t ht
  intro x hx
  exact ht.trans_le (hbound x hx)

end
end ArtinMatthews

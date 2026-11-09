module

public import ArtinMatthews.SourceExteriorCompactMargin


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Set Filter
open scoped NumberField Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAutomorphic_radial_threshold_window (T : ℝ) (hT : 1 < T)
    {f : SourceKPAutomorphicLevel K hζ → ℂ} (hc : HasCompactSupport f)
    (hsupp : tsupport f ⊆ {x | T < sourceKPAutomorphicOrbitHeight K hζ x}) :
    ∀ᶠ t : ℝ in 𝓝 0,
      1 < Real.exp (2 * (InfinitePlace.nrComplexPlaces K : ℝ) * t) * T ∧
      tsupport f ⊆ {x | Real.exp (2 * (InfinitePlace.nrComplexPlaces K : ℝ) * t) * T <
        sourceKPAutomorphicOrbitHeight K hζ x} := by
  have hlim : Tendsto (fun t : ℝ => Real.exp (2 * (InfinitePlace.nrComplexPlaces K : ℝ) * t) * T)
      (𝓝 0) (𝓝 T) := by
    have hh : Continuous (fun t : ℝ => Real.exp (2 * (InfinitePlace.nrComplexPlaces K : ℝ) * t) * T) := by
      fun_prop
    simpa only [mul_zero, Real.exp_zero, one_mul] using hh.continuousAt.tendsto (x := (0 : ℝ))
  filter_upwards [hlim.eventually (eventually_gt_nhds hT),
    sourceKPAutomorphic_radial_threshold_support K hζ T hc hsupp] with t ht hs
  exact ⟨ht, fun x hx => hs x hx⟩

end
end ArtinMatthews

module

public import ArtinMatthews.SourceFiniteIntertwinerEuler


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open NumberField IsDedekindDomain MeasureTheory StandardAdelic
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPFiniteCoordinateIntertwiningKernel_one (s : ℂ)
    (g : SourceKPFiniteAdeleProjective K hζ) (x : 𝔸ᶠ[K]) :
    sourceKPFiniteCoordinateIntertwiningKernel K hζ s g 1 x =
      sourceKPFiniteIntertwiningKernel K hζ s g x := by
  simp only [sourceKPFiniteCoordinateIntertwiningKernel,
    sourceKPFiniteIntertwiningKernel, one_mul]

theorem sourceKPFiniteCoordinateIntertwiner_one (s : ℂ)
    (g : SourceKPFiniteAdeleProjective K hζ) :
    sourceKPFiniteCoordinateIntertwiner K hζ s g 1 =
      sourceKPFiniteIntertwiner K hζ s g := by
  simp only [sourceKPFiniteCoordinateIntertwiner, sourceKPFiniteIntertwiner,
    sourceKPFiniteCoordinateIntertwiningKernel_one]

theorem sourceKPAdelicTraceIntertwiner_eq_euler
    (g : SourceKPAdelicProjective K hζ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      S₀ ⊆ S ∧ sourceHilbertSet K ∅ ⊆ S ∧ traceBadPlaces K ⊆ S ∧
      ∀ (s : ℂ), ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1 →
        sourceKPAdelicTraceIntertwiner K hζ s g =
          (((Real.pi : ℂ) / s) ^ Fintype.card (InfinitePlace K) *
            sourceArchSphericalProduct K hζ (-s) g.1) *
          (sourceKPExteriorScattering S s *
            sourceKPFiniteWindowIntegral K (sourceKPFiniteIntertwiningKernel K hζ s g.2) S) := by
  obtain ⟨S, hS, hH, hbad, hEuler⟩ :=
    sourceKPFiniteCoordinateIntertwiner_eq_euler K hζ g.2 S₀
  refine ⟨S, hS, hH, hbad, ?_⟩
  intro s hs
  have hpos : 0 < s.re := lt_trans (by norm_num) (sourceKPInitialHalfplane_exterior K hs)
  have h := hEuler s hs 1
  change sourceKPFiniteCoordinateIntertwiner K hζ s g.2 1 =
    sourceKPExteriorScattering S s * sourceKPFiniteWindowIntegral K
      (sourceKPFiniteCoordinateIntertwiningKernel K hζ s g.2 1) S at h
  have hk : sourceKPFiniteCoordinateIntertwiningKernel K hζ s g.2 1 =
      sourceKPFiniteIntertwiningKernel K hζ s g.2 :=
    funext (sourceKPFiniteCoordinateIntertwiningKernel_one K hζ s g.2)
  rw [sourceKPFiniteCoordinateIntertwiner_one, hk] at h
  rw [sourceKPAdelicTraceIntertwiner_arch_formula K hζ hpos, h]

theorem sourceKPAdelicSphericalIntertwinerValue_eq_euler
    (g : SourceKPAdelicProjective K hζ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      S₀ ⊆ S ∧ sourceHilbertSet K ∅ ⊆ S ∧ traceBadPlaces K ⊆ S ∧
      ∀ (s : ℂ), ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1 →
        ∀ t : sourceKPAdelicCoveringTorus K hζ,
          (sourceKPAdelicSphericalIntertwinerValue K hζ
            (sourceKPAdelicTraceProduct K) s g).val t =
            (sourceKPAdelicBorelModularHalf K hζ
              (sourceKPAdelicBorelTorusInclusion K hζ
                (sourceKPAdelicCoveringTorusWeyl K hζ t)))⁻¹ *
            sourceArchSphericalProduct K hζ s (sourceKPAdelicCoveringTorusWeyl K hζ t).val.1 *
            (((Real.pi : ℂ) / s) ^ Fintype.card (InfinitePlace K) *
              sourceArchSphericalProduct K hζ (-s) g.1) *
            (sourceKPExteriorScattering S s * sourceKPFiniteWindowIntegral K
              (sourceKPFiniteCoordinateIntertwiningKernel K hζ s g.2
                (sourceKPAdelicCoveringTorusWeyl K hζ t).val.2) S) := by
  obtain ⟨S, hS, hH, hbad, hEuler⟩ :=
    sourceKPFiniteCoordinateIntertwiner_eq_euler K hζ g.2 S₀
  refine ⟨S, hS, hH, hbad, ?_⟩
  intro s hs t
  have hpos : 0 < s.re := lt_trans (by norm_num) (sourceKPInitialHalfplane_exterior K hs)
  rw [sourceKPAdelicSphericalIntertwinerValue_arch_finite K hζ hpos,
    hEuler s hs (sourceKPAdelicCoveringTorusWeyl K hζ t)]

end
end ArtinMatthews

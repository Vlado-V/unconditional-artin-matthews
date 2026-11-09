module

public import ArtinMatthews.SourceKPCoupledWindowContinuation
public import ArtinMatthews.SourceAdelicIntertwinerEuler


set_option backward.privateInPublic true
@[expose] public section

/-! The checked nonzero continuation of the literal finite window
is the remainder in the actual global trace intertwiner at the wild test. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic SourceArchJacquet
open scoped NumberField AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCoupledTraceIntertwiner_eq_window :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      sixthWildPrimes K ⊆ S ∧ sourceHilbertSet K ∅ ⊆ S ∧ traceBadPlaces K ⊆ S ∧
      ∀ s : ℂ, ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1 →
        sourceKPAdelicTraceIntertwiner K hζ s (sourceKPCoupledWildWeyl K hζ) =
          (((Real.pi : ℂ) / s) ^ Fintype.card (InfinitePlace K)) *
            (sourceKPExteriorScattering S s * sourceKPCoupledWindowContinuation K S s) := by
  obtain ⟨S, hS, hHilbert, hTrace, h⟩ := sourceKPAdelicTraceIntertwiner_eq_euler K hζ
    (sourceKPCoupledWildWeyl K hζ) (sixthWildPrimes K)
  refine ⟨S, hS, hHilbert, hTrace, fun s hs => ?_⟩
  have he := h s hs
  rw [sourceKPCoupledWildWeyl_arch K hζ, sourceKPCoupledWindowContinuation_agrees K hζ S hs] at he
  simpa only [sourceArchSphericalProduct, map_one, sourceArchSphericalSection_one,
    Finset.prod_const_one, mul_one] using he

end
end ArtinMatthews

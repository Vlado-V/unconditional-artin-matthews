module

public import ArtinMatthews.SourceKPFiniteCommonWindow
public import ArtinMatthews.SourceKPFiniteCyclicWindow


set_option backward.privateInPublic true
@[expose] public section

/-! Local cyclic relations hold for the actual scattering residues on one
common continuation window, with arbitrary other-place data. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic SourcePhysical
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "ι₀" => sourceKPAdelicLocalProjective K hζ P.val

theorem sourceKPFiniteFiberScatteringResidue_cyclic_relation_common_window
    (hP : P.val ∉ traceBadPlaces K) (qf : SourceKPFiniteAdeleProjective K hζ)
    {I : Type*} [Fintype I] (g : I → SourceFiniteKP2Projective K hζ P.val) (c : I → ℂ)
    (hrel : SourceKPLocalNegativeCyclicRelation K hζ S₀ P g c) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      P.val ∈ S ∧ S₀ ⊆ S ∧ sourceHilbertSet K ∅ ⊆ S ∧ traceBadPlaces K ⊆ S ∧
      (∀ i (s : ℂ), ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1 →
        sourceKPAdelicTraceIntertwiner K hζ s (1, qf * (ι₀ (g i)).2) =
          sourceKPFiniteFiberScatteringContinuation K hζ (qf * (ι₀ (g i)).2) S s) ∧
      ∑ i, c i * sourceKPFiniteFiberScatteringResidue K hζ (qf * (ι₀ (g i)).2) S = 0 := by
  obtain ⟨S, hS, hH, hB, hmatch⟩ := sourceKPFiniteFiberScatteringContinuation_common_window K hζ
    (fun i => qf * (ι₀ (g i)).2) (insert P.val S₀)
  have hPS : P.val ∈ S := hS (Finset.mem_insert_self _ _)
  exact ⟨S, hPS, (Finset.subset_insert _ _).trans hS, hH, hB, hmatch,
    sourceKPFiniteFiberScatteringResidue_cyclic_relation K hζ S₀ P hP qf g c hrel S hPS⟩

end
end ArtinMatthews

module

public import ArtinMatthews.SourceKPAdelicCubeCompact
public import ArtinMatthews.SourceKPFiniteUnipotentTopology


set_option backward.privateInPublic true
@[expose] public section

/-! Every conjugated finite upper root enters the actual global
compact subgroup near zero. Cubing removes the finite central
ambiguity, and division by three preserves the neighborhood. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Topology Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicFiniteConjugate_eventually_compact (g : SourceKPAdelicProjective K hζ) :
    ∀ᶠ t : 𝔸ᶠ[K] in nhds 0,
      g⁻¹ * sourceKPAdelicUpperLift K hζ (0, t) * g ∈ sourceKPAdelicDeepCompact K hζ := by
  obtain ⟨a, ha⟩ := ProjGenLinGroup.mk_surjective (sourceKPAdelicProjectiveProjection K hζ g)
  let af := (sourceKPGL2ProductEquiv K a).2
  have hcubed : ∀ᶠ t : 𝔸ᶠ[K] in nhds 0,
      g⁻¹ * sourceKPAdelicUpperLift K hζ (0, (3 : 𝔸ᶠ[K]) * t) * g ∈
        sourceKPAdelicDeepCompact K hζ := by
    filter_upwards [sourceKPFiniteConjugateMatrix_eventually_deep K af] with t ht
    let k : sourceKPFiniteDeepMatrixGroup K := ⟨sourceKPFiniteConjugateMatrix K af t, ht⟩
    let c : sourceKPAdelicDeepCompact K hζ :=
      ⟨sourceKPFiniteDeepCoverLift K hζ k, ⟨sourceKPFiniteDeepIntoAdelic K hζ k, rfl⟩⟩
    have hp :
        sourceKPAdelicProjectiveProjection K hζ (g⁻¹ * sourceKPAdelicUpperLift K hζ (0, t) * g) =
          sourceKPAdelicProjectiveProjection K hζ c.val := by
      exact (sourceKPAdelicFiniteConjugate_projection K hζ g a ha.symm t).trans
        (sourceKPFiniteDeepCoverLift_projection K hζ k).symm
    have h := sourceKPAdelicCube_mem_compact_of_projection K hζ
      (g⁻¹ * sourceKPAdelicUpperLift K hζ (0, t) * g) c hp
    exact (congrArg (fun x => x ∈ sourceKPAdelicDeepCompact K hζ)
      (sourceKPAdelicFiniteConjugate_cube K hζ g t)).mp h
  let d : 𝔸ᶠ[K] := algebraMap K 𝔸ᶠ[K] ((3 : K)⁻¹)
  have hd : (3 : 𝔸ᶠ[K]) * d = 1 := by
    have hthree : algebraMap K 𝔸ᶠ[K] (3 : K) = (3 : 𝔸ᶠ[K]) :=
      map_natCast (algebraMap K 𝔸ᶠ[K]) 3
    have h := congrArg (algebraMap K 𝔸ᶠ[K]) (mul_inv_cancel₀ (show (3 : K) ≠ 0 by norm_num))
    rw [map_mul, hthree, map_one] at h
    exact h
  have hcont : Filter.Tendsto (fun t : 𝔸ᶠ[K] => d * t) (nhds 0) (nhds 0) := by
    have hc : Continuous (fun t : 𝔸ᶠ[K] => d * t) := continuous_const.mul continuous_id
    simpa only [mul_zero] using hc.tendsto (0 : 𝔸ᶠ[K])
  filter_upwards [hcont.eventually hcubed] with t ht
  simpa only [← mul_assoc, hd, one_mul] using ht

theorem sourceKPAdelicFiniteConjugate_compact_neighborhood (g : SourceKPAdelicProjective K hζ) :
    ∃ U : Set 𝔸ᶠ[K], U ∈ nhds 0 ∧ ∀ t ∈ U,
      g⁻¹ * sourceKPAdelicUpperLift K hζ (0, t) * g ∈ sourceKPAdelicDeepCompact K hζ :=
  ⟨_, sourceKPAdelicFiniteConjugate_eventually_compact K hζ g, fun _ ht => ht⟩

end
end ArtinMatthews

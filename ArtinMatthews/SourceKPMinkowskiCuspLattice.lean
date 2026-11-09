module

public import ArtinMatthews.SourceAdelicFundamentalDomain
public import Mathlib.Analysis.Normed.Module.FiniteDimension


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Minkowski lattice obtained by scaling the integral basis by a nonzero integer. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain Module Module.Free Topology
open scoped NumberField
noncomputable section

variable (K : Type) [Field K] [NumberField K] (d : 𝓞 K) (hd : d ≠ 0)

local notation "E" => mixedEmbedding.mixedSpace K
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)

def sourceKPCuspScaleUnit : Eˣ :=
  Units.map (mixedEmbedding K).toMonoidHom (Units.mk0 (d : K) (by exact_mod_cast hd))

def sourceKPCuspScale : E ≃ₗ[ℝ] E :=
  (sourceKPCuspScaleUnit K d hd).mulLeftLinearEquiv ℝ E

omit [NumberField K] in
lemma sourceKPCuspScale_apply (x : E) :
    sourceKPCuspScale K d hd x = mixedEmbedding K (d : K) * x := rfl

def sourceKPCuspLatticeBasis : Basis I ℝ E :=
  (mixedEmbedding.latticeBasis K).map (sourceKPCuspScale K d hd)

def sourceKPCuspLattice : Submodule ℤ E :=
  Submodule.span ℤ (Set.range (sourceKPCuspLatticeBasis K d hd))

lemma sourceKPCuspLattice_map :
    sourceKPCuspLattice K d hd = (mixedEmbedding.integerLattice K).map
      ((sourceKPCuspScale K d hd).toLinearMap.restrictScalars ℤ) := by
  unfold sourceKPCuspLattice sourceKPCuspLatticeBasis
  rw [Basis.coe_map, Set.range_comp]
  change Submodule.span ℤ
      (((sourceKPCuspScale K d hd).toLinearMap.restrictScalars ℤ) '' Set.range (mixedEmbedding.latticeBasis K)) = _
  rw [← Submodule.map_span, mixedEmbedding.span_latticeBasis]

lemma sourceKPCuspLattice_mem (x : E) :
    x ∈ sourceKPCuspLattice K d hd ↔
      ∃ r : 𝓞 K, mixedEmbedding K ((d * r : 𝓞 K) : K) = x := by
  rw [sourceKPCuspLattice_map, Submodule.mem_map]
  constructor
  · rintro ⟨y, ⟨r, hr⟩, hy⟩
    refine ⟨r, ?_⟩
    rw [← hy, ← hr]
    change mixedEmbedding K ((d * r : 𝓞 K) : K) = mixedEmbedding K (d : K) * mixedEmbedding K (r : K)
    rw [← map_mul]
    rfl
  · rintro ⟨r, hr⟩
    refine ⟨mixedEmbedding K (r : K), ⟨r, rfl⟩, ?_⟩
    change mixedEmbedding K (d : K) * mixedEmbedding K (r : K) = x
    rw [← map_mul]
    exact hr

lemma sourceKPCuspLatticeBasis_apply (i : I) :
    sourceKPCuspLatticeBasis K d hd i = mixedEmbedding K ((d : K) * integralBasis K i) := by
  rw [sourceKPCuspLatticeBasis, Basis.map_apply, sourceKPCuspScale_apply,
    mixedEmbedding.latticeBasis_apply, ← map_mul]

instance sourceKPCuspLattice_discrete : DiscreteTopology (sourceKPCuspLattice K d hd) := by
  let e := (sourceKPCuspScale K d hd).toContinuousLinearEquiv
  have hmem (x : sourceKPCuspLattice K d hd) : e.symm (x : E) ∈ mixedEmbedding.integerLattice K := by
    have hx : (x : E) ∈ (mixedEmbedding.integerLattice K).map
        ((sourceKPCuspScale K d hd).toLinearMap.restrictScalars ℤ) := by
      rw [← sourceKPCuspLattice_map]
      exact x.property
    obtain ⟨y, hy, he⟩ := hx
    change e y = (x : E) at he
    rw [← he, e.symm_apply_apply]
    exact hy
  let f : sourceKPCuspLattice K d hd → mixedEmbedding.integerLattice K :=
    fun x => ⟨e.symm x.val, hmem x⟩
  have hf : Continuous f := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _
  exact DiscreteTopology.of_continuous_injective hf (fun x y h =>
    Subtype.ext (e.symm.injective (congrArg Subtype.val h)))

def sourceKPCuspCoordinates : E ≃L[ℝ] (I → ℝ) :=
  (sourceKPCuspLatticeBasis K d hd).equivFunL

end
end ArtinMatthews

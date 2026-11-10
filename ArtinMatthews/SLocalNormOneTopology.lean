module

public import ArtinMatthews.SLocalNormOneGroup
public import ArtinMatthews.SLocalSUnitIsolation
public import Mathlib.Data.Finsupp.Encodable
public import Mathlib.Data.Rat.Encodable
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.Algebra.ProperAction.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! The subgroup being divided out in the actual source integral is
discrete, closed, and countable. The literal quotient is compact and
Hausdorff; no separation premise on it is supplied. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

theorem sNormOneSixthSubgroup_discrete : DiscreteTopology (sNormOneSixthSubgroup K S) := by
  rw [discreteTopology_iff_isOpen_singleton_one]
  obtain ⟨V, hV, h1, hIso⟩ := exists_sWholeUnit_open_isolation K S
  let f : sNormOneSixthSubgroup K S → SWholeUnits K S := fun x => x.val.val
  have hf : Continuous f := continuous_subtype_val.comp continuous_subtype_val
  have he : f ⁻¹' V = {1} := by
    ext x
    constructor
    · intro hx
      change x.val.val ∈ V at hx
      have hx' : ∃ u : SUnitGroup (K := K) S, sNormOneSixthMap K S u = x.val := x.property
      obtain ⟨u, hu⟩ := hx'
      have hd : sWholeDiagonal K S ((u ^ 6 : SUnitGroup (K := K) S) : Kˣ) = x.val.val :=
        congrArg Subtype.val hu
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      apply Subtype.ext
      exact hd.symm.trans (hIso (u ^ 6) (by rwa [hd]))
    · intro hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact h1
  rw [← he]
  exact hV.preimage hf

theorem sNormOneSixthSubgroup_isClosed :
    IsClosed (sNormOneSixthSubgroup K S : Set (SNormOne K S)) := by
  let : DiscreteTopology (sNormOneSixthSubgroup K S) := sNormOneSixthSubgroup_discrete K S
  exact Subgroup.isClosed_of_discreteTopology

theorem sNormOneSixthQuotient_t2 : T2Space (SNormOneSixthQuotient K S) := by
  let : IsClosed (sNormOneSixthSubgroup K S : Set (SNormOne K S)) :=
    sNormOneSixthSubgroup_isClosed K S
  infer_instance

theorem sNormOneSixthSubgroup_countable : Countable (sNormOneSixthSubgroup K S) := by
  let : Countable K := (Module.finBasis ℚ K).repr.injective.countable
  let : Countable Kˣ := Units.val_injective.countable
  let f (u : SUnitGroup (K := K) S) : sNormOneSixthSubgroup K S :=
    ⟨sNormOneSixthMap K S u, ⟨u, rfl⟩⟩
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨u, hu⟩ := x.property
    exact ⟨u, Subtype.ext hu⟩
  exact hf.countable

end
end ArtinMatthews.SourcePhysical

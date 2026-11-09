module

public import ArtinMatthews.SourceKPMinkowskiCuspLattice
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Topology.Algebra.Group.Quotient


set_option backward.privateInPublic true
@[expose] public section

/-! The actual scaled Minkowski quotient in standard torus coordinates. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain Module Module.Free Topology
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] (d : 𝓞 K) (hd : d ≠ 0)
local notation "E" => mixedEmbedding.mixedSpace K
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)

def sourceKPCuspTorusHom : E →+ UnitAddTorus I :=
  AddMonoidHom.pi (fun i =>
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).comp
      ((Pi.evalAddMonoidHom (fun _ : I => ℝ) i).comp
        (sourceKPCuspCoordinates K d hd).toAddMonoidHom))

lemma sourceKPCuspTorusHom_apply (x : E) (i : I) :
    sourceKPCuspTorusHom K d hd x i = ((sourceKPCuspCoordinates K d hd x i : ℝ) : AddCircle (1 : ℝ)) := rfl

lemma sourceKPCuspTorusHom_ker :
    (sourceKPCuspTorusHom K d hd).ker = (sourceKPCuspLattice K d hd).toAddSubgroup := by
  apply AddSubgroup.ext
  intro x
  change sourceKPCuspTorusHom K d hd x = 0 ↔ x ∈ Submodule.span ℤ (Set.range (sourceKPCuspLatticeBasis K d hd))
  rw [(sourceKPCuspLatticeBasis K d hd).mem_span_iff_repr_mem ℤ x]
  constructor
  · intro hx i
    have hi := congrFun hx i
    change ((sourceKPCuspCoordinates K d hd x i : ℝ) : AddCircle (1 : ℝ)) = 0 at hi
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hi
    exact ⟨n, by simpa [sourceKPCuspCoordinates, zsmul_eq_mul] using hn⟩
  · intro hx
    ext i
    obtain ⟨n, hn⟩ := hx i
    change ((sourceKPCuspCoordinates K d hd x i : ℝ) : AddCircle (1 : ℝ)) = 0
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    exact ⟨n, by simpa [sourceKPCuspCoordinates, zsmul_eq_mul] using hn⟩

lemma sourceKPCuspTorusHom_surjective : Function.Surjective (sourceKPCuspTorusHom K d hd) := by
  intro t
  choose r hr using (fun i : I => QuotientAddGroup.mk_surjective (t i))
  refine ⟨(sourceKPCuspCoordinates K d hd).symm r, ?_⟩
  ext i
  change (((sourceKPCuspCoordinates K d hd) ((sourceKPCuspCoordinates K d hd).symm r) i : ℝ) : AddCircle (1 : ℝ)) = t i
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact hr i

lemma sourceKPCuspTorusHom_continuous : Continuous (sourceKPCuspTorusHom K d hd) := by
  apply continuous_pi
  intro i
  exact (AddCircle.continuous_mk' (1 : ℝ)).comp
    ((continuous_apply i).comp (sourceKPCuspCoordinates K d hd).continuous)

lemma sourceKPCuspTorusHom_isOpenMap : IsOpenMap (sourceKPCuspTorusHom K d hd) := by
  have hp : IsOpenMap (fun x : I → ℝ => fun i => (x i : AddCircle (1 : ℝ))) :=
    IsOpenMap.piMap (fun _ => QuotientAddGroup.isOpenMap_coe)
      (Filter.Eventually.of_forall (fun _ => QuotientAddGroup.mk_surjective))
  exact hp.comp (sourceKPCuspCoordinates K d hd).toHomeomorph.isOpenMap

def sourceKPCuspTorusEquiv : (E ⧸ (sourceKPCuspLattice K d hd).toAddSubgroup) ≃+ UnitAddTorus I :=
  (QuotientAddGroup.quotientAddEquivOfEq (sourceKPCuspTorusHom_ker K d hd).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (sourceKPCuspTorusHom K d hd)
      (sourceKPCuspTorusHom_surjective K d hd))

lemma sourceKPCuspTorusEquiv_mk (x : E) :
    sourceKPCuspTorusEquiv K d hd (QuotientAddGroup.mk x) = sourceKPCuspTorusHom K d hd x := rfl

lemma sourceKPCuspTorusEquiv_continuous : Continuous (sourceKPCuspTorusEquiv K d hd) := by
  apply (QuotientAddGroup.isQuotientMap_mk (sourceKPCuspLattice K d hd).toAddSubgroup).continuous_iff.mpr
  simpa only [Function.comp_def, sourceKPCuspTorusEquiv_mk] using sourceKPCuspTorusHom_continuous K d hd

lemma sourceKPCuspTorusEquiv_isOpenMap : IsOpenMap (sourceKPCuspTorusEquiv K d hd) := by
  apply IsOpenMap.of_comp QuotientAddGroup.continuous_mk QuotientAddGroup.mk_surjective
  simpa only [Function.comp_def, sourceKPCuspTorusEquiv_mk] using sourceKPCuspTorusHom_isOpenMap K d hd

def sourceKPCuspTorusHomeomorph : (E ⧸ (sourceKPCuspLattice K d hd).toAddSubgroup) ≃ₜ+ UnitAddTorus I where
  __ := sourceKPCuspTorusEquiv K d hd
  continuous_toFun := sourceKPCuspTorusEquiv_continuous K d hd
  continuous_invFun := (sourceKPCuspTorusEquiv K d hd).toEquiv.continuous_symm_iff.mpr
    (sourceKPCuspTorusEquiv_isOpenMap K d hd)

end
end ArtinMatthews

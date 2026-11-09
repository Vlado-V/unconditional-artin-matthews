module

public import ArtinMatthews.SLocalSixthCompactReduction
public import ArtinMatthews.SLocalNormAlgebra
public import Mathlib.Topology.Algebra.Group.Quotient


set_option backward.privateInPublic true
@[expose] public section

/-! The literal norm-one S-local group and its quotient by the image
of sixth powers of actual S-units.  The image, rather than a chosen
sixth root, is the eventual counting group in the unfolding. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

theorem continuous_sLocalNorm : Continuous (sLocalNorm K S) :=
  Real.continuous_exp.comp (continuous_sLocalLogSum K S)

def sNormOneSubgroup : Subgroup (SWholeUnits K S) where
  carrier := {x | sLocalNorm K S x = 1}
  one_mem' := sLocalNorm_one K S
  mul_mem' {x y} hx hy := by
    change sLocalNorm K S (x * y) = 1
    rw [sLocalNorm_mul, show sLocalNorm K S x = 1 from hx,
      show sLocalNorm K S y = 1 from hy, mul_one]
  inv_mem' {x} hx := by
    change sLocalNorm K S x⁻¹ = 1
    rw [sLocalNorm_inv, show sLocalNorm K S x = 1 from hx, inv_one]

abbrev SNormOne := sNormOneSubgroup K S

theorem sNormOneSubgroup_isClosed :
    IsClosed (sNormOneSubgroup K S : Set (SWholeUnits K S)) :=
  isClosed_eq (continuous_sLocalNorm K S) continuous_const

def sNormOneUnitMap : SUnitGroup (K := K) S →* SNormOne K S :=
  ((sWholeDiagonal K S).comp (SUnitGroup (K := K) S).subtype).codRestrict
    (sNormOneSubgroup K S) (sLocalNorm_sUnit K S)

def sNormOneSixthMap : SUnitGroup (K := K) S →* SNormOne K S :=
  (sNormOneUnitMap K S).comp (powMonoidHom 6)

theorem sNormOneSixthMap_val (u : SUnitGroup (K := K) S) :
    (sNormOneSixthMap K S u : SWholeUnits K S) = sWholeDiagonal K S ((u : Kˣ) ^ 6) := rfl

def sNormOneSixthSubgroup : Subgroup (SNormOne K S) := (sNormOneSixthMap K S).range

abbrev SNormOneSixthQuotient := SNormOne K S ⧸ sNormOneSixthSubgroup K S

def sNormOneSixthQuotientMap : SNormOne K S →* SNormOneSixthQuotient K S :=
  QuotientGroup.mk' (sNormOneSixthSubgroup K S)

@[simp] theorem sNormOneSixthQuotientMap_sixth (u : SUnitGroup (K := K) S) :
    sNormOneSixthQuotientMap K S (sNormOneSixthMap K S u) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr ⟨u, rfl⟩

def sNormOneCover : Set (SNormOne K S) := Subtype.val ⁻¹' sixthBalancedCompactSet K S

theorem sNormOneCover_isCompact : IsCompact (sNormOneCover K S) := by
  have he := (sNormOneSubgroup_isClosed K S).isClosedEmbedding_subtypeVal.isInducing
  apply (he.isCompact_preimage_iff ?_).mpr (sixthBalancedCompactSet_isCompact K S)
  intro x hx
  exact ⟨⟨x, sixthBalancedCompactSet_norm K S hx⟩, rfl⟩

theorem sNormOneCover_quotient : sNormOneSixthQuotientMap K S '' sNormOneCover K S = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨u, hu⟩ := exists_sUnit_sixth_compact_reduction K S x.val x.property
  refine ⟨x * sNormOneSixthMap K S u, hu, ?_⟩
  rw [map_mul, sNormOneSixthQuotientMap_sixth]
  exact mul_one (sNormOneSixthQuotientMap K S x)

theorem sNormOneSixthQuotient_compact : CompactSpace (SNormOneSixthQuotient K S) := by
  constructor
  rw [← sNormOneCover_quotient K S]
  exact (sNormOneCover_isCompact K S).image continuous_quotient_mk'

end
end ArtinMatthews.SourcePhysical

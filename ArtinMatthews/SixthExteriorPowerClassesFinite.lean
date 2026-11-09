module

public import ArtinMatthews.SixthExteriorPowerClassesUnits
public import Mathlib.GroupTheory.FiniteAbelian.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! The actual exterior S-unit quotient by sixth powers is finite.
Representatives are chosen from this proved finite quotient, and every
S-unit is a representative times a sixth power of an actual S-unit. -/
namespace ArtinMatthews
open IsDedekindDomain
open scoped NumberField
noncomputable section

variable {K : Type*} [Field K] [NumberField K]

abbrev ExteriorUnitSixthClasses (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  exteriorUnitSubgroup S ⧸ (powMonoidHom (α := exteriorUnitSubgroup S) 6).range

instance exteriorUnitSixthClasses_finite (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Finite (ExteriorUnitSixthClasses S) := by
  let : Group.FG (exteriorUnitSubgroup S) := exteriorUnit_fg S
  exact Subgroup.finiteIndex_iff_finite_quotient.mp
    (Subgroup.finiteIndex_range_powMonoidHom_of_fg (exteriorUnitSubgroup S) (by decide : 6≠0))

def exteriorUnitSixthRepresentatives (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Finset (exteriorUnitSubgroup S) := by
  classical
  letI := Fintype.ofFinite (ExteriorUnitSixthClasses S)
  exact Finset.univ.image (Quotient.out : ExteriorUnitSixthClasses S → exteriorUnitSubgroup S)

theorem exteriorUnitSixthRepresentatives_out_mem (S : Finset (HeightOneSpectrum (𝓞 K)))
    (q : ExteriorUnitSixthClasses S) : q.out ∈ exteriorUnitSixthRepresentatives S := by
  classical
  let : Fintype (ExteriorUnitSixthClasses S) := Fintype.ofFinite _
  unfold exteriorUnitSixthRepresentatives
  exact Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩

theorem exteriorUnitSixthClass_out (S : Finset (HeightOneSpectrum (𝓞 K)))
    (q : ExteriorUnitSixthClasses S) :
    QuotientGroup.mk' (powMonoidHom (α := exteriorUnitSubgroup S) 6).range q.out=q :=
  Quotient.out_eq q

theorem exteriorUnitSixthRepresentatives_complete (S : Finset (HeightOneSpectrum (𝓞 K)))
    (u : exteriorUnitSubgroup S) :
    ∃ r ∈ exteriorUnitSixthRepresentatives S, ∃ t : exteriorUnitSubgroup S, u=r*t^6 := by
  let q : ExteriorUnitSixthClasses S :=
    QuotientGroup.mk' (powMonoidHom (α := exteriorUnitSubgroup S) 6).range u
  have hq := exteriorUnitSixthClass_out S q
  change QuotientGroup.mk' (powMonoidHom (α := exteriorUnitSubgroup S) 6).range q.out=
    QuotientGroup.mk' (powMonoidHom (α := exteriorUnitSubgroup S) 6).range u at hq
  obtain ⟨z,hz,he⟩ := (QuotientGroup.mk'_eq_mk'
    (powMonoidHom (α := exteriorUnitSubgroup S) 6).range).mp hq
  obtain ⟨t,ht⟩ := hz
  change t^6=z at ht
  exact ⟨q.out,exteriorUnitSixthRepresentatives_out_mem S q,t,by simpa only [ht] using he.symm⟩

theorem exteriorUnitSixthRepresentatives_unique (S : Finset (HeightOneSpectrum (𝓞 K)))
    {r s : exteriorUnitSubgroup S}
    (hr : r ∈ exteriorUnitSixthRepresentatives S) (hs : s ∈ exteriorUnitSixthRepresentatives S)
    (hclass : QuotientGroup.mk' (powMonoidHom (α := exteriorUnitSubgroup S) 6).range r=
      QuotientGroup.mk' (powMonoidHom (α := exteriorUnitSubgroup S) 6).range s) : r=s := by
  classical
  let : Fintype (ExteriorUnitSixthClasses S) := Fintype.ofFinite _
  unfold exteriorUnitSixthRepresentatives at hr hs
  obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨q',_,rfl⟩ := Finset.mem_image.mp hs
  rw [exteriorUnitSixthClass_out,exteriorUnitSixthClass_out] at hclass
  exact congrArg Quotient.out hclass

def exteriorUnitSixthFieldRepresentatives (S : Finset (HeightOneSpectrum (𝓞 K))) : Finset Kˣ := by
  classical
  exact (exteriorUnitSixthRepresentatives S).image Subtype.val

theorem exteriorUnitSixthFieldRepresentatives_mem (S : Finset (HeightOneSpectrum (𝓞 K)))
    {r : Kˣ} (hr : r ∈ exteriorUnitSixthFieldRepresentatives S) : r ∈ exteriorUnitSubgroup S := by
  classical
  obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hr
  exact u.2

/-- Finite representatives and sixth-power factors are actual field units
with zero valuations outside S; no generator or class representative is
assumed in the construction. -/
theorem exteriorUnitSixthFieldRepresentatives_complete (S : Finset (HeightOneSpectrum (𝓞 K)))
    (u : Kˣ) (hu : u ∈ exteriorUnitSubgroup S) :
    ∃ r ∈ exteriorUnitSixthFieldRepresentatives S,
      ∃ t : exteriorUnitSubgroup S, u=r*(t:Kˣ)^6 := by
  classical
  obtain ⟨r,hr,t,ht⟩ := exteriorUnitSixthRepresentatives_complete S ⟨u,hu⟩
  refine ⟨r.1,Finset.mem_image.mpr ⟨r,hr,rfl⟩,t,?_⟩
  exact congrArg Subtype.val ht

end
end ArtinMatthews

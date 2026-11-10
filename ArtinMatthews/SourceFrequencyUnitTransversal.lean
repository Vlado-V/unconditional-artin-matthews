module

public import ArtinMatthews.SixthExteriorPowerClassesFinite
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial


set_option backward.privateInPublic true
@[expose] public section

/-! Use the actual finite exterior S-unit sixth-power quotient to
choose representatives, with representative one at the principal class.
The residual factor is a distinct sixth power, not a chosen root. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain
open scoped NumberField Classical
noncomputable section
variable {F : Type} [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

abbrev SourceExteriorUnitSixthPowers :=
  (powMonoidHom (α := exteriorUnitSubgroup S) 6).range

def sourceExteriorUnitSixthClass : exteriorUnitSubgroup S →* ExteriorUnitSixthClasses S :=
  QuotientGroup.mk' (SourceExteriorUnitSixthPowers S)

def sourceExteriorUnitSixthRepresentative (q : ExteriorUnitSixthClasses S) : exteriorUnitSubgroup S :=
  if q = 1 then 1 else q.out

@[simp] theorem sourceExteriorUnitSixthRepresentative_one :
    sourceExteriorUnitSixthRepresentative S 1 = 1 := by
  simp [sourceExteriorUnitSixthRepresentative]

@[simp] theorem sourceExteriorUnitSixthRepresentative_class (q : ExteriorUnitSixthClasses S) :
    sourceExteriorUnitSixthClass S (sourceExteriorUnitSixthRepresentative S q) = q := by
  by_cases h : q = 1
  · subst q
    rw [sourceExteriorUnitSixthRepresentative_one, map_one]
  · rw [sourceExteriorUnitSixthRepresentative, ite_eq_right h]
    exact exteriorUnitSixthClass_out S q

theorem sourceExteriorUnitSixthClass_eq_one_iff (u : exteriorUnitSubgroup S) :
    sourceExteriorUnitSixthClass S u = 1 ↔ u ∈ SourceExteriorUnitSixthPowers S :=
  QuotientGroup.eq_one_iff _

def sourceExteriorUnitSixthEquiv :
    ExteriorUnitSixthClasses S × SourceExteriorUnitSixthPowers S ≃ exteriorUnitSubgroup S :=
  Equiv.ofBijective (fun p => sourceExteriorUnitSixthRepresentative S p.1 * p.2.val) (by
    have hclass (q : ExteriorUnitSixthClasses S) (u : SourceExteriorUnitSixthPowers S) :
        sourceExteriorUnitSixthClass S (sourceExteriorUnitSixthRepresentative S q * u.val) = q := by
      rw [map_mul, sourceExteriorUnitSixthRepresentative_class,
        (sourceExteriorUnitSixthClass_eq_one_iff S u.val).mpr u.property]
      exact mul_one q
    constructor
    · rintro ⟨q, u⟩ ⟨r, v⟩ h
      change sourceExteriorUnitSixthRepresentative S q * u.val =
        sourceExteriorUnitSixthRepresentative S r * v.val at h
      have hqr : q = r := (hclass q u).symm.trans
        ((congrArg (sourceExteriorUnitSixthClass S) h).trans (hclass r v))
      subst r
      exact Prod.ext rfl (Subtype.ext (mul_left_cancel h))
    · intro u
      let q := sourceExteriorUnitSixthClass S u
      let v := (sourceExteriorUnitSixthRepresentative S q)⁻¹ * u
      have hv : v ∈ SourceExteriorUnitSixthPowers S := by
        apply (sourceExteriorUnitSixthClass_eq_one_iff S v).mp
        rw [show v = _ from rfl, map_mul, map_inv, sourceExteriorUnitSixthRepresentative_class]
        exact inv_mul_cancel q
      refine ⟨(q, ⟨v, hv⟩), ?_⟩
      change sourceExteriorUnitSixthRepresentative S q * ((sourceExteriorUnitSixthRepresentative S q)⁻¹ * u) = u
      exact mul_inv_cancel_left _ _)

@[simp] theorem sourceExteriorUnitSixthEquiv_apply (q : ExteriorUnitSixthClasses S)
    (u : SourceExteriorUnitSixthPowers S) :
    sourceExteriorUnitSixthEquiv S (q, u) = sourceExteriorUnitSixthRepresentative S q * u.val := rfl

theorem sourceExteriorUnitSixthPower_exists_root (u : SourceExteriorUnitSixthPowers S) :
    ∃ t : exteriorUnitSubgroup S, u.val = t ^ 6 := by
  obtain ⟨t, ht⟩ := u.property
  exact ⟨t, ht.symm⟩

end
end ArtinMatthews

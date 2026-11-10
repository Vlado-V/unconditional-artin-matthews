module

public import Mathlib.RingTheory.ClassGroup.ExtendedHom
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

/-! Localization is surjective on ideal class groups. Killing the images
of a complete family of integral representatives therefore makes the
localized Dedekind domain principal. -/

namespace ArtinMatthews.SIntegerPrincipalization
open scoped nonZeroDivisors Classical
noncomputable section

variable {R A : Type*} [CommRing R] [CommRing A]
    [IsDedekindDomain R] [IsDedekindDomain A] [Algebra R A] [Module.IsTorsionFree R A]

theorem classGroup_extendedHom_surjective (M : Submonoid R) [IsLocalization M A] :
    Function.Surjective (ClassGroup.extendedHom R A) := by
  intro c
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective c
  have hI : J.val.under R ≠ ⊥ := by
    intro he
    have hm := IsLocalization.map_under M A J.val
    rw [he, Ideal.map_bot] at hm
    exact (mem_nonZeroDivisors_iff_ne_zero.mp J.property) hm.symm
  let I : (Ideal R)⁰ := ⟨J.val.under R, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
  refine ⟨ClassGroup.mk0 I, ?_⟩
  rw [ClassGroup.extendedHom_mk0]
  have he : ClassGroup.extendedIdeal R A I = J := by
    apply Subtype.ext
    exact IsLocalization.map_under M A J.val
  rw [he]
  exact hJ

theorem classGroup_extendedHom_eq_one_of_representatives
    (rep : ClassGroup R → (Ideal R)⁰) (hrep : ∀ c, ClassGroup.mk0 (rep c) = c)
    (hunit : ∀ c, (rep c).val.map (algebraMap R A) = ⊤) :
    ClassGroup.extendedHom R A = 1 := by
  ext c
  rw [← hrep c, ClassGroup.extendedHom_mk0, MonoidHom.one_apply]
  apply (ClassGroup.mk0_eq_one_iff (ClassGroup.extendedIdeal R A (rep c)).property).mpr
  change ((rep c).val.map (algebraMap R A)).IsPrincipal
  rw [hunit]
  infer_instance

theorem localization_classGroup_subsingleton (M : Submonoid R) [IsLocalization M A]
    (rep : ClassGroup R → (Ideal R)⁰) (hrep : ∀ c, ClassGroup.mk0 (rep c) = c)
    (hunit : ∀ c, (rep c).val.map (algebraMap R A) = ⊤) :
    Subsingleton (ClassGroup A) := by
  have ht := classGroup_extendedHom_eq_one_of_representatives rep hrep hunit
  have hall (c : ClassGroup A) : c = 1 := by
    obtain ⟨b, hb⟩ := classGroup_extendedHom_surjective (A := A) M c
    rw [← hb, ht, MonoidHom.one_apply]
  exact ⟨fun a b => (hall a).trans (hall b).symm⟩

theorem localization_isPrincipalIdealRing_of_representatives
    (M : Submonoid R) [IsLocalization M A]
    (rep : ClassGroup R → (Ideal R)⁰) (hrep : ∀ c, ClassGroup.mk0 (rep c) = c)
    (hunit : ∀ c, (rep c).val.map (algebraMap R A) = ⊤) : IsPrincipalIdealRing A := by
  let : Subsingleton (ClassGroup A) := localization_classGroup_subsingleton M rep hrep hunit
  refine ⟨fun I => ?_⟩
  by_cases hI : I = ⊥
  · rw [hI]
    infer_instance
  · exact (ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_iff_ne_zero.mpr hI)).mp
      (Subsingleton.elim _ _)

end
end ArtinMatthews.SIntegerPrincipalization

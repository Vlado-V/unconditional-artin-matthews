module

public import ArtinMatthews.VaryingKummerAnalyticIdealModuleFrequencyLabels
public import ArtinMatthews.VaryingKummerAnalyticIdealGaussFourier
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality


set_option backward.privateInPublic true
@[expose] public section

/-! The whole finite trace-dual quotient, including nonunit frequencies.
Actual trace characters on I/(MI) are parametrized by O/M, without a
coprimality assumption on I or a principal different. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem primitive_addChar_mulShift_bijective {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) : Function.Bijective ψ.mulShift := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨AddChar.to_mulShift_inj_of_isPrimitive hψ, (AddChar.card_eq (α := R)).symm⟩

def idealModuleFrequencyResidueValue (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)
    (r : (𝓞 K) ⧸ M) : K :=
  idealModuleTraceFrequencyBase K I M hI hM * (Quotient.out r : 𝓞 K)

theorem idealModuleFrequencyResidueValue_character (I M : Ideal (𝓞 K))
    (hI : I ≠ ⊥) (hM : M ≠ ⊥) (r : (𝓞 K) ⧸ M) (a : I) :
    idealModuleTraceChar K I (idealModuleFrequencyResidueValue K I M hI hM r) a =
      idealTraceAddChar K M hM (r * idealResidueCoordinate I M hI hM a) := by
  let b : 𝓞 K := Quotient.out r
  calc
    _ = idealModuleTraceChar K I (idealModuleTraceFrequencyBase K I M hI hM) (b • a) := by
      simp only [idealModuleTraceChar_apply, fieldTraceAddChar_apply]
      congr 3
      congr 1
      change (idealModuleTraceFrequencyBase K I M hI hM * (b : K)) * (a.val : K) =
        idealModuleTraceFrequencyBase K I M hI hM * ((b * a.val : 𝓞 K) : K)
      exact mul_assoc _ _ _
    _ = idealTraceAddChar K M hM (idealResidueCoordinate I M hI hM (b • a)) :=
      congrArg (fun χ : AddChar I ℂ => χ (b • a))
        (idealModuleTraceFrequencyBase_character K I M hI hM)
    _ = _ := by
      rw [map_smul]
      change idealTraceAddChar K M hM
        (Ideal.Quotient.mk M b * idealResidueCoordinate I M hI hM a) = _
      rw [show Ideal.Quotient.mk M b = r from Ideal.Quotient.mk_out r]

theorem idealModuleFrequencyResidueValue_mem_dual (I M : Ideal (𝓞 K))
    (hI : I ≠ ⊥) (hM : M ≠ ⊥) (r : (𝓞 K) ⧸ M) :
    idealModuleFrequencyResidueValue K I M hI hM r ∈
      dual ℤ ℚ ((M*I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [FractionalIdeal.mem_dual (FractionalIdeal.coeIdeal_ne_zero.mpr (mul_ne_zero hM hI))]
  intro y hy
  obtain ⟨a,ha,rfl⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hy
  let b : I := ⟨a, (Ideal.mul_le_right : M*I ≤ I) ha⟩
  have hc : idealResidueCoordinate I M hI hM b = 0 := by
    rw [← map_zero (Ideal.Quotient.mk M)]
    apply (idealResidueCoordinate_eq_mk_iff I M hI hM b 0).mpr
    simpa only [zero_mul, sub_zero] using ha
  have H := idealModuleFrequencyResidueValue_character K I M hI hM r b
  rw [hc, mul_zero, AddChar.map_zero_eq_one] at H
  exact (fieldTraceAddChar_eq_one_iff K _ a).mp H

theorem idealModuleTraceChar_one_on_relation (I M : Ideal (𝓞 K))
    (hI : I ≠ ⊥) (hM : M ≠ ⊥) (β : K)
    (hβ : β ∈ dual ℤ ℚ ((M*I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))
    (a : I) (ha : a ∈ idealModuleRelation I M) : idealModuleTraceChar K I β a = 1 := by
  apply (fieldTraceAddChar_eq_one_iff K β a.val).mpr
  exact (FractionalIdeal.mem_dual
    (FractionalIdeal.coeIdeal_ne_zero.mpr (mul_ne_zero hM hI))).mp hβ
      (a.val : K) (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰ ha)

def idealModuleDualQuotientAddChar (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)
    (β : K) (hβ : β ∈ dual ℤ ℚ ((M*I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) :
    AddChar (IdealModuleResidue I M) ℂ :=
  AddChar.toAddMonoidHomEquiv.symm
    (QuotientAddGroup.lift (idealModuleRelation I M).toAddSubgroup
      (idealModuleTraceChar K I β).toAddMonoidHom
      (fun a ha => idealModuleTraceChar_one_on_relation K I M hI hM β hβ a ha))

@[simp] theorem idealModuleDualQuotientAddChar_mk (I M : Ideal (𝓞 K))
    (hI : I ≠ ⊥) (hM : M ≠ ⊥) (β : K)
    (hβ : β ∈ dual ℤ ℚ ((M*I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) (a : I) :
    idealModuleDualQuotientAddChar K I M hI hM β hβ (Submodule.Quotient.mk a) =
      idealModuleTraceChar K I β a := rfl

theorem idealModuleDual_exists_unique_residue (I M : Ideal (𝓞 K))
    (hI : I ≠ ⊥) (hM : M ≠ ⊥) (β : K)
    (hβ : β ∈ dual ℤ ℚ ((M*I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) :
    ∃! r : (𝓞 K) ⧸ M,
      β - idealModuleFrequencyResidueValue K I M hI hM r ∈
        dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) := by
  let : Finite ((𝓞 K) ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient hM
  let : Fintype ((𝓞 K) ⧸ M) := Fintype.ofFinite _
  let η := (idealModuleDualQuotientAddChar K I M hI hM β hβ).compAddMonoidHom
    (idealModuleTrivialization I M hI hM).toAddMonoidHom
  obtain ⟨r,hr⟩ := (primitive_addChar_mulShift_bijective
    (idealTraceAddChar K M hM) (idealTraceAddChar_isPrimitive K M hM)).surjective η
  have he : idealModuleTraceChar K I β =
      idealModuleTraceChar K I (idealModuleFrequencyResidueValue K I M hI hM r) := by
    ext a
    rw [idealModuleFrequencyResidueValue_character]
    have H := congrArg (fun χ : AddChar ((𝓞 K) ⧸ M) ℂ =>
      χ (idealResidueCoordinate I M hI hM a)) hr
    change idealTraceAddChar K M hM (r * idealResidueCoordinate I M hI hM a) =
      idealModuleDualQuotientAddChar K I M hI hM β hβ
        (idealModuleTrivialization I M hI hM (idealResidueCoordinate I M hI hM a)) at H
    rw [idealResidueCoordinate_trivialization, idealModuleDualQuotientAddChar_mk] at H
    exact H.symm
  refine ⟨r, (idealModuleTraceChar_eq_iff_sub_mem_dual K I hI _ _).mp he, ?_⟩
  intro s hs
  apply AddChar.to_mulShift_inj_of_isPrimitive (idealTraceAddChar_isPrimitive K M hM)
  ext x
  obtain ⟨a,rfl⟩ := idealResidueCoordinate_surjective I M hI hM x
  have H := (idealModuleTraceChar_eq_iff_sub_mem_dual K I hI _ _).mpr hs
  have H' := congrArg (fun χ : AddChar I ℂ => χ a) (H.symm.trans he)
  simpa only [idealModuleFrequencyResidueValue_character, AddChar.mulShift_apply] using H'

def idealModuleDualResidue (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)
    (β : K) (hβ : β ∈ dual ℤ ℚ ((M*I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) :
    (𝓞 K) ⧸ M :=
  (idealModuleDual_exists_unique_residue K I M hI hM β hβ).exists.choose

theorem idealModuleDualResidue_spec (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)
    (β : K) (hβ : β ∈ dual ℤ ℚ ((M*I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) :
    β - idealModuleFrequencyResidueValue K I M hI hM
      (idealModuleDualResidue K I M hI hM β hβ) ∈
        dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) :=
  (idealModuleDual_exists_unique_residue K I M hI hM β hβ).exists.choose_spec

theorem idealModuleDualResidue_eq_iff (I M : Ideal (𝓞 K))
    (hI : I ≠ ⊥) (hM : M ≠ ⊥) (β : K)
    (hβ : β ∈ dual ℤ ℚ ((M*I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))
    (r : (𝓞 K) ⧸ M) :
    idealModuleDualResidue K I M hI hM β hβ = r ↔
      β - idealModuleFrequencyResidueValue K I M hI hM r ∈
        dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) := by
  constructor
  · intro h
    rw [← h]
    exact idealModuleDualResidue_spec K I M hI hM β hβ
  · intro h
    exact (idealModuleDual_exists_unique_residue K I M hI hM β hβ).unique
      (idealModuleDualResidue_spec K I M hI hM β hβ) h

theorem idealModuleDualResidue_eq_iff_sub_mem_dual (I M : Ideal (𝓞 K))
    (hI : I ≠ ⊥) (hM : M ≠ ⊥) (β γ : K)
    (hβ : β ∈ dual ℤ ℚ ((M*I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))
    (hγ : γ ∈ dual ℤ ℚ ((M*I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) :
    idealModuleDualResidue K I M hI hM β hβ = idealModuleDualResidue K I M hI hM γ hγ ↔
      β - γ ∈ dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) := by
  have Hβ := idealModuleDualResidue_spec K I M hI hM β hβ
  have Hγ := idealModuleDualResidue_spec K I M hI hM γ hγ
  constructor
  · intro h
    rw [h] at Hβ
    change β - γ ∈ (dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K)).val
    simpa only [sub_sub_sub_cancel_right] using
      (dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K)).val.sub_mem Hβ Hγ
  · intro h
    apply (idealModuleDualResidue_eq_iff K I M hI hM β hβ _).mpr
    change β - idealModuleFrequencyResidueValue K I M hI hM
      (idealModuleDualResidue K I M hI hM γ hγ) ∈
        (dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K)).val
    convert (dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K)).val.add_mem h Hγ using 1
    ring

theorem idealModuleDualResidue_frequencyResidueValue (I M : Ideal (𝓞 K))
    (hI : I ≠ ⊥) (hM : M ≠ ⊥) (r : (𝓞 K) ⧸ M) :
    idealModuleDualResidue K I M hI hM
      (idealModuleFrequencyResidueValue K I M hI hM r)
      (idealModuleFrequencyResidueValue_mem_dual K I M hI hM r) = r := by
  apply (idealModuleDualResidue_eq_iff K I M hI hM _ _ r).mpr
  rw [sub_self]
  exact (dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K)).zero_mem

theorem idealModuleDualResidue_character (I M : Ideal (𝓞 K))
    (hI : I ≠ ⊥) (hM : M ≠ ⊥) (β : K)
    (hβ : β ∈ dual ℤ ℚ ((M*I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) (a : I) :
    idealModuleTraceChar K I β a = idealTraceAddChar K M hM
      (idealModuleDualResidue K I M hI hM β hβ * idealResidueCoordinate I M hI hM a) := by
  have he := (idealModuleTraceChar_eq_iff_sub_mem_dual K I hI _ _).mpr
    (idealModuleDualResidue_spec K I M hI hM β hβ)
  exact (congrArg (fun χ : AddChar I ℂ => χ a) he).trans
    (idealModuleFrequencyResidueValue_character K I M hI hM _ a)

theorem idealModuleDualQuotientAddChar_trivialization (I M : Ideal (𝓞 K))
    (hI : I ≠ ⊥) (hM : M ≠ ⊥) (β : K)
    (hβ : β ∈ dual ℤ ℚ ((M*I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))
    (r : (𝓞 K) ⧸ M) :
    idealModuleDualQuotientAddChar K I M hI hM β hβ
        (idealModuleTrivialization I M hI hM r) =
      idealTraceAddChar K M hM (idealModuleDualResidue K I M hI hM β hβ * r) := by
  obtain ⟨a,rfl⟩ := idealResidueCoordinate_surjective I M hI hM r
  rw [idealResidueCoordinate_trivialization, idealModuleDualQuotientAddChar_mk]
  exact idealModuleDualResidue_character K I M hI hM β hβ a

/-- Exact finite Fourier transform on I/(MI), at every actual frequency in
dual(MI). The residue label is uniquely determined modulo dual(I). -/
theorem idealModule_primitive_trace_transform (I M : Ideal (𝓞 K))
    (hI : I ≠ ⊥) [NeZero M] (χ : MulChar ((𝓞 K) ⧸ M) ℂ)
    (hχ : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals χ) (β : K)
    (hβ : β ∈ dual ℤ ℚ ((M*I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) :
    (∑' a : IdealModuleResidue I M,
      χ ((idealModuleTrivialization I M hI (NeZero.ne M)).symm a) *
        idealModuleDualQuotientAddChar K I M hI (NeZero.ne M) β hβ a) =
      χ⁻¹ (idealModuleDualResidue K I M hI (NeZero.ne M) β hβ) *
        idealTraceGaussSum K M χ := by
  let : Finite ((𝓞 K) ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
  let : Fintype ((𝓞 K) ⧸ M) := Fintype.ofFinite _
  rw [← (idealModuleTrivialization I M hI (NeZero.ne M)).toEquiv.tsum_eq]
  simp only [LinearEquiv.coe_toEquiv, LinearEquiv.symm_apply_apply,
    idealModuleDualQuotientAddChar_trivialization, tsum_fintype]
  exact idealTraceFourier_primitive K M χ hχ _

theorem idealModule_primitive_trace_transform_norm (I M : Ideal (𝓞 K))
    (hI : I ≠ ⊥) [NeZero M] (χ : MulChar ((𝓞 K) ⧸ M) ℂ)
    (hχ : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals χ) (β : K)
    (hβ : β ∈ dual ℤ ℚ ((M*I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) :
    ‖∑' a : IdealModuleResidue I M,
      χ ((idealModuleTrivialization I M hI (NeZero.ne M)).symm a) *
        idealModuleDualQuotientAddChar K I M hI (NeZero.ne M) β hβ a‖ =
      if IsUnit (idealModuleDualResidue K I M hI (NeZero.ne M) β hβ)
      then Real.sqrt (Ideal.absNorm M : ℝ) else 0 := by
  let : Finite ((𝓞 K) ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
  let : Fintype ((𝓞 K) ⧸ M) := Fintype.ofFinite _
  rw [idealModule_primitive_trace_transform K I M hI χ hχ β hβ]
  split_ifs with hu
  · have hunit : ‖χ⁻¹ (hu.unit : (𝓞 K) ⧸ M)‖ = 1 :=
      Complex.norm_eq_one_of_mem_rootsOfUnity ((χ⁻¹).apply_mem_rootsOfUnity hu.unit)
    rw [norm_mul, ← hu.unit_spec, hunit, one_mul]
    exact idealTraceGaussSum_norm K M χ hχ
  · rw [MulChar.map_nonunit _ hu, zero_mul, norm_zero]

end
end ArtinMatthews.VaryingKummerAnalytic

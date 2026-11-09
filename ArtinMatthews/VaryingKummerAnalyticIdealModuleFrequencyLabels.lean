module

public import ArtinMatthews.VaryingKummerAnalyticIdealModuleFrequencyTrace
public import ArtinMatthews.VaryingKummerAnalyticIdealFrequencyLabelSeparation


set_option backward.privateInPublic true
@[expose] public section

/-! Primitive trace labels on a fixed nonzero ideal. Their exact scalar
annihilator recovers the varying modulus without coprimality assumptions. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def idealModuleFrequencyValue (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)
    (u : ((𝓞 K) ⧸ M)ˣ) : K :=
  idealModuleTraceFrequencyBase K I M hI hM * (Quotient.out (u : (𝓞 K) ⧸ M) : 𝓞 K)

theorem idealModuleFrequencyValue_character (I M : Ideal (𝓞 K))
    (hI : I ≠ ⊥) (hM : M ≠ ⊥) (u : ((𝓞 K) ⧸ M)ˣ) (a : I) :
    idealModuleTraceChar K I (idealModuleFrequencyValue K I M hI hM u) a =
      idealTraceAddChar K M hM
        ((u : (𝓞 K) ⧸ M) * idealResidueCoordinate I M hI hM a) := by
  let r : 𝓞 K := Quotient.out (u : (𝓞 K) ⧸ M)
  calc
    _ = idealModuleTraceChar K I (idealModuleTraceFrequencyBase K I M hI hM) (r • a) := by
      simp only [idealModuleTraceChar_apply, fieldTraceAddChar_apply]
      congr 3
      congr 1
      change (idealModuleTraceFrequencyBase K I M hI hM * (r : K)) * (a.val : K) =
        idealModuleTraceFrequencyBase K I M hI hM * ((r * a.val : 𝓞 K) : K)
      exact mul_assoc _ _ _
    _ = idealTraceAddChar K M hM (idealResidueCoordinate I M hI hM (r • a)) := by
      exact congrArg (fun χ : AddChar I ℂ => χ (r • a))
        (idealModuleTraceFrequencyBase_character K I M hI hM)
    _ = _ := by
      rw [map_smul]
      change idealTraceAddChar K M hM
        (Ideal.Quotient.mk M r * idealResidueCoordinate I M hI hM a) = _
      rw [show Ideal.Quotient.mk M r = (u : (𝓞 K) ⧸ M) from Ideal.Quotient.mk_out _]

def idealModuleScalarShift (I : Ideal (𝓞 K)) (χ : AddChar I ℂ) (r : 𝓞 K) : AddChar I ℂ :=
  χ.compAddMonoidHom (r • (LinearMap.id : I →ₗ[𝓞 K] I)).toAddMonoidHom

omit [NumberField K] in
theorem idealModuleScalarShift_apply (I : Ideal (𝓞 K)) (χ : AddChar I ℂ)
    (r : 𝓞 K) (a : I) : idealModuleScalarShift K I χ r a = χ (r • a) := rfl

theorem idealModuleFrequencyValue_smul_character (I M : Ideal (𝓞 K))
    (hI : I ≠ ⊥) (hM : M ≠ ⊥) (u : ((𝓞 K) ⧸ M)ˣ) (r : 𝓞 K) (a : I) :
    idealModuleTraceChar K I (idealModuleFrequencyValue K I M hI hM u) (r • a) =
      idealTraceAddChar K M hM
        (((u : (𝓞 K) ⧸ M) * Ideal.Quotient.mk M r) * idealResidueCoordinate I M hI hM a) := by
  rw [idealModuleFrequencyValue_character, map_smul]
  change idealTraceAddChar K M hM
    ((u : (𝓞 K) ⧸ M) * (Ideal.Quotient.mk M r * idealResidueCoordinate I M hI hM a)) = _
  rw [mul_assoc]

/-- The primitive label has precisely M as its scalar annihilator on I. -/
theorem idealModuleFrequencyValue_annihilator (I M : Ideal (𝓞 K))
    (hI : I ≠ ⊥) (hM : M ≠ ⊥) (u : ((𝓞 K) ⧸ M)ˣ) (r : 𝓞 K) :
    idealModuleScalarShift K I
      (idealModuleTraceChar K I (idealModuleFrequencyValue K I M hI hM u)) r = 1 ↔ r ∈ M := by
  constructor
  · intro h
    have hs : (idealTraceAddChar K M hM).mulShift
        ((u : (𝓞 K) ⧸ M) * Ideal.Quotient.mk M r) = 1 := by
      ext x
      obtain ⟨a, rfl⟩ := idealResidueCoordinate_surjective I M hI hM x
      have H := congrArg (fun χ : AddChar I ℂ => χ a) h
      simpa only [idealModuleScalarShift_apply, idealModuleFrequencyValue_smul_character,
        AddChar.mulShift_apply, AddChar.one_apply] using H
    have hz : (u : (𝓞 K) ⧸ M) * Ideal.Quotient.mk M r = 0 := by
      by_contra hn
      exact idealTraceAddChar_isPrimitive K M hM hn hs
    exact Ideal.Quotient.eq_zero_iff_mem.mp (u.isUnit.mul_right_eq_zero.mp hz)
  · intro hr
    ext a
    simp only [idealModuleScalarShift_apply, idealModuleFrequencyValue_smul_character,
      Ideal.Quotient.eq_zero_iff_mem.mpr hr, mul_zero, zero_mul,
      AddChar.map_zero_eq_one, AddChar.one_apply]

theorem idealModuleFrequencyValue_mem_dual (I M : Ideal (𝓞 K))
    (hI : I ≠ ⊥) (hM : M ≠ ⊥) (u : ((𝓞 K) ⧸ M)ˣ) :
    idealModuleFrequencyValue K I M hI hM u ∈
      FractionalIdeal.dual ℤ ℚ ((M * I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [FractionalIdeal.mem_dual (FractionalIdeal.coeIdeal_ne_zero.mpr (mul_ne_zero hM hI))]
  intro y hy
  obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hy
  let b : I := ⟨a, (Ideal.mul_le_right : M * I ≤ I) ha⟩
  have hc : idealResidueCoordinate I M hI hM b = 0 := by
    rw [← map_zero (Ideal.Quotient.mk M)]
    apply (idealResidueCoordinate_eq_mk_iff I M hI hM b 0).mpr
    simpa only [zero_mul, sub_zero] using ha
  have H := idealModuleFrequencyValue_character K I M hI hM u b
  rw [hc, mul_zero, AddChar.map_zero_eq_one] at H
  exact (fieldTraceAddChar_eq_one_iff K _ a).mp H

theorem idealModuleFrequencyValue_modulus_eq_of_sub_mem_dual
    (I M N : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥) (hN : N ≠ ⊥)
    (u : ((𝓞 K) ⧸ M)ˣ) (v : ((𝓞 K) ⧸ N)ˣ)
    (h : idealModuleFrequencyValue K I M hI hM u - idealModuleFrequencyValue K I N hI hN v ∈
      FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K)) : M = N := by
  have he := (idealModuleTraceChar_eq_iff_sub_mem_dual K I hI _ _).mpr h
  ext r
  rw [← idealModuleFrequencyValue_annihilator K I M hI hM u r,
    ← idealModuleFrequencyValue_annihilator K I N hI hN v r, he]

theorem idealModuleFrequencyValue_injective_mod_dual
    (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)
    (u v : ((𝓞 K) ⧸ M)ˣ)
    (h : idealModuleFrequencyValue K I M hI hM u - idealModuleFrequencyValue K I M hI hM v ∈
      FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K)) : u = v := by
  have he := (idealModuleTraceChar_eq_iff_sub_mem_dual K I hI _ _).mpr h
  apply Units.ext
  apply AddChar.to_mulShift_inj_of_isPrimitive (idealTraceAddChar_isPrimitive K M hM)
  ext x
  obtain ⟨a, rfl⟩ := idealResidueCoordinate_surjective I M hI hM x
  simpa only [idealModuleFrequencyValue_character, AddChar.mulShift_apply] using
    congrArg (fun χ : AddChar I ℂ => χ a) he

def idealModuleFrequencyLabelValue (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (ℓ : IdealFrequencyLabel K) : K :=
  idealModuleFrequencyValue K I ℓ.1.val hI ℓ.1.property ℓ.2

theorem idealModuleFrequencyLabel_eq_of_sub_mem_dual
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (ℓ ℓ' : IdealFrequencyLabel K)
    (h : idealModuleFrequencyLabelValue K I hI ℓ - idealModuleFrequencyLabelValue K I hI ℓ' ∈
      FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K)) : ℓ = ℓ' := by
  rcases ℓ with ⟨⟨M, hM⟩, u⟩
  rcases ℓ' with ⟨⟨N, hN⟩, v⟩
  have hMN := idealModuleFrequencyValue_modulus_eq_of_sub_mem_dual K I M N hI hM hN u v h
  cases hMN
  have huv := idealModuleFrequencyValue_injective_mod_dual K I M hI hM u v h
  subst v
  rfl

theorem idealModuleFrequencyLabel_difference_ne_zero
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) {ℓ ℓ' : IdealFrequencyLabel K} (hne : ℓ ≠ ℓ') {r : K}
    (hr : r ∈ FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K)) :
    idealModuleFrequencyLabelValue K I hI ℓ - idealModuleFrequencyLabelValue K I hI ℓ' + r ≠ 0 := by
  intro hz
  apply hne
  apply idealModuleFrequencyLabel_eq_of_sub_mem_dual K I hI
  rw [eq_neg_of_add_eq_zero_left hz]
  exact (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K)).val.neg_mem hr

end
end ArtinMatthews.VaryingKummerAnalytic

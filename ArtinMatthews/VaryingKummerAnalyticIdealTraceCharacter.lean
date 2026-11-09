module

public import ArtinMatthews.VaryingKummerAnalyticIdealTraceGenerator
public import OAI.NumberTheory.DirichletL.FiniteFourier


set_option backward.privateInPublic true
@[expose] public section

/-! Actual primitive additive trace characters on arbitrary nonzero ideal
quotients of a number field, using a genuinely constructed dual generator. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def integerTraceAddChar (β : Kˣ) : AddChar (𝓞 K) ℂ where
  toFun a := Complex.exp ((Algebra.trace ℚ K ((β : K)*(a : K)) : ℂ) *
    (2 * (Real.pi : ℂ) * Complex.I))
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by simp [mul_add, map_add, add_mul, Complex.exp_add]

theorem integerTraceAddChar_eq_one_iff (β : Kˣ) (a : 𝓞 K) :
    integerTraceAddChar K β a = 1 ↔
      Algebra.trace ℚ K ((β : K)*(a : K)) ∈ (algebraMap ℤ ℚ).range := by
  change Complex.exp (_ * (2 * (Real.pi : ℂ) * Complex.I)) = 1 ↔ _
  rw [Complex.exp_eq_one_iff]
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  constructor
  · rintro ⟨n,hn⟩
    have H := mul_right_cancel₀ hc hn
    refine ⟨n,?_⟩
    exact_mod_cast H.symm
  · rintro ⟨n,hn⟩
    refine ⟨n,?_⟩
    congr 1
    exact_mod_cast hn.symm

def idealTraceGenerator (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) : Kˣ :=
  (exists_trace_modulus_generator K M hM).choose

theorem idealTraceGenerator_spec (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (a : 𝓞 K) :
    ((a : K) ∈ FractionalIdeal.dual ℤ ℚ
      (toPrincipalIdeal (𝓞 K) K (idealTraceGenerator K M hM)).val ↔ a ∈ M) :=
  (exists_trace_modulus_generator K M hM).choose_spec a

theorem integerTraceAddChar_eq_one_of_mem (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (a : 𝓞 K) (ha : a ∈ M) : integerTraceAddChar K (idealTraceGenerator K M hM) a = 1 := by
  rw [integerTraceAddChar_eq_one_iff]
  have hm := (idealTraceGenerator_spec K M hM a).mpr ha
  have H := (FractionalIdeal.mem_dual (toPrincipalIdeal (𝓞 K) K
    (idealTraceGenerator K M hM)).ne_zero).mp hm
  have hb : (idealTraceGenerator K M hM : K) ∈
      (toPrincipalIdeal (𝓞 K) K (idealTraceGenerator K M hM)).val :=
    by rw [coe_toPrincipalIdeal]; exact FractionalIdeal.mem_spanSingleton_self _ _
  simpa only [Algebra.traceForm_apply, mul_comm] using H _ hb

def idealTraceAddChar (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) : AddChar ((𝓞 K) ⧸ M) ℂ :=
  AddChar.toAddMonoidHomEquiv.symm
    (QuotientAddGroup.lift M.toAddSubgroup (integerTraceAddChar K (idealTraceGenerator K M hM)).toAddMonoidHom
      (fun a ha => integerTraceAddChar_eq_one_of_mem K M hM a ha))

theorem idealTraceAddChar_mk (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (a : 𝓞 K) :
    idealTraceAddChar K M hM (Ideal.Quotient.mk M a) =
      integerTraceAddChar K (idealTraceGenerator K M hM) a := rfl

theorem idealTraceAddChar_isPrimitive (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) :
    (idealTraceAddChar K M hM).IsPrimitive := by
  intro x hx he
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  apply hx
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply (idealTraceGenerator_spec K M hM a).mp
  rw [FractionalIdeal.mem_dual (toPrincipalIdeal (𝓞 K) K
    (idealTraceGenerator K M hM)).ne_zero]
  intro y hy
  rw [coe_toPrincipalIdeal] at hy
  obtain ⟨b,rfl⟩ := (FractionalIdeal.mem_spanSingleton _).mp hy
  have H := congrArg (fun χ : AddChar ((𝓞 K) ⧸ M) ℂ => χ (Ideal.Quotient.mk M b)) he
  simp only [AddChar.mulShift_apply, ← map_mul, idealTraceAddChar_mk, AddChar.one_apply] at H
  have ht := (integerTraceAddChar_eq_one_iff K (idealTraceGenerator K M hM) (a*b)).mp H
  convert ht using 1
  simp only [Algebra.traceForm_apply, Algebra.smul_def, map_mul]
  congr 1
  ring

end
end ArtinMatthews.VaryingKummerAnalytic

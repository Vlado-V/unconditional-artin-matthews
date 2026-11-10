module

public import ArtinMatthews.ArtinRayResidueRealization
public import ArtinMatthews.VaryingKummerAnalyticRayIdealCharacter
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Residue realization at a genuine integral ideal modulus. This is an
algebraic constructor after a principal congruence kernel has been proved;
the sharp-modulus application obtains that kernel from actual Artin reciprocity. -/
namespace ArtinMatthews.VaryingKummerAnalytic.PrincipalIdealRay
open PrincipalRay
open scoped NumberField nonZeroDivisors Classical
noncomputable section

variable {F : Type*} [Field F] [NumberField F]
variable (φ : (FractionalIdeal (𝓞 F)⁰ F)ˣ →* ℂˣ)

def KernelLaw (M : Ideal (𝓞 F)) : Prop :=
  ∀ (a : 𝓞 F) (ha : a ≠ 0), a-1 ∈ M → principalValue φ a ha=1

omit [NumberField F] in
theorem exists_nonzero_lift (M : Ideal (𝓞 F)) (hM : M ≠ ⊥) (x : (𝓞 F) ⧸ M) :
    ∃ a : 𝓞 F, a ≠ 0 ∧ Ideal.Quotient.mk M a=x := by
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  by_cases ha : a=0
  · subst a
    obtain ⟨b,hb,hb0⟩ := M.ne_bot_iff.mp hM
    exact ⟨b,hb0,(Ideal.Quotient.eq_zero_iff_mem.mpr hb).trans (map_zero _).symm⟩
  · exact ⟨a,ha,rfl⟩

def residueLift (M : Ideal (𝓞 F)) (hM : M ≠ ⊥) (u : ((𝓞 F) ⧸ M)ˣ) : 𝓞 F :=
  (exists_nonzero_lift M hM (u : (𝓞 F) ⧸ M)).choose

omit [NumberField F] in
theorem residueLift_ne_zero (M : Ideal (𝓞 F)) (hM : M ≠ ⊥) (u : ((𝓞 F) ⧸ M)ˣ) :
    residueLift M hM u ≠ 0 := (exists_nonzero_lift M hM (u : (𝓞 F) ⧸ M)).choose_spec.1

omit [NumberField F] in
theorem residueLift_spec (M : Ideal (𝓞 F)) (hM : M ≠ ⊥) (u : ((𝓞 F) ⧸ M)ˣ) :
    Ideal.Quotient.mk M (residueLift M hM u)=(u : (𝓞 F) ⧸ M) :=
  (exists_nonzero_lift M hM (u : (𝓞 F) ⧸ M)).choose_spec.2

theorem principalValue_eq (M : Ideal (𝓞 F)) (hM : M ≠ ⊥) (hk : KernelLaw φ M)
    (u : ((𝓞 F) ⧸ M)ˣ) (a b : 𝓞 F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hqa : Ideal.Quotient.mk M a=(u : (𝓞 F) ⧸ M))
    (hqb : Ideal.Quotient.mk M b=(u : (𝓞 F) ⧸ M)) :
    PrincipalRay.principalValue φ a ha=PrincipalRay.principalValue φ b hb := by
  let c := residueLift M hM u⁻¹
  have hc : c ≠ 0 := residueLift_ne_zero M hM u⁻¹
  have hqc : Ideal.Quotient.mk M c=(u⁻¹ : ((𝓞 F) ⧸ M)ˣ) := residueLift_spec M hM u⁻¹
  have hac : a*c-1 ∈ M := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub,map_mul,hqa,hqc,map_one,Units.mul_inv,sub_self]
  have hbc : b*c-1 ∈ M := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub,map_mul,hqb,hqc,map_one,Units.mul_inv,sub_self]
  have hA := hk (a*c) (mul_ne_zero ha hc) hac
  have hB := hk (b*c) (mul_ne_zero hb hc) hbc
  rw [PrincipalRay.principalValue_mul φ a c ha hc] at hA
  rw [PrincipalRay.principalValue_mul φ b c hb hc] at hB
  exact mul_right_cancel (hA.trans hB.symm)

def residueHom (M : Ideal (𝓞 F)) (hM : M ≠ ⊥) (hk : KernelLaw φ M) :
    ((𝓞 F) ⧸ M)ˣ →* ℂˣ where
  toFun u := PrincipalRay.principalValue φ (residueLift M hM u) (residueLift_ne_zero M hM u)
  map_one' := by
    apply hk
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub,map_one,residueLift_spec,Units.val_one,sub_self]
  map_mul' u v := by
    rw [← PrincipalRay.principalValue_mul]
    apply principalValue_eq φ M hM hk (u*v)
    · exact residueLift_spec M hM (u*v)
    · rw [map_mul,residueLift_spec,residueLift_spec,Units.val_mul]

theorem residueHom_spec (M : Ideal (𝓞 F)) (hM : M ≠ ⊥) (hk : KernelLaw φ M)
    (a : 𝓞 F) (ha : a ≠ 0) (u : ((𝓞 F) ⧸ M)ˣ)
    (hq : Ideal.Quotient.mk M a=(u : (𝓞 F) ⧸ M)) :
    residueHom φ M hM hk u=PrincipalRay.principalValue φ a ha :=
  principalValue_eq φ M hM hk u _ a (residueLift_ne_zero M hM u) ha
    (residueLift_spec M hM u) hq

def realize (M : Ideal (𝓞 F)) (hM : M ≠ ⊥) (hk : KernelLaw φ M)
    (hf : ∃ e : ℕ, 0 < e ∧ ∀ I, φ I^e=1) : EvenIdealRayCharacter F M where
  idealHom := φ
  finiteOrder := hf
  residue := MulChar.ofUnitHom (residueHom φ M hM hk)
  principalLaw a ha hc := by
    have hu := (quotient_isUnit_iff_span_coprime M a).mpr hc
    change (PrincipalRay.principalValue φ a ha : ℂ)=_
    rw [show Ideal.Quotient.mk M a=(hu.unit : (𝓞 F) ⧸ M) from hu.unit_spec.symm,
      MulChar.ofUnitHom_coe,residueHom_spec φ M hM hk a ha hu.unit hu.unit_spec.symm]

@[simp] theorem realize_idealHom (M : Ideal (𝓞 F)) (hM : M ≠ ⊥) (hk : KernelLaw φ M)
    (hf : ∃ e : ℕ, 0 < e ∧ ∀ I, φ I^e=1) : (realize φ M hM hk hf).idealHom=φ := rfl

end
end ArtinMatthews.VaryingKummerAnalytic.PrincipalIdealRay

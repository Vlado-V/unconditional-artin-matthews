module

public import ArtinMatthews.VaryingKummerAnalyticIdealTraceCharacter
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
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual ideal-quotient frequency labels.  Their trace characters recover
the modulus, so distinct labels remain distinct modulo the trace-dual lattice. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- The additive trace character of an arbitrary field frequency. -/
def fieldTraceAddChar (α : K) : AddChar (𝓞 K) ℂ where
  toFun a := Complex.exp ((Algebra.trace ℚ K (α * (a : K)) : ℂ) *
    (2 * (Real.pi : ℂ) * Complex.I))
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by simp [mul_add, map_add, add_mul, Complex.exp_add]

theorem fieldTraceAddChar_apply (α : K) (a : 𝓞 K) :
    fieldTraceAddChar K α a = Complex.exp
      ((Algebra.trace ℚ K (α * (a : K)) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := rfl

theorem fieldTraceAddChar_eq_one_iff (α : K) (a : 𝓞 K) :
    fieldTraceAddChar K α a = 1 ↔
      Algebra.trace ℚ K (α * (a : K)) ∈ (algebraMap ℤ ℚ).range := by
  change Complex.exp (_ * (2 * (Real.pi : ℂ) * Complex.I)) = 1 ↔ _
  rw [Complex.exp_eq_one_iff]
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  constructor
  · rintro ⟨n, hn⟩
    have H := mul_right_cancel₀ hc hn
    refine ⟨n, ?_⟩
    exact_mod_cast H.symm
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    congr 1
    exact_mod_cast hn.symm

theorem fieldTraceAddChar_eq_one_iff_mem_dual (α : K) :
    fieldTraceAddChar K α = 1 ↔
      α ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [FractionalIdeal.mem_dual one_ne_zero]
  constructor
  · intro h y hy
    obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff (𝓞 K)⁰).mp hy
    have he := congrArg (fun χ : AddChar (𝓞 K) ℂ => χ a) h
    simpa only [Algebra.traceForm_apply] using
      (fieldTraceAddChar_eq_one_iff K α a).mp he
  · intro h
    ext a
    apply (fieldTraceAddChar_eq_one_iff K α a).mpr
    exact h _ (FractionalIdeal.coe_mem_one (𝓞 K)⁰ a)

theorem fieldTraceAddChar_sub (α β : K) :
    fieldTraceAddChar K (α - β) = fieldTraceAddChar K α / fieldTraceAddChar K β := by
  ext a
  simp only [AddChar.div_apply', fieldTraceAddChar_apply, sub_mul, map_sub,
    Rat.cast_sub, Complex.exp_sub]

theorem fieldTraceAddChar_eq_iff_sub_mem_dual (α β : K) :
    fieldTraceAddChar K α = fieldTraceAddChar K β ↔
      α - β ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [← fieldTraceAddChar_eq_one_iff_mem_dual, fieldTraceAddChar_sub, div_eq_one]

/-- A lift of a unit residue gives an actual field frequency. -/
def idealFrequencyValue (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (u : ((𝓞 K) ⧸ M)ˣ) : K :=
  (idealTraceGenerator K M hM : K) * (Quotient.out (u : (𝓞 K) ⧸ M) : 𝓞 K)

theorem idealFrequencyValue_character (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (u : ((𝓞 K) ⧸ M)ˣ) (a : 𝓞 K) :
    fieldTraceAddChar K (idealFrequencyValue K M hM u) a =
      idealTraceAddChar K M hM ((u : (𝓞 K) ⧸ M) * Ideal.Quotient.mk M a) := by
  conv_rhs => rw [← Ideal.Quotient.mk_out (u : (𝓞 K) ⧸ M), ← map_mul,
    idealTraceAddChar_mk]
  change Complex.exp _ = Complex.exp _
  congr 3
  simp only [idealFrequencyValue, map_mul, mul_assoc]

theorem idealFrequencyValue_mem_dual (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (u : ((𝓞 K) ⧸ M)ˣ) :
    idealFrequencyValue K M hM u ∈
      FractionalIdeal.dual ℤ ℚ (M : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [FractionalIdeal.mem_dual (FractionalIdeal.coeIdeal_ne_zero.mpr hM)]
  intro y hy
  obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hy
  apply (fieldTraceAddChar_eq_one_iff K _ a).mp
  rw [idealFrequencyValue_character, Ideal.Quotient.eq_zero_iff_mem.mpr ha,
    mul_zero, AddChar.map_zero_eq_one]

theorem idealFrequencyValue_annihilator (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (u : ((𝓞 K) ⧸ M)ˣ) (a : 𝓞 K) :
    (fieldTraceAddChar K (idealFrequencyValue K M hM u)).mulShift a = 1 ↔ a ∈ M := by
  constructor
  · intro h
    have hshift : (idealTraceAddChar K M hM).mulShift
        ((u : (𝓞 K) ⧸ M) * Ideal.Quotient.mk M a) = 1 := by
      ext x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      have H := congrArg (fun χ : AddChar (𝓞 K) ℂ => χ b) h
      simpa only [AddChar.mulShift_apply, idealFrequencyValue_character,
        map_mul, AddChar.one_apply, mul_assoc] using H
    have hz : (u : (𝓞 K) ⧸ M) * Ideal.Quotient.mk M a = 0 := by
      by_contra hn
      exact idealTraceAddChar_isPrimitive K M hM hn hshift
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact (u.isUnit.mul_right_eq_zero).mp hz
  · intro ha
    ext b
    simp only [AddChar.mulShift_apply, idealFrequencyValue_character,
      map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_mul, mul_zero,
      AddChar.map_zero_eq_one, AddChar.one_apply]

theorem idealFrequencyValue_modulus_eq_of_sub_mem_dual
    (M N : Ideal (𝓞 K)) (hM : M ≠ ⊥) (hN : N ≠ ⊥)
    (u : ((𝓞 K) ⧸ M)ˣ) (v : ((𝓞 K) ⧸ N)ˣ)
    (h : idealFrequencyValue K M hM u - idealFrequencyValue K N hN v ∈
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)) : M = N := by
  have he := (fieldTraceAddChar_eq_iff_sub_mem_dual K _ _).mpr h
  ext a
  rw [← idealFrequencyValue_annihilator K M hM u a,
    ← idealFrequencyValue_annihilator K N hN v a, he]

theorem idealFrequencyValue_injective_mod_dual (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (u v : ((𝓞 K) ⧸ M)ˣ)
    (h : idealFrequencyValue K M hM u - idealFrequencyValue K M hM v ∈
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)) : u = v := by
  have he := (fieldTraceAddChar_eq_iff_sub_mem_dual K _ _).mpr h
  apply Units.ext
  apply AddChar.to_mulShift_inj_of_isPrimitive (idealTraceAddChar_isPrimitive K M hM)
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simpa only [idealFrequencyValue_character, AddChar.mulShift_apply] using
    congrArg (fun χ : AddChar (𝓞 K) ℂ => χ a) he

end
end ArtinMatthews.VaryingKummerAnalytic

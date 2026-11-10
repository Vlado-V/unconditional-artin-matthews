module

public import ArtinMatthews.VaryingKummerAnalyticIdealTraceCharacter
public import Mathlib.Algebra.AffineMonoid.Basic
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
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The literal trace phase exp(2*pi*i*Tr(x/a)) on a principal integral
modulus. Primitivity is derived from the actual different ideal. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def probeStandardTraceBeta (a : 𝓞 K) (ha : a ≠ 0) : Kˣ :=
  (Units.mk0 (a : K) (RingOfIntegers.coe_ne_zero_iff.mpr ha))⁻¹

omit [NumberField K] in
theorem probeStandardTraceBeta_value (a : 𝓞 K) (ha : a ≠ 0) :
    (probeStandardTraceBeta K a ha : K) = (a : K)⁻¹ := rfl

theorem probeStandardTrace_dual (a : 𝓞 K) (ha : a ≠ 0) :
    FractionalIdeal.dual ℤ ℚ (toPrincipalIdeal (𝓞 K) K (probeStandardTraceBeta K a ha)).val =
      ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) /
        ((differentIdeal ℤ (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
  have hprincipal : (toPrincipalIdeal (𝓞 K) K
      (Units.mk0 (a : K) (RingOfIntegers.coe_ne_zero_iff.mpr ha))).val =
      ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [coe_toPrincipalIdeal, coeIdeal_span_singleton]
    rfl
  rw [probeStandardTraceBeta, map_inv, Units.val_inv_eq_inv_val, hprincipal,
    FractionalIdeal.dual_inv]
  rw [div_eq_mul_inv, coeIdeal_differentIdeal ℤ ℚ K (𝓞 K), inv_inv,
    mul_comm]

theorem probeStandardTrace_dual_integer_iff (a : 𝓞 K) (ha : a ≠ 0)
    (hcop : IsCoprime (differentIdeal ℤ (𝓞 K)) (Ideal.span {a})) (x : 𝓞 K) :
    (x : K) ∈ FractionalIdeal.dual ℤ ℚ
      (toPrincipalIdeal (𝓞 K) K (probeStandardTraceBeta K a ha)).val ↔
        x ∈ Ideal.span {a} := by
  rw [probeStandardTrace_dual]
  exact integral_mem_fractional_div_coprime K (Ideal.span {a}) (differentIdeal ℤ (𝓞 K))
    differentIdeal_ne_bot hcop x

theorem probeStandardTrace_period (a : 𝓞 K) (ha : a ≠ 0)
    (hcop : IsCoprime (differentIdeal ℤ (𝓞 K)) (Ideal.span {a}))
    (x : 𝓞 K) (hx : x ∈ Ideal.span {a}) :
    integerTraceAddChar K (probeStandardTraceBeta K a ha) x = 1 := by
  rw [integerTraceAddChar_eq_one_iff]
  have hm := (probeStandardTrace_dual_integer_iff K a ha hcop x).mpr hx
  have ht := (FractionalIdeal.mem_dual
    (toPrincipalIdeal (𝓞 K) K (probeStandardTraceBeta K a ha)).ne_zero).mp hm
  have hb : (probeStandardTraceBeta K a ha : K) ∈
      (toPrincipalIdeal (𝓞 K) K (probeStandardTraceBeta K a ha)).val := by
    rw [coe_toPrincipalIdeal]
    exact FractionalIdeal.mem_spanSingleton_self _ _
  simpa only [Algebra.traceForm_apply, mul_comm] using ht _ hb

def probeStandardTraceModChar (a : 𝓞 K) (ha : a ≠ 0)
    (hcop : IsCoprime (differentIdeal ℤ (𝓞 K)) (Ideal.span {a})) :
    AddChar ((𝓞 K) ⧸ Ideal.span {a}) ℂ :=
  AddChar.toAddMonoidHomEquiv.symm (QuotientAddGroup.lift (Ideal.span {a}).toAddSubgroup
    (integerTraceAddChar K (probeStandardTraceBeta K a ha)).toAddMonoidHom
    (fun x hx => probeStandardTrace_period K a ha hcop x hx))

theorem probeStandardTraceModChar_mk (a : 𝓞 K) (ha : a ≠ 0)
    (hcop : IsCoprime (differentIdeal ℤ (𝓞 K)) (Ideal.span {a})) (x : 𝓞 K) :
    probeStandardTraceModChar K a ha hcop (Ideal.Quotient.mk _ x) =
      Complex.exp ((Algebra.trace ℚ K ((x : K) / (a : K)) : ℂ) *
        (2 * (Real.pi : ℂ) * Complex.I)) := by
  change Complex.exp ((Algebra.trace ℚ K
    ((probeStandardTraceBeta K a ha : K) * (x : K)) : ℂ) *
      (2 * (Real.pi : ℂ) * Complex.I)) = _
  rw [probeStandardTraceBeta_value, div_eq_mul_inv, mul_comm ((a : K)⁻¹) (x : K)]

theorem probeStandardTraceModChar_primitive (a : 𝓞 K) (ha : a ≠ 0)
    (hcop : IsCoprime (differentIdeal ℤ (𝓞 K)) (Ideal.span {a})) :
    (probeStandardTraceModChar K a ha hcop).IsPrimitive := by
  intro x hx he
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply hx
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply (probeStandardTrace_dual_integer_iff K a ha hcop x).mp
  rw [FractionalIdeal.mem_dual (toPrincipalIdeal (𝓞 K) K (probeStandardTraceBeta K a ha)).ne_zero]
  intro y hy
  rw [coe_toPrincipalIdeal] at hy
  obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).mp hy
  have ht := congrArg (fun ψ : AddChar ((𝓞 K) ⧸ Ideal.span {a}) ℂ =>
    ψ (Ideal.Quotient.mk _ b)) he
  change integerTraceAddChar K (probeStandardTraceBeta K a ha) (x * b) = 1 at ht
  have H := (integerTraceAddChar_eq_one_iff K (probeStandardTraceBeta K a ha) (x * b)).mp ht
  have hmul : ((x * b : 𝓞 K) : K) = (x : K) * (b : K) :=
    map_mul (algebraMap (𝓞 K) K) x b
  rw [hmul] at H
  simpa only [Algebra.traceForm_apply, Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm] using H

end
end ArtinMatthews.VaryingKummerAnalytic

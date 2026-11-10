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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! A coherent trace tower on the actual principal prime-power quotients.
It is built from the genuine trace-dual generator at the first power, rather
than postulating compatibility of independently chosen quotient characters. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped NumberField Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def probeTracePrimeUnit (p : 𝓞 K) (hp : p ≠ 0) : Kˣ :=
  Units.mk0 (p : K) (by exact_mod_cast hp)

def probePrimeTraceParameter (p : 𝓞 K) (hp : p ≠ 0) (n : ℕ) : Kˣ :=
  idealTraceGenerator K (Ideal.span {p}) (Ideal.span_singleton_eq_bot.not.mpr hp) *
    (probeTracePrimeUnit K p hp)⁻¹ ^ n

def probeIntegerPrimeTrace (p : 𝓞 K) (hp : p ≠ 0) (n : ℕ) : AddChar (𝓞 K) ℂ :=
  integerTraceAddChar K (probePrimeTraceParameter K p hp n)

theorem probeIntegerPrimeTrace_scale (p : 𝓞 K) (hp : p ≠ 0) (n : ℕ) (x : 𝓞 K) :
    probeIntegerPrimeTrace K p hp n (p ^ n * x) =
      integerTraceAddChar K (idealTraceGenerator K (Ideal.span {p})
        (Ideal.span_singleton_eq_bot.not.mpr hp)) x := by
  change Complex.exp _ = Complex.exp _
  apply congrArg (fun z : K => Complex.exp
    ((Algebra.trace ℚ K z : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)))
  simp only [probePrimeTraceParameter, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_inv_eq_inv_val, probeTracePrimeUnit, Units.val_mk0, map_mul, map_pow]
  have hpK : (p : K) ≠ 0 := by exact_mod_cast hp
  rw [inv_pow, mul_assoc, ← mul_assoc ((p : K) ^ n)⁻¹,
    inv_mul_cancel₀ (pow_ne_zero n hpK), one_mul]

theorem probeIntegerPrimeTrace_step (p : 𝓞 K) (hp : p ≠ 0) (n : ℕ) (x : 𝓞 K) :
    probeIntegerPrimeTrace K p hp (n + 1) (p * x) =
      probeIntegerPrimeTrace K p hp n x := by
  change Complex.exp _ = Complex.exp _
  apply congrArg (fun z : K => Complex.exp
    ((Algebra.trace ℚ K z : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)))
  simp only [probePrimeTraceParameter, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_inv_eq_inv_val, probeTracePrimeUnit, Units.val_mk0, map_mul, pow_succ]
  have hpK : (p : K) ≠ 0 := by exact_mod_cast hp
  field_simp

theorem probeIntegerPrimeTrace_period (p : 𝓞 K) (hp : p ≠ 0) (n : ℕ)
    (x : 𝓞 K) (hx : x ∈ Ideal.span {p ^ (n + 1)}) :
    probeIntegerPrimeTrace K p hp n x = 1 := by
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
  rw [pow_succ, mul_assoc, probeIntegerPrimeTrace_scale]
  exact integerTraceAddChar_eq_one_of_mem K (Ideal.span {p})
    (Ideal.span_singleton_eq_bot.not.mpr hp) (p * y)
    (Ideal.mem_span_singleton.mpr ⟨y, rfl⟩)

def probePrimePowerTrace (p : 𝓞 K) (hp : p ≠ 0) (n : ℕ) :
    AddChar ((𝓞 K) ⧸ Ideal.span {p ^ (n + 1)}) ℂ :=
  AddChar.toAddMonoidHomEquiv.symm
    (QuotientAddGroup.lift (Ideal.span {p ^ (n + 1)}).toAddSubgroup
      (probeIntegerPrimeTrace K p hp n).toAddMonoidHom
      (fun x hx => probeIntegerPrimeTrace_period K p hp n x hx))

theorem probePrimePowerTrace_mk (p : 𝓞 K) (hp : p ≠ 0) (n : ℕ) (x : 𝓞 K) :
    probePrimePowerTrace K p hp n (Ideal.Quotient.mk _ x) =
      probeIntegerPrimeTrace K p hp n x := rfl

private theorem probeIntegerPrimeTrace_base_annihilator (p : 𝓞 K) (hp : p ≠ 0)
    (d : 𝓞 K)
    (hd : ∀ y : 𝓞 K, integerTraceAddChar K
      (idealTraceGenerator K (Ideal.span {p})
        (Ideal.span_singleton_eq_bot.not.mpr hp)) (d * y) = 1) : p ∣ d := by
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  by_contra hn
  apply idealTraceAddChar_isPrimitive K (Ideal.span {p})
    (Ideal.span_singleton_eq_bot.not.mpr hp) hn
  ext y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  simpa only [AddChar.mulShift_apply, ← map_mul, idealTraceAddChar_mk,
    AddChar.one_apply] using hd y

theorem probeIntegerPrimeTrace_annihilator (p : 𝓞 K) (hp : p ≠ 0)
    (n : ℕ) (d : 𝓞 K)
    (hd : ∀ y : 𝓞 K, probeIntegerPrimeTrace K p hp n (d * y) = 1) :
    p ^ (n + 1) ∣ d := by
  induction n generalizing d with
  | zero =>
      simp only [Nat.zero_add, pow_one]
      apply probeIntegerPrimeTrace_base_annihilator K p hp d
      simpa only [probeIntegerPrimeTrace, probePrimeTraceParameter, pow_zero, mul_one] using hd
  | succ n ih =>
      have hpd : p ∣ d := by
        apply probeIntegerPrimeTrace_base_annihilator K p hp d
        intro y
        have he := hd (p ^ (n + 1) * y)
        rw [show d * (p ^ (n + 1) * y) = p ^ (n + 1) * (d * y) by ring,
          probeIntegerPrimeTrace_scale] at he
        exact he
      obtain ⟨d, rfl⟩ := hpd
      have hsmall : ∀ y : 𝓞 K, probeIntegerPrimeTrace K p hp n (d * y) = 1 := by
        intro y
        have he := hd y
        rw [mul_assoc, probeIntegerPrimeTrace_step] at he
        exact he
      obtain ⟨z, hz⟩ := ih d hsmall
      refine ⟨z, ?_⟩
      rw [hz, pow_succ']
      ring

theorem probePrimePowerTrace_primitive (p : 𝓞 K) (hp : p ≠ 0) (n : ℕ) :
    (probePrimePowerTrace K p hp n).IsPrimitive := by
  intro x hx he
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply hx
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton.mpr
  apply probeIntegerPrimeTrace_annihilator K p hp n d
  intro y
  have ht := congrArg
    (fun χ : AddChar ((𝓞 K) ⧸ Ideal.span {p ^ (n + 1)}) ℂ =>
      χ (Ideal.Quotient.mk _ y)) he
  simpa only [AddChar.mulShift_apply, ← map_mul, probePrimePowerTrace_mk,
    AddChar.one_apply] using ht

theorem probePrimePowerTrace_base (p : 𝓞 K) (hp : p ≠ 0) (x : 𝓞 K) :
    probePrimePowerTrace K p hp 0 (Ideal.Quotient.mk _ x) =
      idealTraceAddChar K (Ideal.span {p})
        (Ideal.span_singleton_eq_bot.not.mpr hp) (Ideal.Quotient.mk _ x) := by
  simp only [probePrimePowerTrace_mk, probeIntegerPrimeTrace, probePrimeTraceParameter,
    pow_zero, mul_one, idealTraceAddChar_mk]

end

end ArtinMatthews.VaryingKummerAnalytic

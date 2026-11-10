module

public import ArtinMatthews.ProbeStandardTraceModulus
public import OAI.NumberTheory.DirichletL.GaussSum.ChineseRemainder
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact CRT component phases for literal standard trace characters on
integral principal moduli. The Bezout residue multipliers are retained. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField OAI.IdealGaussCRT
open scoped NumberField BigOperators Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem probeDifferentCoprime_left (a b : 𝓞 K)
    (h : IsCoprime (differentIdeal ℤ (𝓞 K)) (Ideal.span {a * b})) :
    IsCoprime (differentIdeal ℤ (𝓞 K)) (Ideal.span {a}) := by
  rw [← Ideal.span_singleton_mul_span_singleton] at h
  exact h.of_mul_right_left

theorem probeDifferentCoprime_right (a b : 𝓞 K)
    (h : IsCoprime (differentIdeal ℤ (𝓞 K)) (Ideal.span {a * b})) :
    IsCoprime (differentIdeal ℤ (𝓞 K)) (Ideal.span {b}) := by
  rw [← Ideal.span_singleton_mul_span_singleton] at h
  exact h.of_mul_right_right

def probeStandardProductPhase (a b : 𝓞 K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hD : IsCoprime (differentIdeal ℤ (𝓞 K)) (Ideal.span {a * b})) :
    AddChar ((𝓞 K) ⧸ (Ideal.span {a} * Ideal.span {b})) ℂ :=
  (probeStandardTraceModChar K (a * b) (mul_ne_zero ha hb) hD).compAddMonoidHom
    (Ideal.quotEquivOfEq (Ideal.span_singleton_mul_span_singleton a b)).toAddMonoidHom

theorem probeStandardProductPhase_mk (a b : 𝓞 K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hD : IsCoprime (differentIdeal ℤ (𝓞 K)) (Ideal.span {a * b})) (x : 𝓞 K) :
    probeStandardProductPhase K a b ha hb hD (Ideal.Quotient.mk _ x) =
      Complex.exp ((Algebra.trace ℚ K ((x : K) / ((a : K) * (b : K))) : ℂ) *
        (2 * (Real.pi : ℂ) * Complex.I)) := by
  change probeStandardTraceModChar K (a * b) (mul_ne_zero ha hb) hD
    (Ideal.quotEquivOfEq (Ideal.span_singleton_mul_span_singleton a b) (Ideal.Quotient.mk _ x)) = _
  rw [Ideal.quotEquivOfEq_mk, probeStandardTraceModChar_mk]
  have hab : ((a * b : 𝓞 K) : K) = (a : K) * (b : K) :=
    map_mul (algebraMap (𝓞 K) K) a b
  rw [hab]

theorem probeStandardProductPhase_left (a b u v : 𝓞 K)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hD : IsCoprime (differentIdeal ℤ (𝓞 K)) (Ideal.span {a * b}))
    (hbez : u * a + v * b = 1) :
    leftAddChar (Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
      (principal_coprime_of_bezout hbez)) (probeStandardProductPhase K a b ha hb hD) =
      (probeStandardTraceModChar K a ha (probeDifferentCoprime_left K a b hD)).mulShift
        (Ideal.Quotient.mk (Ideal.span {a}) v) := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change probeStandardProductPhase K a b ha hb hD
    ((Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
      (principal_coprime_of_bezout hbez)).symm (Ideal.Quotient.mk _ x, 0)) = _
  rw [crt_left_inverse_coordinate hbez x]
  simp only [probeStandardProductPhase_mk, AddChar.mulShift_apply, ← map_mul,
    probeStandardTraceModChar_mk]
  have hbK : (b : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hb
  have hfrac : ((x * v * b : 𝓞 K) : K) / ((a : K) * (b : K)) =
      ((v * x : 𝓞 K) : K) / (a : K) := by
    simp only [map_mul]
    field_simp
  rw [map_mul (algebraMap (𝓞 K) K) a b]
  rw [hfrac]

theorem probeStandardProductPhase_right (a b u v : 𝓞 K)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hD : IsCoprime (differentIdeal ℤ (𝓞 K)) (Ideal.span {a * b}))
    (hbez : u * a + v * b = 1) :
    rightAddChar (Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
      (principal_coprime_of_bezout hbez)) (probeStandardProductPhase K a b ha hb hD) =
      (probeStandardTraceModChar K b hb (probeDifferentCoprime_right K a b hD)).mulShift
        (Ideal.Quotient.mk (Ideal.span {b}) u) := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change probeStandardProductPhase K a b ha hb hD
    ((Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
      (principal_coprime_of_bezout hbez)).symm (0, Ideal.Quotient.mk _ x)) = _
  rw [crt_right_inverse_coordinate hbez x]
  simp only [probeStandardProductPhase_mk, AddChar.mulShift_apply, ← map_mul,
    probeStandardTraceModChar_mk]
  have haK : (a : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr ha
  have hfrac : ((x * u * a : 𝓞 K) : K) / ((a : K) * (b : K)) =
      ((u * x : 𝓞 K) : K) / (b : K) := by
    simp only [map_mul]
    field_simp
  rw [map_mul (algebraMap (𝓞 K) K) a b]
  rw [hfrac]

end
end ArtinMatthews.VaryingKummerAnalytic

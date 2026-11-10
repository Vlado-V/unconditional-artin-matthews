module

public import ArtinMatthews.SIntegerCharacterTransport
public import ArtinMatthews.SIntegerFinitePrincipalization
public import ArtinMatthews.StandardAdelicSIntegerPhase
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
public import Mathlib.NumberTheory.SelbergSieve
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

/-! Literal standard e_S phases under coprime S-integer CRT. The
inverse cofactor multipliers are proved from the actual Bezout identity,
so no local phase comparison unit is set to one. -/
namespace ArtinMatthews.SIntegerQuotient

open NumberField OAI.IdealGaussCRT ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.StandardAdelic
open scoped NumberField Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))

def sourceProductPhase (a b : PrincipalIntegerRing S₀) (ha : a ≠ 0) (hb : b ≠ 0) :
    AddChar ((PrincipalIntegerRing S₀) ⧸ (Ideal.span {a} * Ideal.span {b})) ℂ :=
  pullAddChar (Ideal.quotEquivOfEq (Ideal.span_singleton_mul_span_singleton a b))
    (sIntegerQuotientPhase K (principalizingSet S₀) (a * b) (mul_ne_zero ha hb))

theorem sourceProductPhase_mk (a b : PrincipalIntegerRing S₀) (ha : a ≠ 0) (hb : b ≠ 0)
    (x : PrincipalIntegerRing S₀) :
    sourceProductPhase S₀ a b ha hb (Ideal.Quotient.mk _ x) =
      sCharacter K (principalizingSet S₀) ((x : K) / ((a : K) * (b : K))) := by
  rw [sourceProductPhase, pullAddChar_apply, Ideal.quotEquivOfEq_mk, sIntegerQuotientPhase_mk]
  rfl

theorem sourceProductPhase_left (a b u v : PrincipalIntegerRing S₀)
    (ha : a ≠ 0) (hb : b ≠ 0) (hbez : u * a + v * b = 1) :
    leftAddChar (Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
      (principal_coprime_of_bezout hbez)) (sourceProductPhase S₀ a b ha hb) =
      (sIntegerQuotientPhase K (principalizingSet S₀) a ha).mulShift
        (Ideal.Quotient.mk (Ideal.span {a}) v) := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change sourceProductPhase S₀ a b ha hb
    ((Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
      (principal_coprime_of_bezout hbez)).symm (Ideal.Quotient.mk _ x, 0)) = _
  rw [crt_left_inverse_coordinate hbez x, sourceProductPhase_mk, AddChar.mulShift_apply,
    ← map_mul (Ideal.Quotient.mk (Ideal.span {a})) v x, sIntegerQuotientPhase_mk]
  have hbK : (b : K) ≠ 0 := fun h => hb (Subtype.ext h)
  congr 1
  change ((x : K) * (v : K) * (b : K)) / ((a : K) * (b : K)) =
    ((v : K) * (x : K)) / (a : K)
  field_simp

theorem sourceProductPhase_right (a b u v : PrincipalIntegerRing S₀)
    (ha : a ≠ 0) (hb : b ≠ 0) (hbez : u * a + v * b = 1) :
    rightAddChar (Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
      (principal_coprime_of_bezout hbez)) (sourceProductPhase S₀ a b ha hb) =
      (sIntegerQuotientPhase K (principalizingSet S₀) b hb).mulShift
        (Ideal.Quotient.mk (Ideal.span {b}) u) := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change sourceProductPhase S₀ a b ha hb
    ((Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
      (principal_coprime_of_bezout hbez)).symm (0, Ideal.Quotient.mk _ x)) = _
  rw [crt_right_inverse_coordinate hbez x, sourceProductPhase_mk, AddChar.mulShift_apply,
    ← map_mul (Ideal.Quotient.mk (Ideal.span {b})) u x, sIntegerQuotientPhase_mk]
  have haK : (a : K) ≠ 0 := fun h => ha (Subtype.ext h)
  congr 1
  change ((x : K) * (u : K) * (a : K)) / ((a : K) * (b : K)) =
    ((u : K) * (x : K)) / (b : K)
  field_simp

end
end ArtinMatthews.SIntegerQuotient

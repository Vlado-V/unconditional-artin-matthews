module

public import ArtinMatthews.EisensteinAngularIdeal
public import ArtinMatthews.FiniteFieldNormCharacter
public import ArtinMatthews.DavenportHasseSextic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Identify the genuine base cubic Jacobi sum with the chosen primary
generator, then lift that identity over arbitrary finite residue fields.
The additive character never enters the resulting Jacobi value. -/
namespace ArtinMatthews.AngularLambda
open OAI OAI.ActualEisensteinCubic OAI.CompletedGauss OAI.ConcreteTraceCRT
open scoped Classical
noncomputable section

variable (q : Ideal BaseIntegers) [q.IsMaximal] (hq : lambda ∉ q)
local instance : Field (BaseIntegers ⧸ q) := Ideal.Quotient.field q
local instance : Fintype (BaseIntegers ⧸ q) := Fintype.ofFinite _

include hq in
theorem primaryGenerator_prime_ne_zero : primaryGenerator q ≠ 0 := by
  obtain ⟨p,hp,hprim,_⟩ := cubicJacobi_exists_primary_generator q hq
  have hp0 : p ≠ 0 := by
    intro he
    have hq0 : q ≠ ⊥ := NeZero.ne q
    apply hq0
    simpa only [he,Ideal.span_singleton_zero] using hp
  rw [hp,primaryGenerator_span p hp0 hprim]
  exact hp0

def eisensteinCubicCharacter : MulChar (BaseIntegers ⧸ q) ℂ :=
  (cubicChar q hq).ringHomComp eisEmbedding

theorem eisensteinCubicCharacter_ne_one : eisensteinCubicCharacter q hq ≠ 1 :=
  (MulChar.ringHomComp_ne_one_iff eisEmbedding_injective).mpr (cubicChar_ne_one q hq)

theorem eisensteinCubicCharacter_order : orderOf (eisensteinCubicCharacter q hq) = 3 := by
  have hp : eisensteinCubicCharacter q hq ^ 3 = 1 := by
    rw [eisensteinCubicCharacter,MulChar.ringHomComp_pow,cubicChar_pow_three,MulChar.ringHomComp_one]
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp (orderOf_dvd_of_pow_eq_one hp) with h | h
  · exact False.elim (eisensteinCubicCharacter_ne_one q hq (orderOf_eq_one_iff.mp h))
  · exact h

theorem eisensteinCubicCharacter_jacobi :
    jacobiSum (eisensteinCubicCharacter q hq) (eisensteinCubicCharacter q hq) =
      -eisEmbedding (primaryGenerator q) := by
  have hspec := primaryGenerator_spec q (primaryGenerator_prime_ne_zero q hq)
  rw [eisensteinCubicCharacter,jacobiSum_ringHomComp,
    cubicJacobi_eq_neg_primary_generator_of_principal q hq (primaryGenerator q) hspec.1.symm hspec.2,
    map_neg]

theorem jacobi_lift_sign (m : ℕ) (hm : 0 < m) (z : ℂ) :
    (-1 : ℂ)^(m-1) * (-z)^m = -(z^m) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have hs : (-1 : ℂ)^k * (-1)^k = 1 := by
    rw [← mul_pow]
    norm_num
  rw [Nat.succ_eq_add_one,Nat.add_sub_cancel,neg_pow z,pow_succ (-1 : ℂ)]
  calc
    _ = -(((-1 : ℂ)^k * (-1)^k) * z^(k+1)) := by ring
    _ = _ := by rw [hs,one_mul]

variable (E : Type*) [Field E] [Fintype E] [Algebra (BaseIntegers ⧸ q) E]

theorem eisensteinCubicCharacter_lifted_jacobi :
    jacobiSum (FiniteFieldCharacter.normLift (BaseIntegers ⧸ q) E (eisensteinCubicCharacter q hq))
      (FiniteFieldCharacter.normLift (BaseIntegers ⧸ q) E (eisensteinCubicCharacter q hq)) =
      -(eisEmbedding (primaryGenerator q) ^ Module.finrank (BaseIntegers ⧸ q) E) := by
  rw [DavenportHasse.jacobiSum_norm_lift_cubic (BaseIntegers ⧸ q) E
    (eisensteinCubicCharacter q hq) (eisensteinCubicCharacter_order q hq),
    eisensteinCubicCharacter_jacobi q hq]
  exact jacobi_lift_sign _ Module.finrank_pos _

end
end ArtinMatthews.AngularLambda

module

public import ArtinMatthews.PrincipalOppositeFourier
public import ArtinMatthews.SIntegerLocalCZero
public import ArtinMatthews.SIntegerPhaseCongruence
public import ArtinMatthews.SIntegerStandardPhase
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

/-! The literal two-factor source phase and its exact lower phase.
Primitivity is derived from the actual exterior prime and codifferent. -/
namespace ArtinMatthews.SIntegerFourier

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.StandardAdelic
open scoped NumberField Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

def sourceHigherPhase (a : PrincipalIntegerRing S₀) (ha : a ≠ 0) (m n : ℕ) :
    AddChar ((PrincipalIntegerRing S₀) ⧸ Ideal.span {(a * a ^ m) * (a * a ^ n)}) ℂ :=
  sIntegerQuotientPhase K (principalizingSet S₀) ((a * a ^ m) * (a * a ^ n))
    (mul_ne_zero (mul_ne_zero ha (pow_ne_zero m ha)) (mul_ne_zero ha (pow_ne_zero n ha)))

theorem sourceHigherPhase_primitive (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ traceBadPlaces K) (m n : ℕ) :
    (sourceHigherPhase S₀ a (exterior_generator_ne_zero S₀ P a ha) m n).IsPrimitive := by
  have he : (a * a ^ m) * (a * a ^ n) = a ^ (m + n + 2) := by
    simp only [pow_add, pow_succ]
    ring
  unfold sourceHigherPhase
  exact (sourcePhase_primitive_congr S₀ _ _ _ _ he).mpr
    (sIntegerQuotientPhase_primitive S₀ P hP a ha (m + n + 2) hbad)

theorem sourceHigherPhase_lower (a : PrincipalIntegerRing S₀) (ha : a ≠ 0) (m n : ℕ) :
    oppositeLowerChar (a * a ^ m) (a * a ^ n) (sourceHigherPhase S₀ a ha m n) =
      linearPowerPhase S₀ a ha n := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [oppositeLowerChar_mk]
  change sIntegerQuotientPhase K (principalizingSet S₀) ((a * a ^ m) * (a * a ^ n)) _
    (Ideal.Quotient.mk _ ((a * a ^ m) * x)) = _
  unfold linearPowerPhase
  rw [sIntegerQuotientPhase_mk, sIntegerQuotientPhase_mk]
  have haK : (a : K) ≠ 0 := fun h => ha (Subtype.ext h)
  congr 1
  change (((a : K) * (a : K)^m) * (x : K)) /
    (((a : K) * (a : K)^m) * ((a : K) * (a : K)^n)) =
      (x : K) / ((a : K) * (a : K)^n)
  field_simp

end
end ArtinMatthews.SIntegerFourier

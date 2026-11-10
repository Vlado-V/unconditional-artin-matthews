module

public import ArtinMatthews.PositiveDensityCandidateWeights
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The fixed exceptional set in the cubic sieve is the actual finite set
of rational primes ramified in the constructed cubic Kummer field. -/

noncomputable section
namespace ArtinMatthews

open scoped NumberField

def giantCubicRamifiedPrimes (S : Finset ℤ) : Finset ℕ :=
  (NumberField.discr (integerCubicField S)).natAbs.primeFactors

theorem giantCubic_not_mem_ramifiedPrimes_iff (S : Finset ℤ) {p : ℕ} (hp : p.Prime) :
    p ∉ giantCubicRamifiedPrimes S ↔
      Algebra.IsUnramifiedIn (𝓞 (integerCubicField S)) (Ideal.span {(p : ℤ)}) := by
  have hpz : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  have hD := Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero (integerCubicField S))
  rw [← NumberField.not_dvd_discr_iff_isUnramifiedIn (integerCubicField S)
    (𝓞 (integerCubicField S)) hpz]
  simp only [giantCubicRamifiedPrimes, Nat.mem_primeFactors, hp, true_and]
  rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs]
  exact not_congr (and_iff_left hD)

theorem giantCubicSieveSelection_discr_iff {S : Finset ℤ}
    {p : ℕ} [Fact p.Prime] (D : IntegralFrobeniusData (integerCubicField S) p)
    (hp₃ : p % 3 = 1) (ha₀ : ∀ a ∈ S, (a : ZMod p) ≠ 0) :
    giantCubicSieveSelection S (giantCubicRamifiedPrimes S) p ↔
      Algebra.IsUnramifiedIn (𝓞 (integerCubicField S)) (Ideal.span {(p : ℤ)}) ∧
        relativeCubicFrobenius D hp₃ ∈ cubicNonfixingSet S := by
  rw [giantCubicSieveSelection_iff_frobenius _ D hp₃ ha₀,
    giantCubic_not_mem_ramifiedPrimes_iff S (Fact.out : p.Prime)]

def giantCubicFrobeniusSelection (S : Finset ℤ) (p : ℕ) : Prop :=
  ∃ (hp : p.Prime) (hp₃ : p % 3 = 1),
    Algebra.IsUnramifiedIn (𝓞 (integerCubicField S)) (Ideal.span {(p : ℤ)}) ∧
      ∃ D : IntegralFrobeniusData (integerCubicField S) p,
        @relativeCubicFrobenius S p ⟨hp⟩ D hp₃ ∈ cubicNonfixingSet S

theorem giantCubicFrobeniusSelection_iff {S : Finset ℤ} {p : ℕ}
    (hp : p.Prime) (hp₃ : p % 3 = 1) (ha₀ : ∀ a ∈ S, (a : ZMod p) ≠ 0) :
    giantCubicFrobeniusSelection S p ↔
      giantCubicSieveSelection S (giantCubicRamifiedPrimes S) p := by
  let : Fact p.Prime := ⟨hp⟩
  constructor
  · rintro ⟨_hp, _hp₃, hu, D, hD⟩
    exact (giantCubicSieveSelection_discr_iff D hp₃ ha₀).mpr ⟨hu, hD⟩
  · intro hs
    obtain ⟨D⟩ := exists_integralFrobeniusData (integerCubicField S) hp
    obtain ⟨hu, hD⟩ := (giantCubicSieveSelection_discr_iff D hp₃ ha₀).mp hs
    exact ⟨hp, hp₃, hu, D, hD⟩

end ArtinMatthews

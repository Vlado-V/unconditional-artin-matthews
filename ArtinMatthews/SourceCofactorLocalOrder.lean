module

public import ArtinMatthews.SourceCRTCofactorPhase
public import ArtinMatthews.SIntegerExteriorGenerator
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
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

/-! The actual omitted prime factors are units at the retained prime,
and exact ideal-power order produces an S-integer unit cofactor. -/
namespace ArtinMatthews.SourceCRTNormalization

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient
open scoped NumberField Classical BigOperators
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sourcePrimeCofactor_valuation (P : ι → HeightOneSpectrum (𝓞 K))
    (hP : Pairwise fun i j => P i ≠ P j) (hS : ∀ i, P i ∉ principalizingSet S₀)
    (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (n : ι → ℕ) (i : ι) :
    (P i).valuation K (sourcePrimeCofactor S₀ a n i : K) = 1 := by
  change (P i).valuation K (algebraMap (PrincipalIntegerRing S₀) K (sourcePrimeCofactor S₀ a n i)) = 1
  simp only [sourcePrimeCofactor, map_prod, map_pow]
  apply Finset.prod_eq_one
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  change (P i).valuation K (a j : K) ^ n j = 1
  rw [exterior_generator_other_valuation S₀ (P j) (a j) (ha j) (P i) (hS i) (hP hji.symm), one_pow]

theorem sourcePrimeCofactor_not_mem (P : ι → HeightOneSpectrum (𝓞 K))
    (hP : Pairwise fun i j => P i ≠ P j) (hS : ∀ i, P i ∉ principalizingSet S₀)
    (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (n : ι → ℕ) (i : ι) :
    sourcePrimeCofactor S₀ a n i ∉ (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) := by
  intro hm
  have hl := (principalInteger_power_mem_iff_valuation S₀ (P i) (hS i) 1
    (sourcePrimeCofactor S₀ a n i)).mp (by simpa only [pow_one] using hm)
  rw [sourcePrimeCofactor_valuation S₀ P hP hS a ha n i] at hl
  have ht : WithZero.exp (-1 : ℤ) < (1 : WithZero (Multiplicative ℤ)) := by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by norm_num)
  exact (not_le_of_gt ht) hl

theorem source_exact_order_factor (P : HeightOneSpectrum (𝓞 K)) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (J : ℕ) (H : PrincipalIntegerRing S₀)
    (hlo : H ∈ primePowerIdeal S₀ P J) (hhi : H ∉ primePowerIdeal S₀ P (J + 1)) :
    ∃ hp : PrincipalIntegerRing S₀, H = a ^ J * hp ∧
      hp ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) := by
  rw [primePowerIdeal, generator_power_ideal S₀ P a ha J, Ideal.mem_span_singleton] at hlo
  obtain ⟨hp, hH⟩ := hlo
  refine ⟨hp, hH, ?_⟩
  intro hpm
  have hd : a ∣ hp := by
    rw [← Ideal.mem_span_singleton, ← ha]
    exact hpm
  obtain ⟨z, hz⟩ := hd
  apply hhi
  rw [primePowerIdeal, generator_power_ideal S₀ P a ha (J + 1), Ideal.mem_span_singleton]
  refine ⟨z, ?_⟩
  rw [hH, hz, pow_succ']
  ring

end
end ArtinMatthews.SourceCRTNormalization

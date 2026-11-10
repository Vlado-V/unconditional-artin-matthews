module

public import ArtinMatthews.CubicThetaCoefficients
public import ArtinMatthews.QuadraticIdealNormCountGlobal
public import ArtinMatthews.QuadraticIdealNormCountPrimePower
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
public import Mathlib.RingTheory.Radical.NatInt
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

/-! Actual prime ideals of the Eisenstein field have rational prime or
prime-square norm. Consequently the residue-degree-two terms in a bounded
prime ideal sum have square-root cardinality. -/

noncomputable section
namespace ArtinMatthews
open OAI OAI.SevenEighths
open scoped BigOperators
local notation "EO" => HeckeFamily.O

theorem heckePrimeIdeal_absNorm (P : Ideal EO) (hP : Prime P) :
    ∃ p : ℕ, p.Prime ∧ (P.absNorm = p ∨ P.absNorm = p^2) := by
  let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  obtain ⟨p, n, hn, hpP, hp, hnorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
  have hdiv : p^n ∣ p^2 := by
    have h := Ideal.absNorm_dvd_absNorm_of_le
      ((Ideal.span_singleton_le_iff_mem _).mpr hpP)
    rwa [Ideal.absNorm_span_natCast, heckeRingOfIntegers_finrank_two, hnorm] at h
  have hn2 : n ≤ 2 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdiv
  refine ⟨p, hp, ?_⟩
  rcases (by omega : n = 1 ∨ n = 2) with rfl | rfl
  · exact Or.inl (by simpa only [pow_one] using hnorm)
  · exact Or.inr hnorm

theorem heckePrimeIdeal_nonprime_norm (P : Ideal EO) (hP : Prime P)
    (hnorm : ¬ P.absNorm.Prime) : ∃ p : ℕ, p.Prime ∧ P.absNorm = p^2 := by
  obtain ⟨p, hp, heq | heq⟩ := heckePrimeIdeal_absNorm P hP
  · exact False.elim (hnorm (heq ▸ hp))
  · exact ⟨p, hp, heq⟩

theorem heckePrimeIdeal_of_prime_norm (P : Ideal EO) (hp : P.absNorm.Prime) : Prime P :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (Ideal.irreducible_of_irreducible_absNorm hp)

theorem heckePrimeSquareNorm_card {p : ℕ} (hp : p.Prime) :
    (idealsOfNorm (p^2)).card ≤ 3 := by
  rw [idealsOfNorm_card_eq_idealCoefficient (pow_ne_zero 2 hp.ne_zero)]
  exact quadraticIdealCoefficient_prime_pow_le HeckeFamily.K
    heckeRingOfIntegers_finrank_two hp 2

theorem heckePrimeIdeal_residueDegreeTwo_card (S : Finset (Ideal EO)) (N : ℕ)
    (hS : ∀ P ∈ S, Prime P ∧ P.absNorm ≤ N ∧ ¬ P.absNorm.Prime) :
    S.card ≤ 3 * N.sqrt := by
  classical
  let ps := (Finset.Icc 1 N.sqrt).filter Nat.Prime
  have hsub : S ⊆ ps.biUnion (fun p => idealsOfNorm (p^2)) := by
    intro P hP
    obtain ⟨hp, hle, hnonprime⟩ := hS P hP
    obtain ⟨p, hp, hnorm⟩ := heckePrimeIdeal_nonprime_norm P hp hnonprime
    apply Finset.mem_biUnion.mpr
    refine ⟨p, ?_, mem_idealsOfNorm.mpr hnorm⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨hp.one_lt.le, Nat.le_sqrt'.mpr (hnorm ▸ hle)⟩, hp⟩
  calc
    S.card ≤ (ps.biUnion (fun p => idealsOfNorm (p^2))).card := Finset.card_le_card hsub
    _ ≤ ps.card*3 := Finset.card_biUnion_le_card_mul _ _ _
      (fun p hp => heckePrimeSquareNorm_card (Finset.mem_filter.mp hp).2)
    _ ≤ (Finset.Icc 1 N.sqrt).card*3 :=
      Nat.mul_le_mul_right 3 (Finset.card_filter_le _ _)
    _ = 3*N.sqrt := by simp [Nat.card_Icc, mul_comm]

theorem heckePrimeIdeal_residueDegreeTwo_weighted_bound
    (S : Finset (Ideal EO)) (N : ℕ) (η : HeckeFamily.Character)
    (w : Ideal EO → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hS : ∀ P ∈ S, Prime P ∧ P.absNorm ≤ N ∧ ¬ P.absNorm.Prime)
    (hw : ∀ P ∈ S, ‖w P‖ ≤ B) :
    ‖∑ P ∈ S, thetaIdealCharacter η P*w P‖ ≤ 3*(N.sqrt : ℝ)*B := by
  calc
    _ ≤ ∑ P ∈ S, ‖thetaIdealCharacter η P*w P‖ := norm_sum_le _ _
    _ ≤ ∑ _P ∈ S, B := by
      apply Finset.sum_le_sum
      intro P hP
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (thetaIdealCharacter_norm_le_one η P)
        (norm_nonneg _)).trans (by simpa only [one_mul] using hw P hP)
    _ = (S.card : ℝ)*B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast heckePrimeIdeal_residueDegreeTwo_card S N hS) hB

end ArtinMatthews

module

public import ArtinMatthews.HeckeDirichletTwist
public import OAI.NumberTheory.DirichletL.PrimeRows.NormFiberExtraction
public import ArtinMatthews.HeckePrimeResidueDegree
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Exact passage from actual ideal-prime sums to rational prime theta
coefficients, with an explicit residue-degree-two error. -/

noncomputable section
namespace ArtinMatthews
open OAI OAI.SevenEighths ConcretePrimeRowBridge
open scoped BigOperators Classical
local notation "EO" => HeckeFamily.O

theorem heckePrimeNorm_idealSum (η : HeckeFamily.Character) (N : ℕ) (w : ℕ → ℂ) :
    (∑ P ∈ (idealsUpTo N).filter (fun P => Prime P ∧ P.absNorm.Prime),
      thetaIdealCharacter η P*w P.absNorm) =
    ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, idealThetaCoeff η p*w p := by
  classical
  have hset : (idealsUpTo N).filter (fun P => Prime P ∧ P.absNorm.Prime) =
      ((Finset.Icc 1 N).filter Nat.Prime).biUnion idealsOfNorm := by
    ext P
    simp only [Finset.mem_filter, mem_idealsUpTo, Finset.mem_biUnion,
      Finset.mem_Icc, mem_idealsOfNorm]
    constructor
    · intro h
      exact ⟨P.absNorm, ⟨h.1, h.2.2⟩, rfl⟩
    · rintro ⟨p, ⟨hp, hprime⟩, hnorm⟩
      subst p
      exact ⟨hp, heckePrimeIdeal_of_prime_norm P hprime, hprime⟩
  rw [hset, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro p _
    rw [idealThetaCoeff, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro P hP
    rw [mem_idealsOfNorm.mp hP]
  · intro p _ q _ hpq
    apply Finset.disjoint_left.mpr
    intro P hp hq
    exact hpq ((mem_idealsOfNorm.mp hp).symm.trans (mem_idealsOfNorm.mp hq))

theorem heckePrimeIdealSum_sub_rationalPrimeSum (η : HeckeFamily.Character)
    (N : ℕ) (w : ℕ → ℂ) :
    (∑ P ∈ (idealsUpTo N).filter Prime, thetaIdealCharacter η P*w P.absNorm) -
      (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, idealThetaCoeff η p*w p) =
    ∑ P ∈ (idealsUpTo N).filter (fun P => Prime P ∧ ¬ P.absNorm.Prime),
      thetaIdealCharacter η P*w P.absNorm := by
  classical
  rw [← heckePrimeNorm_idealSum]
  have h := Finset.sum_filter_add_sum_filter_not
    ((idealsUpTo N).filter Prime) (fun P => P.absNorm.Prime)
    (fun P => thetaIdealCharacter η P*w P.absNorm)
  simp only [Finset.filter_filter] at h
  linear_combination -h

theorem heckePrimeIdealSum_rationalPrimeSum_error (η : HeckeFamily.Character)
    (N : ℕ) (w : ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hw : ∀ n ∈ Finset.Icc 1 N, ‖w n‖ ≤ B) :
    ‖(∑ P ∈ (idealsUpTo N).filter Prime, thetaIdealCharacter η P*w P.absNorm) -
      (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, idealThetaCoeff η p*w p)‖ ≤
      3*(N.sqrt : ℝ)*B := by
  classical
  rw [heckePrimeIdealSum_sub_rationalPrimeSum]
  apply heckePrimeIdeal_residueDegreeTwo_weighted_bound _ N η _ B hB
  · intro P hP
    have h := Finset.mem_filter.mp hP
    exact ⟨h.2.1, (mem_idealsUpTo.mp h.1).2, h.2.2⟩
  · intro P hP
    exact hw _ (Finset.mem_Icc.mpr (mem_idealsUpTo.mp (Finset.mem_filter.mp hP).1))

theorem heckeDirichletPrimeSum_error (η : HeckeFamily.Character)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (N : ℕ) (w : ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hw : ∀ n ∈ Finset.Icc 1 N, ‖w n‖ ≤ B) :
    ‖(∑ P ∈ (idealsUpTo N).filter Prime,
        thetaIdealCharacter (heckeDirichletTwist η χ) P*w P.absNorm) -
      (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, idealThetaCoeff η p*χ p*w p)‖ ≤
      3*(N.sqrt : ℝ)*B := by
  simpa only [idealThetaCoeff_heckeDirichletTwist] using
    heckePrimeIdealSum_rationalPrimeSum_error (heckeDirichletTwist η χ) N w B hB hw

end ArtinMatthews

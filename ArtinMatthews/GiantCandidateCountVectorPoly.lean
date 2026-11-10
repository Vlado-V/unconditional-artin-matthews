module

public import ArtinMatthews.GiantCandidatePointCountPoly
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The product of fixed even count polynomials expands into the exact
finite family of joint binomial tests. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

def giantCandidateCountVectors (ι : Type*) [Fintype ι] [DecidableEq ι] (a : ℕ) :
    Finset (ι → ℕ) :=
  Fintype.piFinset (fun _ : ι => range (a+1))

theorem mem_giantCandidateCountVectors {ι : Type*} [Fintype ι] [DecidableEq ι] {a : ℕ}
    {n : ι → ℕ} : n∈giantCandidateCountVectors ι a ↔ ∀ i,n i≤a := by
  simp only [giantCandidateCountVectors,Fintype.mem_piFinset,mem_range,Nat.lt_succ_iff]

def giantCandidateCountBinomialTest {ι : Type*} [Fintype ι] (k n : ι → ℕ) : ℝ :=
  ∏ i,((n i).choose (k i):ℝ)

def giantCandidateCountVectorDelta {ι : Type*} [Fintype ι] (k n : ι → ℕ) : ℝ :=
  if n=k then 1 else 0

theorem giantCandidateCountVectorDelta_eq_prod {ι : Type*} [Fintype ι] (k n : ι → ℕ) :
    giantCandidateCountVectorDelta k n = ∏ i,giantCandidatePointCountDelta (k i) (n i) := by
  classical
  unfold giantCandidateCountVectorDelta
  by_cases h : n=k
  · subst n
    simp only [giantCandidatePointCountDelta,ite_true,prod_const_one]
  · have hn : ∃ i,n i≠k i := by
      by_contra hn
      apply h
      funext i
      by_contra hi
      exact hn ⟨i,hi⟩
    obtain ⟨i,hi⟩ := hn
    rw [ite_eq_right h]
    exact (prod_eq_zero (mem_univ i) (ite_eq_right hi)).symm

def giantCandidateCountVectorPoly {ι : Type*} [Fintype ι] (k : ι → ℕ) (b : ℕ)
    (n : ι → ℕ) : ℝ :=
  ∏ i,giantCandidatePointCountPoly (k i) (2*b) (n i)

def giantCandidateCountPolyCoeff {ι : Type*} [Fintype ι] (k l : ι → ℕ) : ℝ :=
  ∏ i,(-1:ℝ)^(l i)*((k i+l i).choose (k i):ℝ)

theorem giantCandidateCountVectorPoly_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ι → ℕ) (b : ℕ) (n : ι → ℕ) :
    giantCandidateCountVectorPoly k b n =
      ∑ l∈giantCandidateCountVectors ι (2*b),giantCandidateCountPolyCoeff k l*
        giantCandidateCountBinomialTest (fun i => k i+l i) n := by
  unfold giantCandidateCountVectorPoly giantCandidatePointCountPoly
  rw [prod_univ_sum,giantCandidateCountVectors]
  apply sum_congr rfl
  intro l _
  rw [giantCandidateCountPolyCoeff,giantCandidateCountBinomialTest,← prod_mul_distrib]

def giantCandidateCountErrorSubsets (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Finset (Finset ι) :=
  (univ : Finset ι).powerset.erase ∅

def giantCandidateCountErrorOrders {ι : Type*} [DecidableEq ι] (k : ι → ℕ) (r : ℕ)
    (A : Finset ι) (i : ι) : ℕ :=
  if i∈A then k i+r else 0

def giantCandidateCountErrorCoeff {ι : Type*} (k : ι → ℕ) (r : ℕ) (A : Finset ι) : ℝ :=
  ∏ i∈A,((k i+r).choose (k i):ℝ)

theorem giantCandidateCountErrorCoeff_nonneg {ι : Type*} (k : ι → ℕ) (r : ℕ) (A : Finset ι) :
    0≤giantCandidateCountErrorCoeff k r A :=
  prod_nonneg (fun _ _ => Nat.cast_nonneg _)

theorem giantCandidateCountErrorTerm_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k n : ι → ℕ) (r : ℕ) (A : Finset ι) :
    (∏ i∈A,((k i+r).choose (k i):ℝ)*((n i).choose (k i+r):ℝ)) =
      giantCandidateCountErrorCoeff k r A*
        giantCandidateCountBinomialTest (giantCandidateCountErrorOrders k r A) n := by
  have hprod : (∏ i∈A,((n i).choose (k i+r):ℝ)) =
      giantCandidateCountBinomialTest (giantCandidateCountErrorOrders k r A) n := by
    unfold giantCandidateCountBinomialTest
    calc
      _ = ∏ i∈A,((n i).choose (giantCandidateCountErrorOrders k r A i):ℝ) := by
        apply prod_congr rfl
        intro i hi
        rw [giantCandidateCountErrorOrders,ite_eq_left hi]
      _ = _ := by
        apply prod_subset (subset_univ _)
        intro i _ hi
        simp only [giantCandidateCountErrorOrders,ite_eq_right hi,Nat.choose_zero_right,Nat.cast_one]
  rw [prod_mul_distrib,giantCandidateCountErrorCoeff,hprod]

end
end ArtinMatthews

module

public import ArtinMatthews.GiantCandidateCountMoments
public import Mathlib.CategoryTheory.Category.Basic
public import ArtinMatthews.GiantCandidateCountVectorRemainder
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Rat.Star
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

/-! Under factorial moment bounds, the first omitted mixed terms in
the exact-count approximant have a uniform factorial tail. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

def giantCandidateCountRemainderScale (C : ℝ) (a r : ℕ) : ℝ :=
  (max 1 C)^a*(C^r/(r.factorial:ℝ))

theorem giantCandidateCountRemainderScale_nonneg {C : ℝ} (hC : 0≤C) (a r : ℕ) :
    0≤giantCandidateCountRemainderScale C a r := by
  unfold giantCandidateCountRemainderScale
  have hmax : 0 ≤ max 1 C := zero_le_one.trans (le_max_left _ _)
  positivity

private theorem giantCandidateCountErrorEnvelope_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : ℝ} (hC : 0≤C) {a : ℕ} (k : ι → ℕ) (hk : ∀i,k i≤a) (r : ℕ)
    (A : Finset ι) (hA : A.Nonempty) (hR : giantCandidateCountRemainderScale C a r≤1) :
    giantCandidateCountErrorCoeff k r A*
      giantCandidateMomentEnvelope C (giantCandidateCountErrorOrders k r A) ≤
        giantCandidateCountRemainderScale C a r := by
  let R := giantCandidateCountRemainderScale C a r
  have hR₀ : 0≤R := giantCandidateCountRemainderScale_nonneg hC a r
  have henv : giantCandidateMomentEnvelope C (giantCandidateCountErrorOrders k r A) =
      ∏ i∈A,C^(k i+r)/((k i+r).factorial:ℝ) := by
    unfold giantCandidateMomentEnvelope
    symm
    calc
      _ = ∏ i∈A,C^(giantCandidateCountErrorOrders k r A i)/
          ((giantCandidateCountErrorOrders k r A i).factorial:ℝ) := by
        apply prod_congr rfl
        intro i hi
        rw [giantCandidateCountErrorOrders,ite_eq_left hi]
      _ = _ := by
        apply prod_subset (subset_univ _)
        intro i _ hi
        simp only [giantCandidateCountErrorOrders,ite_eq_right hi,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one]
  have hfactor (i : ι) : (C^(k i)/((k i).factorial:ℝ))*(C^r/(r.factorial:ℝ))≤R := by
    have hfac : (1:ℝ)≤(k i).factorial := by exact_mod_cast Nat.factorial_pos (k i)
    apply mul_le_mul_of_nonneg_right _ (by positivity : 0≤C^r/(r.factorial:ℝ))
    calc
      _ ≤ C^(k i) := div_le_self (pow_nonneg hC _) hfac
      _ ≤ (max 1 C)^(k i) := pow_le_pow_left₀ hC (le_max_right _ _) _
      _ ≤ _ := pow_le_pow_right₀ (le_max_left _ _) (hk i)
  calc
    _ = ∏ i∈A,(C^(k i)/((k i).factorial:ℝ))*(C^r/(r.factorial:ℝ)) := by
      rw [giantCandidateCountErrorCoeff,henv,← prod_mul_distrib]
      exact prod_congr rfl (fun i _ => giantCandidateBinomialFactorial_error C (k i) r)
    _ ≤ ∏ _i∈A,R := prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => hfactor i)
    _ = R^A.card := prod_const _
    _ ≤ R := by
      obtain ⟨s,hs⟩ := Nat.exists_eq_succ_of_ne_zero (card_pos.mpr hA).ne'
      rw [hs,pow_succ]
      exact mul_le_of_le_one_left hR₀ (pow_le_one₀ hR₀ hR)

theorem giantCandidateCountVectorMeanPoly_error {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset Ω) (N : Ω → ι → ℕ) {C : ℝ} (hC : 0≤C)
    {a : ℕ} (k : ι → ℕ) (hk : ∀i,k i≤a) (b : ℕ)
    (hR : giantCandidateCountRemainderScale C a (2*b+1)≤1)
    (hMom : ∀ A∈giantCandidateCountErrorSubsets ι,
      giantCandidateCountMoment S N (giantCandidateCountErrorOrders k (2*b+1) A) ≤
        2*giantCandidateMomentEnvelope C (giantCandidateCountErrorOrders k (2*b+1) A)) :
    |(𝔼 t∈S,giantCandidateCountVectorDelta k (N t))-
      (𝔼 t∈S,giantCandidateCountVectorPoly k b (N t))| ≤
        2*(2:ℝ)^Fintype.card ι*giantCandidateCountRemainderScale C a (2*b+1) := by
  let r := 2*b+1
  let R := giantCandidateCountRemainderScale C a r
  let D := giantCandidateCountErrorSubsets ι
  have hR₀ : 0≤R := giantCandidateCountRemainderScale_nonneg hC a r
  have hlo : (𝔼 t∈S,giantCandidateCountVectorDelta k (N t)) ≤
      𝔼 t∈S,giantCandidateCountVectorPoly k b (N t) :=
    expect_le_expect (fun t _ => (giantCandidateCountVectorPoly_bounds k b (N t)).1)
  have hhi : (𝔼 t∈S,giantCandidateCountVectorPoly k b (N t)) ≤
      (𝔼 t∈S,giantCandidateCountVectorDelta k (N t))+
        ∑ A∈D,giantCandidateCountErrorCoeff k r A*
          giantCandidateCountMoment S N (giantCandidateCountErrorOrders k r A) := by
    have h := expect_le_expect (s:=S) (fun t _ => (giantCandidateCountVectorPoly_bounds k b (N t)).2)
    simpa only [expect_add_distrib,expect_sum_comm,← mul_expect,giantCandidateCountMoment] using h
  have hsum : (∑ A∈D,giantCandidateCountErrorCoeff k r A*
      giantCandidateCountMoment S N (giantCandidateCountErrorOrders k r A)) ≤ 2*(2:ℝ)^Fintype.card ι*R := by
    calc
      _ ≤ ∑ _A∈D,2*R := by
        apply sum_le_sum
        intro A hA
        have hA₀ : A.Nonempty := nonempty_iff_ne_empty.mpr (mem_erase.mp hA).1
        have hcoef := giantCandidateCountErrorCoeff_nonneg k r A
        calc
          _ ≤ giantCandidateCountErrorCoeff k r A*
                (2*giantCandidateMomentEnvelope C (giantCandidateCountErrorOrders k r A)) :=
            mul_le_mul_of_nonneg_left (hMom A hA) hcoef
          _ = 2*(giantCandidateCountErrorCoeff k r A*
                giantCandidateMomentEnvelope C (giantCandidateCountErrorOrders k r A)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (giantCandidateCountErrorEnvelope_le hC k hk r A hA₀ hR) (by norm_num)
      _ = (D.card:ℝ)*(2*R) := by rw [sum_const,nsmul_eq_mul]
      _ ≤ (2:ℝ)^Fintype.card ι*(2*R) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast (calc
          D.card ≤ (univ : Finset ι).powerset.card := card_le_card (erase_subset _ _)
          _ = 2^Fintype.card ι := by rw [card_powerset,card_univ])
      _ = _ := by ring
  rw [abs_of_nonpos (sub_nonpos.mpr hlo)]
  linarith only [hhi,hsum]

end
end ArtinMatthews

module

public import ArtinMatthews.GiantCandidateSelectionPrimeMask
public import ArtinMatthews.GiantCandidatePrimeResidueModel
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

/-! The literal rough-box binomial moment is a sum of selected-prime
event masses. The independent model uses the same selections. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

def giantCandidateBoxBinomialMoment {ι : Type*} [Fintype ι] {j : ℕ}
    (S : Fin j → Finset ℕ) (G : ι → Finset ℕ)
    (side : ι → GiantCandidateHitSide) (k : ι → ℕ) : ℝ :=
  (∑ t∈Fintype.piFinset S,
    ∏ i,(Nat.choose (giantCandidateHitSet (G i) (side i) (∏ v,t v)).card (k i):ℝ))/
      ((Fintype.piFinset S).card:ℝ)

def giantCandidateModelBinomialMoment {ι : Type*} [Fintype ι] (j : ℕ)
    (G : ι → Finset ℕ) (side : ι → GiantCandidateHitSide) (k : ι → ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) : ℝ :=
  ∑ D : giantCandidateHitSelections G k,
    ∏ p : giantCandidateSelectionPrimes D.val,
      ((giantCandidateSelectionPrimeMask D.val side
        (giantCandidateSelectionPrimes_prime D.property hG) j p).card:ℝ)/(p.val:ℝ)^j

theorem giantCandidateBoxBinomialMoment_eq_selected {ι : Type*} [Fintype ι] {j : ℕ}
    (S : Fin j → Finset ℕ) (G : ι → Finset ℕ)
    (side : ι → GiantCandidateHitSide) (k : ι → ℕ)
    (hG : ∀ i p,p∈G i → p.Prime)
    (hS : ∀ t∈Fintype.piFinset S,0<∏ v,t v) :
    giantCandidateBoxBinomialMoment S G side k =
      ∑ D : giantCandidateHitSelections G k,
        ((giantCandidatePrimeTupleMask S (giantCandidateSelectionPrimeMask D.val side
          (giantCandidateSelectionPrimes_prime D.property hG) j)).card:ℝ)/
        ((Fintype.piFinset S).card:ℝ) := by
  classical
  let T := Fintype.piFinset S
  let E := giantCandidateHitSelections G k
  let F (D : ι → Finset ℕ) (t : Fin j → ℕ) :=
    ∀ i,D i ⊆ giantCandidateHitSet (G i) (side i) (∏ v,t v)
  unfold giantCandidateBoxBinomialMoment
  simp_rw [giantCandidateHitBinomials_eq_selection_sum]
  change (∑ t∈T,∑ D∈E,if F D t then (1:ℝ) else 0)/(T.card:ℝ) = _
  rw [sum_comm,sum_div,← sum_coe_sort]
  apply sum_congr rfl
  intro D _
  let hP := giantCandidateSelectionPrimes_prime D.property hG
  have he : T.filter (F D.val) =
      giantCandidatePrimeTupleMask S (giantCandidateSelectionPrimeMask D.val side hP j) := by
    ext t
    simp only [giantCandidatePrimeTupleMask,mem_filter]
    exact and_congr_right (fun ht => giantCandidateSelectedHits_iff_primeMask D.property side hP t (hS t ht))
  rw [← sum_filter,sum_const,nsmul_eq_mul,mul_one,he]

end
end ArtinMatthews

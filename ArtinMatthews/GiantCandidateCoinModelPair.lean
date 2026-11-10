module

public import ArtinMatthews.GiantCandidateCoinModel
public import ArtinMatthews.GiantCandidateModelSplit
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

/-! The model coin means of two disjoint actual groups factor exactly,
using the literal independent residue carriers. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

def giantCandidateTwoBands (P Q : Finset ℕ) (i : Fin 2) : Finset ℕ :=
  if i=0 then P else Q

theorem giantCandidateTwoBands_zero (P Q : Finset ℕ) : giantCandidateTwoBands P Q 0=P :=
  ite_eq_left rfl

theorem giantCandidateTwoBands_one (P Q : Finset ℕ) : giantCandidateTwoBands P Q 1=Q :=
  ite_eq_right (by decide)

theorem giantCandidateSingleModelPrimes (P : Finset ℕ) :
    giantCandidateSelectionPrimes (giantCandidateCoinModelBands (fun _ : Fin 1 => P)) = P := by
  ext p
  rw [mem_giantCandidateSelectionPrimes]
  constructor
  · rintro ⟨i,hi⟩
    exact hi
  · intro hp
    exact ⟨(0,true),hp⟩

theorem giantCandidatePairModelPrimes (P Q : Finset ℕ) :
    giantCandidateSelectionPrimes (giantCandidateCoinModelBands (giantCandidateTwoBands P Q)) =
      P∪Q := by
  ext p
  rw [mem_giantCandidateSelectionPrimes,mem_union]
  constructor
  · rintro ⟨i,hi⟩
    change p∈(if i.1=0 then P else Q) at hi
    split_ifs at hi with h
    · exact Or.inl hi
    · exact Or.inr hi
  · rintro (hp | hq)
    · exact ⟨(0,true),giantCandidateTwoBands_zero P Q ▸ hp⟩
    · exact ⟨(1,true),giantCandidateTwoBands_one P Q ▸ hq⟩

theorem giantCandidatePairModelCoinMean_eq (P Q : Finset ℕ)
    (hP : ∀ p∈P,p.Prime) (hQ : ∀ p∈Q,p.Prime) (hd : Disjoint P Q)
    (hG : ∀ i p,p∈giantCandidateCoinModelBands (giantCandidateTwoBands P Q) i → p.Prime)
    (c q : ℝ) (j : ℕ) :
    (𝔼 t∈giantCandidateModelResidueTuples (giantCandidateCoinModelBands (giantCandidateTwoBands P Q)) hG j,
      giantCandidateCoinModelValue (giantCandidateTwoBands P Q) c q j 0 t*
        giantCandidateCoinModelValue (giantCandidateTwoBands P Q) c q j 1 t) =
      giantCandidateSingleModelCoinMean P hP c q j*giantCandidateSingleModelCoinMean Q hQ c q j := by
  let A := giantCandidateTwoBands P Q
  let B : Fin 1 → Finset ℕ := fun _ => P
  let C : Fin 1 → Finset ℕ := fun _ => Q
  let G := giantCandidateCoinModelBands A
  let D := giantCandidateCoinModelBands B
  let E := giantCandidateCoinModelBands C
  have h : giantCandidateSelectionPrimes G =
      giantCandidateSelectionPrimes D∪giantCandidateSelectionPrimes E := by
    exact (giantCandidatePairModelPrimes P Q).trans (congrArg₂ (· ∪ ·)
      (giantCandidateSingleModelPrimes P).symm (giantCandidateSingleModelPrimes Q).symm)
  have hDis : Disjoint (giantCandidateSelectionPrimes D) (giantCandidateSelectionPrimes E) :=
    (giantCandidateSingleModelPrimes P).symm ▸ (giantCandidateSingleModelPrimes Q).symm ▸ hd
  let f := giantCandidateCoinModelValue B c q j 0
  let g := giantCandidateCoinModelValue C c q j 0
  let R₁ := giantCandidateModelRestrict G D (giantCandidateModelSubfamily_left h) (j:=j)
  let R₂ := giantCandidateModelRestrict G E (giantCandidateModelSubfamily_right h) (j:=j)
  have h₁ (t : GiantCandidateModelResidueSpace G j) :
      giantCandidateCoinModelValue A c q j 0 t = f (R₁ t) :=
    giantCandidateCoinModelValue_restrict A B (giantCandidateModelSubfamily_left h) c q j
      0 0 (giantCandidateTwoBands_zero P Q) t
  have h₂ (t : GiantCandidateModelResidueSpace G j) :
      giantCandidateCoinModelValue A c q j 1 t = g (R₂ t) :=
    giantCandidateCoinModelValue_restrict A C (giantCandidateModelSubfamily_right h) c q j
      1 0 (giantCandidateTwoBands_one P Q) t
  change (𝔼 t∈giantCandidateModelResidueTuples G hG j,
    giantCandidateCoinModelValue A c q j 0 t*giantCandidateCoinModelValue A c q j 1 t) = _
  simp_rw [h₁,h₂]
  exact giantCandidateModelResidueMean_mul_eq G D E h hDis hG (fun _ => hP) (fun _ => hQ) j f g

end
end ArtinMatthews

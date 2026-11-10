module

public import ArtinMatthews.GiantCandidateModelMomentRealization
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

/-! Restrict a full residue model to the actual primes of a subfamily.
Each group's literal hit set is unchanged under this restriction. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

def giantCandidateModelRestrict {ι κ : Type*} [Fintype ι] [Fintype κ]
    (G : ι → Finset ℕ) (D : κ → Finset ℕ)
    (h : giantCandidateSelectionPrimes D ⊆ giantCandidateSelectionPrimes G) {j : ℕ}
    (t : GiantCandidateModelResidueSpace G j) : GiantCandidateModelResidueSpace D j :=
  fun p => t ⟨p.val,h p.property⟩

theorem giantCandidateModelResidueTuples_mem {ι : Type*} [Fintype ι]
    (G : ι → Finset ℕ) (hG : ∀ i p,p∈G i → p.Prime) (j : ℕ)
    (t : GiantCandidateModelResidueSpace G j) :
    t∈giantCandidateModelResidueTuples G hG j :=
  Fintype.mem_piFinset.mpr (fun p => giantCandidateModelPrimeCoordinate_mem G hG j p (t p))

theorem giantCandidateModelHitSet_restrict {ι κ : Type*} [Fintype ι] [Fintype κ]
    (G : ι → Finset ℕ) (D : κ → Finset ℕ)
    (h : giantCandidateSelectionPrimes D ⊆ giantCandidateSelectionPrimes G)
    (side : ι → GiantCandidateHitSide) (side' : κ → GiantCandidateHitSide)
    (i : ι) (l : κ) (hgroup : G i = D l) (hside : side i=side' l)
    {j : ℕ} (t : GiantCandidateModelResidueSpace G j) :
    giantCandidateModelHitSet G side t i =
      giantCandidateModelHitSet D side' (giantCandidateModelRestrict G D h t) l := by
  ext p
  by_cases hp : p∈G i
  · have hp' : p∈D l := hgroup ▸ hp
    let p₁ : giantCandidateSelectionPrimes G := ⟨p,mem_giantCandidateSelectionPrimes.mpr ⟨i,hp⟩⟩
    let p₂ : giantCandidateSelectionPrimes D := ⟨p,mem_giantCandidateSelectionPrimes.mpr ⟨l,hp'⟩⟩
    change p₁.val∈giantCandidateModelHitSet G side t i ↔
      p₂.val∈giantCandidateModelHitSet D side' (giantCandidateModelRestrict G D h t) l
    rw [mem_giantCandidateModelHitSet,mem_giantCandidateModelHitSet]
    have he : giantCandidateModelRestrict G D h t p₂ = t p₁ := rfl
    rw [he,hside]
    exact and_congr_left (fun _ => by change p∈G i ↔ p∈D l; rw [hgroup])
  · have hp' : p∉D l := by simpa only [hgroup] using hp
    exact iff_of_false
      (fun hm => hp (giantCandidateModelHitSet_subset G side t i hm))
      (fun hm => hp' (giantCandidateModelHitSet_subset D side' (giantCandidateModelRestrict G D h t) l hm))

theorem giantCandidateModelHitCounts_restrict {ι κ : Type*} [Fintype ι] [Fintype κ]
    (G : ι → Finset ℕ) (D : κ → Finset ℕ)
    (h : giantCandidateSelectionPrimes D ⊆ giantCandidateSelectionPrimes G)
    (side : ι → GiantCandidateHitSide) (side' : κ → GiantCandidateHitSide)
    (i : ι) (l : κ) (hgroup : G i = D l) (hside : side i=side' l)
    {j : ℕ} (t : GiantCandidateModelResidueSpace G j) :
    giantCandidateModelHitCounts G side t i =
      giantCandidateModelHitCounts D side' (giantCandidateModelRestrict G D h t) l :=
  congrArg Finset.card (giantCandidateModelHitSet_restrict G D h side side' i l hgroup hside t)

end
end ArtinMatthews

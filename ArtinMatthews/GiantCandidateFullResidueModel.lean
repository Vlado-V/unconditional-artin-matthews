module

public import ArtinMatthews.GiantCandidateHitSelections
public import Mathlib.Data.Nat.Prime.Defs
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

/-! The independent model chooses a full ordered residue vector at each
prime in the union of the tested groups. The residue rings stay literal. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

abbrev GiantCandidateModelResidueSpace {ι : Type*} [Fintype ι]
    (G : ι → Finset ℕ) (j : ℕ) :=
  (p : giantCandidateSelectionPrimes G) → Fin j → ZMod p.val

private theorem giantCandidateModelPrime_neZero {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) (p : giantCandidateSelectionPrimes G) : NeZero p.val := by
  obtain ⟨i,hi⟩ := mem_giantCandidateSelectionPrimes.mp p.property
  exact ⟨(hG i p.val hi).ne_zero⟩

def giantCandidateModelPrimeCoordinate {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) (j : ℕ)
    (p : giantCandidateSelectionPrimes G) : Finset (Fin j → ZMod p.val) := by
  letI : NeZero p.val := giantCandidateModelPrime_neZero G hG p
  exact univ

theorem giantCandidateModelPrimeCoordinate_mem {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) (j : ℕ)
    (p : giantCandidateSelectionPrimes G) (t : Fin j → ZMod p.val) :
    t∈giantCandidateModelPrimeCoordinate G hG j p := by
  let _ : NeZero p.val := giantCandidateModelPrime_neZero G hG p
  change t ∈ (univ : Finset (Fin j → ZMod p.val))
  exact mem_univ _

theorem giantCandidateModelPrimeCoordinate_card {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) (j : ℕ)
    (p : giantCandidateSelectionPrimes G) :
    (giantCandidateModelPrimeCoordinate G hG j p).card = p.val^j := by
  let _ : NeZero p.val := giantCandidateModelPrime_neZero G hG p
  change (univ : Finset (Fin j → ZMod p.val)).card = _
  rw [card_univ,Fintype.card_fun,Fintype.card_fin,ZMod.card]

def giantCandidateModelResidueTuples {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) (j : ℕ) : Finset (GiantCandidateModelResidueSpace G j) :=
  Fintype.piFinset (giantCandidateModelPrimeCoordinate G hG j)

theorem giantCandidateModelResidueTuples_card {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) (j : ℕ) :
    (giantCandidateModelResidueTuples G hG j).card = ∏ p : giantCandidateSelectionPrimes G,p.val^j := by
  simp only [giantCandidateModelResidueTuples,Fintype.card_piFinset,giantCandidateModelPrimeCoordinate_card]

theorem giantCandidateModelResidueTuples_nonempty {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) (j : ℕ) :
    (giantCandidateModelResidueTuples G hG j).Nonempty :=
  ⟨fun _ _ => 0,Fintype.mem_piFinset.mpr (fun p => giantCandidateModelPrimeCoordinate_mem G hG j p _)⟩

def giantCandidateModelHitSet {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (side : ι → GiantCandidateHitSide) {j : ℕ} (t : GiantCandidateModelResidueSpace G j)
    (i : ι) : Finset ℕ := by
  classical
  exact (G i).filter (fun p => ∃ hp : p∈giantCandidateSelectionPrimes G,
    giantCandidatePrimeResidueHit (side i) (t ⟨p,hp⟩))

theorem giantCandidateModelHitSet_subset {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (side : ι → GiantCandidateHitSide) {j : ℕ} (t : GiantCandidateModelResidueSpace G j)
    (i : ι) : giantCandidateModelHitSet G side t i ⊆ G i :=
  filter_subset _ _

theorem mem_giantCandidateModelHitSet {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (side : ι → GiantCandidateHitSide) {j : ℕ} (t : GiantCandidateModelResidueSpace G j)
    (i : ι) (p : giantCandidateSelectionPrimes G) :
    p.val∈giantCandidateModelHitSet G side t i ↔
      p.val∈G i ∧ giantCandidatePrimeResidueHit (side i) (t p) := by
  simp only [giantCandidateModelHitSet,mem_filter]
  constructor
  · rintro ⟨hg,hp,ht⟩
    exact ⟨hg,ht⟩
  · rintro ⟨hg,ht⟩
    exact ⟨hg,p.property,ht⟩

end
end ArtinMatthews

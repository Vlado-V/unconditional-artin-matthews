module

public import ArtinMatthews.GiantCandidatePrimeHits
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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


set_option backward.privateInPublic true
@[expose] public section

/-! A product of binomial hit counts lists literal fixed-cardinality
subsets of the groups. Their union has at most the fixed total order. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

def giantCandidateHitSet (G : Finset ℕ) (side : GiantCandidateHitSide) (v : ℕ) : Finset ℕ :=
  G.filter (fun p => giantCandidatePrimeHit side p v)

def giantCandidateHitSelections {ι : Type*} [Fintype ι]
    (G : ι → Finset ℕ) (k : ι → ℕ) : Finset (ι → Finset ℕ) := by
  classical
  exact Fintype.piFinset (fun i => (G i).powersetCard (k i))

theorem mem_giantCandidateHitSelections {ι : Type*} [Fintype ι]
    {G : ι → Finset ℕ} {k : ι → ℕ} {D : ι → Finset ℕ} :
    D∈giantCandidateHitSelections G k ↔ ∀ i,D i ⊆ G i ∧ (D i).card=k i := by
  classical
  simp only [giantCandidateHitSelections,Fintype.mem_piFinset,mem_powersetCard]

def giantCandidateSelectionPrimes {ι : Type*} [Fintype ι] (D : ι → Finset ℕ) : Finset ℕ :=
  univ.biUnion D

theorem mem_giantCandidateSelectionPrimes {ι : Type*} [Fintype ι]
    {D : ι → Finset ℕ} {p : ℕ} :
    p∈giantCandidateSelectionPrimes D ↔ ∃ i,p∈D i := by
  simp only [giantCandidateSelectionPrimes,mem_biUnion,mem_univ,true_and]

theorem giantCandidateSelectionPrimes_subset {ι : Type*} [Fintype ι]
    {G : ι → Finset ℕ} {k : ι → ℕ} {D : ι → Finset ℕ}
    (hD : D∈giantCandidateHitSelections G k) {P : Finset ℕ} (hG : ∀ i,G i ⊆ P) :
    giantCandidateSelectionPrimes D ⊆ P := by
  intro p hp
  obtain ⟨i,hi⟩ := mem_giantCandidateSelectionPrimes.mp hp
  exact hG i ((mem_giantCandidateHitSelections.mp hD i).1 hi)

theorem giantCandidateSelectionPrimes_card_le {ι : Type*} [Fintype ι]
    {G : ι → Finset ℕ} {k : ι → ℕ} {D : ι → Finset ℕ}
    (hD : D∈giantCandidateHitSelections G k) :
    (giantCandidateSelectionPrimes D).card ≤ ∑ i,k i := by
  calc
    _ ≤ ∑ i,(D i).card := card_biUnion_le
    _ = _ := sum_congr rfl (fun i _ => (mem_giantCandidateHitSelections.mp hD i).2)

theorem giantCandidateHitBinomials_eq_selection_sum {ι : Type*} [Fintype ι]
    (G : ι → Finset ℕ) (side : ι → GiantCandidateHitSide) (k : ι → ℕ) (v : ℕ) :
    (∏ i,(Nat.choose (giantCandidateHitSet (G i) (side i) v).card (k i):ℝ)) =
      ∑ D∈giantCandidateHitSelections G k,
        if ∀ i,D i ⊆ giantCandidateHitSet (G i) (side i) v then (1:ℝ) else 0 := by
  classical
  let H (i : ι) := giantCandidateHitSet (G i) (side i) v
  let T := Fintype.piFinset (fun i => (H i).powersetCard (k i))
  let S := (giantCandidateHitSelections G k).filter (fun D => ∀ i,D i ⊆ H i)
  have he : S=T := by
    ext D
    simp only [S,T,mem_filter,mem_giantCandidateHitSelections,Fintype.mem_piFinset,mem_powersetCard]
    constructor
    · rintro ⟨hG,hH⟩ i
      exact ⟨hH i,(hG i).2⟩
    · intro hH
      exact ⟨fun i => ⟨(hH i).1.trans (filter_subset _ _),(hH i).2⟩,fun i => (hH i).1⟩
  change (∏ i,(Nat.choose (H i).card (k i):ℝ)) =
    ∑ D∈giantCandidateHitSelections G k,if ∀ i,D i ⊆ H i then (1:ℝ) else 0
  calc
    _ = (T.card:ℝ) := by
      rw [Fintype.card_piFinset,Nat.cast_prod]
      apply prod_congr rfl
      intro i _
      rw [card_powersetCard]
    _ = (S.card:ℝ) := by rw [he]
    _ = _ := by rw [← sum_filter,sum_const,nsmul_eq_mul,mul_one]

end
end ArtinMatthews

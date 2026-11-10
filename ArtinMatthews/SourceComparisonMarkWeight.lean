module

public import ArtinMatthews.MarkedArrayEulerModel
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
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The ordered distinct lists in the ordinary comparison endpoint.
The actual reciprocal masses and every zero-length group are retained. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

variable {G : Type*} [Fintype G]

def sourceComparisonMarkChoices (P : G → Finset ℕ) (t : G → ℕ) :
    Finset ((g : G) → Fin (t g) → ℕ) := by
  classical
  exact (representedArrayChoices P t).filter (fun l => ∀ g, Function.Injective (l g))

theorem mem_sourceComparisonMarkChoices (P : G → Finset ℕ) (t : G → ℕ)
    (l : (g : G) → Fin (t g) → ℕ) :
    l ∈ sourceComparisonMarkChoices P t ↔
      (∀ g i, l g i ∈ P g) ∧ ∀ g, Function.Injective (l g) := by
  classical
  simp only [sourceComparisonMarkChoices, mem_filter, representedArrayChoices, Fintype.mem_piFinset]

def sourceComparisonMarkMass (P : G → Finset ℕ) (t : G → ℕ) : ℝ :=
  ∏ g, (bandReciprocalMass (P g)) ^ t g

def sourceComparisonMarkHitDamping (P : G → Finset ℕ) (t : G → ℕ) (q : G → ℝ) (n : ℕ) : ℝ :=
  ∏ g, (q g) ^ (bandCount (P g) n - t g)

def sourceComparisonMarkWeight (P : G → Finset ℕ) (t : G → ℕ) (q : G → ℝ)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ) (n : ℕ) : ℂ :=
  (sourceComparisonMarkHitDamping P t q n : ℂ) *
    (∑ l ∈ sourceComparisonMarkChoices (fun g => activeDivisors (P g) n) t, b l) /
      (sourceComparisonMarkMass P t : ℂ)

def sourceComparisonMarkCoefficient (P : G → Finset ℕ) (t : G → ℕ)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ) (l : (g : G) → Fin (t g) → ℕ) : ℂ :=
  b l / (sourceComparisonMarkMass P t : ℂ)

def sourceComparisonMarkResidualDamping (P : G → Finset ℕ) (q : G → ℝ) (p : ℕ) : ℝ :=
  ∑ g, if p ∈ P g then 1 - q g else 0

theorem sourceComparisonMarkResidualDamping_on_band (P : G → Finset ℕ) (q : G → ℝ)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j)) {g : G} {p : ℕ} (hp : p ∈ P g) :
    sourceComparisonMarkResidualDamping P q p = 1 - q g := by
  classical
  unfold sourceComparisonMarkResidualDamping
  rw [sum_eq_single g]
  · exact ite_eq_left hp
  · intro j _ hj
    exact ite_eq_right (fun h => disjoint_left.mp (hdis hj) h hp)
  · simp

theorem sourceComparisonMarkResidualDamping_bounds (P : G → Finset ℕ) (q : G → ℝ)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    (hq : ∀ g, 0 ≤ q g ∧ q g ≤ 1) {p : ℕ} (hp : p ∈ univ.biUnion P) :
    0 ≤ sourceComparisonMarkResidualDamping P q p ∧ sourceComparisonMarkResidualDamping P q p ≤ 1 := by
  obtain ⟨g, _, hg⟩ := mem_biUnion.mp hp
  rw [sourceComparisonMarkResidualDamping_on_band P q hdis hg]
  exact ⟨sub_nonneg.mpr (hq g).2, sub_le_self _ (hq g).1⟩

theorem sourceComparisonMarkChoices_active_filter (P : G → Finset ℕ) (t : G → ℕ) (n : ℕ) :
    sourceComparisonMarkChoices (fun g => activeDivisors (P g) n) t =
      (sourceComparisonMarkChoices P t).filter (fun l => ∀ g i, l g i ∣ n) := by
  classical
  ext l
  simp only [mem_filter, mem_sourceComparisonMarkChoices, activeDivisors]
  constructor
  · rintro ⟨hm, hi⟩
    exact ⟨⟨fun g i => (hm g i).1, hi⟩,
      fun g i => (hm g i).2⟩
  · rintro ⟨⟨hm, hi⟩, hd⟩
    exact ⟨fun g i => ⟨hm g i, hd g i⟩, hi⟩

theorem sourceComparisonMarkChoices_selected_subset (P : G → Finset ℕ) (t : G → ℕ)
    {l : (g : G) → Fin (t g) → ℕ} (hl : l ∈ sourceComparisonMarkChoices P t) :
    representedArraySelected l ⊆ univ.biUnion P := by
  classical
  intro p hp
  obtain ⟨g, hg, hp'⟩ := mem_biUnion.mp hp
  exact mem_biUnion.mpr ⟨g, hg,
    representedChoiceSet_subset (((mem_sourceComparisonMarkChoices P t l).mp hl).1 g) hp'⟩

private theorem residual_band_damping (P S : Finset ℕ) (u : ℕ) (q : ℝ)
    (hS : S ⊆ activeDivisors P u) :
    (∏ p ∈ P \ S, (1 - (1 - q) * (if p ∣ u then 1 else 0))) =
      q ^ (bandCount P u - S.card) := by
  classical
  have he (p : ℕ) : 1 - (1 - q) * (if p ∣ u then 1 else 0) =
      if p ∣ u then q else 1 := by split_ifs <;> ring
  have hf : (P \ S).filter (fun p => p ∣ u) = activeDivisors P u \ S := by
    ext p
    simp [activeDivisors, and_assoc, and_left_comm, and_comm]
  calc
    _ = ∏ p ∈ P \ S, (if p ∣ u then q else 1) := prod_congr rfl (fun p _ => he p)
    _ = _ := by rw [← prod_filter, hf, prod_const, card_sdiff_of_subset hS, bandCount]

theorem sourceComparisonMarkResidual_eq (P : G → Finset ℕ) (t : G → ℕ) (q : G → ℝ)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    {l : (g : G) → Fin (t g) → ℕ} (hl : l ∈ sourceComparisonMarkChoices P t) (n : ℕ) :
    markedWeightedResidual (univ.biUnion P) (representedArraySelected l)
      (sourceComparisonMarkResidualDamping P q) n =
      if ∀ g i, l g i ∣ n then sourceComparisonMarkHitDamping P t q n else 0 := by
  classical
  let S (g : G) := representedChoiceSet (l g)
  obtain ⟨hm, hi⟩ := (mem_sourceComparisonMarkChoices P t l).mp hl
  have hS (g : G) : S g ⊆ P g := representedChoiceSet_subset (hm g)
  have hs : representedArraySelected l ⊆ activeDivisors (univ.biUnion P) n ↔
      ∀ g i, l g i ∣ n := by
    change univ.biUnion S ⊆ activeDivisors (univ.biUnion P) n ↔ _
    rw [selected_union_active_iff univ P S (fun g _ => hS g)]
    simp only [mem_univ, true_implies, S, representedChoiceSet_active_iff (hm _)]
  unfold markedWeightedResidual
  rw [if_congr hs rfl rfl]
  split_ifs with hn <;> try rfl
  rw [show representedArraySelected l = univ.biUnion S from rfl,
    disjoint_bands_residual_union univ P S (fun _ _ _ _ hij => hdis hij) (fun g _ => hS g)]
  have hds : Set.PairwiseDisjoint (↑(univ : Finset G)) (fun g => P g \ S g) :=
    fun _ _ _ _ hij => (hdis hij).mono sdiff_subset sdiff_subset
  rw [prod_biUnion hds]
  unfold sourceComparisonMarkHitDamping
  apply prod_congr rfl
  intro g _
  have hcard : (S g).card = t g := by
    unfold S representedChoiceSet
    rw [card_image_of_injective _ (hi g), card_univ, Fintype.card_fin]
  rw [← hcard]
  refine Eq.trans (prod_congr rfl (fun p hp => ?_))
    (residual_band_damping (P g) (S g) n (q g) ((representedChoiceSet_active_iff (hm g) n).mpr (hn g)))
  rw [markedWeightedInput, sourceComparisonMarkResidualDamping_on_band P q hdis (mem_sdiff.mp hp).1]

theorem sourceComparisonMarkWeight_eq_residual (P : G → Finset ℕ) (t : G → ℕ) (q : G → ℝ)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ) (n : ℕ) :
    sourceComparisonMarkWeight P t q b n =
      ∑ l ∈ sourceComparisonMarkChoices P t, sourceComparisonMarkCoefficient P t b l *
        (markedWeightedResidual (univ.biUnion P) (representedArraySelected l)
          (sourceComparisonMarkResidualDamping P q) n : ℂ) := by
  classical
  unfold sourceComparisonMarkWeight sourceComparisonMarkCoefficient
  rw [sourceComparisonMarkChoices_active_filter, sum_filter, mul_sum, sum_div]
  apply sum_congr rfl
  intro l hl
  rw [sourceComparisonMarkResidual_eq P t q hdis hl]
  split_ifs
  · ring
  · simp

end
end ArtinMatthews

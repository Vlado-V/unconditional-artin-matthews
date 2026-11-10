module

public import ArtinMatthews.GiantSignedUniformBirthRank
public import ArtinMatthews.MarkedBirthMixedBudget
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
public import Mathlib.Tactic.ENatToNat
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The signed and absolute factors are counted on the actual affected
edge set of the common performed-birth frame. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

variable {B : Type*} [Fintype B] {M n R : ℕ}

def giantSignedUniformBirthModifiedEdges
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B M n R)) : Finset (Fin n) :=
  Finset.univ.filter (fun i =>
    GiantSignedBirthOperation.edge i ∈ σ.support.image (giantSignedUniformBirthOperation M n R))

theorem giantSignedUniformBirthModifiedEdges_mem
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B M n R)) (i : Fin n) :
    i ∈ giantSignedUniformBirthModifiedEdges σ ↔
      GiantSignedBirthOperation.edge i ∈ σ.support.image (giantSignedUniformBirthOperation M n R) := by
  simp [giantSignedUniformBirthModifiedEdges]

theorem giantSignedUniformBirthModifiedEdges_card
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B M n R)) :
    (giantSignedUniformBirthModifiedEdges σ).card ≤ 2 * markedBirthPermutationRank σ := by
  let edges := giantSignedUniformBirthModifiedEdges σ
  have hsub : edges.image GiantSignedBirthOperation.edge ⊆
      σ.support.image (giantSignedUniformBirthOperation M n R) := by
    intro o ho
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ho
    exact (giantSignedUniformBirthModifiedEdges_mem σ i).mp hi
  have hedge : Function.Injective (@GiantSignedBirthOperation.edge n) :=
    fun _ _ h => GiantSignedBirthOperation.edge.inj h
  calc
    _ = (edges.image GiantSignedBirthOperation.edge).card :=
      (Finset.card_image_of_injective edges hedge).symm
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := markedBirthPermutation_operations_le_twice_rank
      (giantSignedUniformBirthOperation M n R) σ

theorem giantSignedUniformBirth_edge_product {A : Type*} [CommMonoid A]
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B M n R)) (clean dirty : A) :
    let edges := giantSignedUniformBirthModifiedEdges σ
    (∏ i : Fin n, if i ∈ edges then dirty else clean) =
      clean^(n-edges.card) * dirty^edges.card := by
  let edges := giantSignedUniformBirthModifiedEdges σ
  change (∏ i : Fin n, if i ∈ edges then dirty else clean) = _
  have hyes : (Finset.univ.filter fun i => i ∈ edges) = edges := by ext i; simp
  have hno : (Finset.univ.filter fun i => i ∉ edges) = edgesᶜ := by ext i; simp
  rw [Finset.prod_ite, hyes, hno, Finset.prod_const, Finset.prod_const,
    Finset.card_compl, Fintype.card_fin, mul_comm]

theorem giantSignedUniformBirth_edge_norm_budget
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B M n R)) {a b : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 1 ≤ b)
    (hr : 2 * markedBirthPermutationRank σ ≤ n) :
    (∏ i : Fin n, if i ∈ giantSignedUniformBirthModifiedEdges σ then b else a) ≤
      a^(n-2*markedBirthPermutationRank σ) * b^(2*markedBirthPermutationRank σ) := by
  rw [giantSignedUniformBirth_edge_product]
  simpa only [max_eq_right hb] using markedMixedEdgeBudget_mono_count ha ha1 (zero_le_one.trans hb)
    (giantSignedUniformBirthModifiedEdges_card σ) hr

end
end ArtinMatthews

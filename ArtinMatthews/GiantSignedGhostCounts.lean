module

public import ArtinMatthews.GiantSignedGhostRow
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual zero-residue counts split over the selected old indices and
their ordered survivors. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

def giantSignedGroupZeroCount {P : Finset ℕ} {n : ℕ}
    (a : Fin n → GiantSignedParticle P) : ℕ := (giantSignedGhostZeroIndices ⟨n, a⟩).card

theorem giantSignedGroupZeroCount_sum {P : Finset ℕ} {n : ℕ}
    (a : Fin n → GiantSignedParticle P) :
    giantSignedGroupZeroCount a = ∑ i, if (a i).2 = 0 then 1 else 0 := by
  classical
  exact Finset.card_filter _ _

theorem giantSignedGroupZeroCount_partition {P : Finset ℕ} {n : ℕ}
    (a : Fin n → GiantSignedParticle P) (S : Finset (Fin n)) :
    giantSignedGroupZeroCount a =
      giantSignedGroupZeroCount (markedRawSubsetTupleEquiv S a).1 +
        giantSignedGroupZeroCount (markedRawSubsetTupleEquiv S a).2 := by
  classical
  have h := (markedRawSubsetIndexEquiv S).sum_comp
    (fun i : Fin n => if (a i).2 = 0 then (1 : ℕ) else 0)
  rw [Fintype.sum_sum_type] at h
  rw [giantSignedGroupZeroCount_sum, giantSignedGroupZeroCount_sum, giantSignedGroupZeroCount_sum]
  exact h.symm

theorem giantSignedGhost_deleted_zero_iff {P : Finset ℕ} {n : ℕ}
    (a : Fin n → GiantSignedParticle P) (S : Finset (Fin n)) :
    (∀ i, ((markedRawSubsetTupleEquiv S a).1 i).2 = 0) ↔
      S ⊆ giantSignedGhostZeroIndices ⟨n, a⟩ := by
  classical
  constructor
  · intro h i hi
    have hx := h ((S.orderIsoOfFin rfl).symm ⟨i, hi⟩)
    rw [markedRawSubsetTupleEquiv_deleted] at hx
    change (a ((S.orderIsoOfFin rfl ((S.orderIsoOfFin rfl).symm ⟨i, hi⟩)).val)).2 = 0 at hx
    have he := congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply ⟨i, hi⟩)
    rw [he] at hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
  · intro h i
    rw [markedRawSubsetTupleEquiv_deleted]
    have hi : S.orderEmbOfFin rfl i ∈ S := (S.orderIsoOfFin rfl i).property
    exact (Finset.mem_filter.mp (h hi)).2

theorem giantSignedGhost_survivor_zero_count {P : Finset ℕ} {n : ℕ}
    (a : Fin n → GiantSignedParticle P) (S : Finset (Fin n))
    (hS : S ⊆ giantSignedGhostZeroIndices ⟨n, a⟩) :
    giantSignedGroupZeroCount (markedRawSubsetTupleEquiv S a).2 =
      giantSignedGroupZeroCount a - S.card := by
  classical
  have hz := (giantSignedGhost_deleted_zero_iff a S).mpr hS
  have hd : giantSignedGroupZeroCount (markedRawSubsetTupleEquiv S a).1 = S.card := by
    simp [giantSignedGroupZeroCount_sum, hz]
  have hp := giantSignedGroupZeroCount_partition a S
  omega

end
end ArtinMatthews

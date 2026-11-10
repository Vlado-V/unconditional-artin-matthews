module

public import ArtinMatthews.GiantSignedBirthPrefixMemo
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

/-! The actual equality event supplies every local prefix gate. A pivot
is either already retained or an earlier draw in the same stage. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

variable {B : Type*} [Fintype B] {PB : B → Finset ℕ} {k ell n H : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}

theorem giantSignedUniformBirthPrefixGate_of_event
    (hPB : ∀ g p, p ∈ PB g → p.Prime)
    (d : GiantSignedBirthData PB ell C batch) (hH : ∀ i g, batch i g ≤ H)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H))
    (hEvent : MarkedBirthPermutationEvent (giantSignedUniformBirthValue d H hH) σ)
    (o : GiantSignedBirthOperation n) :
    GiantSignedUniformBirthConditionalGate σ o
      (giantSignedUniformBirthConditionalValues hPB (giantSignedBirthStageEmbedding d hH o)
        (giantSignedUniformBirthPrefixMemo d hH (giantSignedBirthOperationTime o))
        (giantSignedBirthStageTuple d hH o)) := by
  rw [giantSignedUniformBirthPrefixMemo_step hPB d hH o]
  intro a ha
  have hstage := Finset.mem_filter.mp ha
  obtain ⟨he,_,_,hv,hperformed⟩ :=
    giantSignedUniformBirthPivot_event σ (giantSignedUniformBirthValue d H hH) hEvent hstage.1
  have ht : giantSignedUniformBirthTime a = giantSignedBirthOperationTime o :=
    congrArg giantSignedBirthOperationTime hstage.2
  have htp := giantSignedUniformBirthEarlier_time he
  have hta : giantSignedUniformBirthTime a < giantSignedBirthOperationTime o+1 := by omega
  have htb : giantSignedUniformBirthTime (giantSignedUniformBirthPivot σ a) <
      giantSignedBirthOperationTime o+1 := htp.trans_lt hta
  have hn : giantSignedBirthOptionPrime (giantSignedUniformBirthValue d H hH a) ≠ none := by
    obtain ⟨i,rfl⟩ := (giantSignedBirthStageEmbedding_range d hH o a).mpr ⟨hstage.2,hperformed⟩
    rw [giantSignedBirthStageEmbedding_value, ← giantSignedBirthStageTuple_value d hH o i]
    rw [giantSignedBirthOptionPrime_some (hPB _ _ (giantSignedBirthStageTuple d hH o i).property)]
    exact Option.some_ne_none _
  simp only [giantSignedUniformBirthPrefixMemo, if_pos hta, if_pos htb]
  exact ⟨hn,congrArg giantSignedBirthOptionPrime hv⟩

theorem giantSignedUniformBirthPrefixPivot_cases
    (hPB : ∀ g p, p ∈ PB g → p.Prime)
    (d : GiantSignedBirthData PB ell C batch) (hH : ∀ i g, batch i g ≤ H)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H))
    (hEvent : MarkedBirthPermutationEvent (giantSignedUniformBirthValue d H hH) σ)
    (o : GiantSignedBirthOperation n)
    {a : GiantSignedUniformBirthAddress B (k+ell) n H}
    (ha : a ∈ giantSignedUniformBirthStageNonpivots σ o) :
    let p := giantSignedUniformBirthPivot σ a
    (giantSignedUniformBirthTime p < giantSignedBirthOperationTime o ∧
      giantSignedUniformBirthPrefixMemo d hH (giantSignedBirthOperationTime o) p ≠ none) ∨
    ∃ i : GiantSignedBirthStageDraw d o, giantSignedBirthStageEmbedding d hH o i = p ∧
      GiantSignedUniformBirthEarlier (giantSignedBirthStageEmbedding d hH o i) a := by
  let p := giantSignedUniformBirthPivot σ a
  have hstage := Finset.mem_filter.mp ha
  obtain ⟨he,_,_,hv,hperformed⟩ :=
    giantSignedUniformBirthPivot_event σ (giantSignedUniformBirthValue d H hH) hEvent hstage.1
  have ht : giantSignedUniformBirthTime a = giantSignedBirthOperationTime o :=
    congrArg giantSignedBirthOperationTime hstage.2
  have hp : giantSignedUniformBirthTime p ≤ giantSignedBirthOperationTime o :=
    (giantSignedUniformBirthEarlier_time he).trans_eq ht
  rcases lt_or_eq_of_le hp with hlt | heq
  · left
    refine ⟨hlt,?_⟩
    rw [giantSignedUniformBirthPrefixMemo, if_pos hlt, ← hv]
    obtain ⟨i,hi⟩ := (giantSignedBirthStageEmbedding_range d hH o a).mpr ⟨hstage.2,hperformed⟩
    rw [← hi, giantSignedBirthStageEmbedding_value, ← giantSignedBirthStageTuple_value d hH o i]
    rw [giantSignedBirthOptionPrime_some (hPB _ _ (giantSignedBirthStageTuple d hH o i).property)]
    exact Option.some_ne_none _
  · right
    have ho : giantSignedUniformBirthOperation (k+ell) n H p = o :=
      giantSignedBirthOperationTime_injective heq
    obtain ⟨i,hi⟩ := (giantSignedBirthStageEmbedding_range d hH o p).mpr ⟨ho,hv.symm.trans_ne hperformed⟩
    exact ⟨i,hi,hi.symm ▸ he⟩

end
end ArtinMatthews

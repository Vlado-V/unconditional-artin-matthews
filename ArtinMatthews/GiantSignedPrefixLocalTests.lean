module

public import ArtinMatthews.GiantSignedBirthLocalMemo
public import ArtinMatthews.GiantSignedRawFreshBirthGate
public import ArtinMatthews.GiantSignedBirthPrefixGate
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

/-! Literal local tests compare a move's memo update with the next
prefix of the complete performed-birth event. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {B : Type*} [Fintype B] [DecidableEq B] {PB : B → Finset ℕ}
    {k ell n H : ℕ} {C : Fin n → B → Finset (Fin k)} {b : Fin (n+1) → B → ℕ}
    (hPB : ∀ g p, p ∈ PB g → p.Prime)
    (d : GiantSignedBirthData PB ell C b) (hH : ∀ i g, b i g ≤ H)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H))

def GiantSignedVisitPrefixCondition (i : Fin (n+1)) (β : B → ℕ) (born : ∀ g, Fin (β g) → PB g) : Prop :=
  ∃ hb : ∀ g, β g ≤ H,
    let t := giantSignedBirthOperationTime (.visit i)
    let old := giantSignedUniformBirthPrefixMemo d hH t
    let out := giantSignedVisitBirthMemo hPB i β hb born old
    GiantSignedUniformBirthConditionalGate σ (.visit i) out ∧
      out = giantSignedUniformBirthPrefixMemo d hH (t+1)

def giantSignedEdgeBirthMemo {D : B → Finset (Fin k)}
    (i : Fin n) (target : MarkedPhysicalMarking PB (k+ell))
    (promoted : ∀ g, Finset (Fin (ell+(D g).card)))
    (old : GiantSignedBirthMemo B (k+ell) n H) : GiantSignedBirthMemo B (k+ell) n H :=
  giantSignedRawFreshBirthValues hPB i D promoted (giantSignedBirthClearCurrent (.edge i) old)
    ((giantSignedEdgeTargetLabelEquiv promoted) (giantSignedPatternFreeLabels D target)).2

def GiantSignedEdgePrefixCondition {D : B → Finset (Fin k)}
    (i : Fin n) (target : MarkedPhysicalMarking PB (k+ell))
    (promoted : ∀ g, Finset (Fin (ell+(D g).card))) : Prop :=
  let t := giantSignedBirthOperationTime (.edge i)
  let old := giantSignedUniformBirthPrefixMemo d hH t
  let out := giantSignedEdgeBirthMemo hPB i target promoted old
  GiantSignedUniformBirthConditionalGate σ (.edge i) out ∧
    out = giantSignedUniformBirthPrefixMemo d hH (t+1)

theorem giantSignedInitialBirthMemo_prefix
    (hEvent : MarkedBirthPermutationEvent (giantSignedUniformBirthValue d H hH) σ) :
    GiantSignedUniformBirthConditionalGate σ .initial (giantSignedInitialBirthMemo hPB d.initial) ∧
      giantSignedInitialBirthMemo hPB d.initial =
        giantSignedUniformBirthPrefixMemo d hH (giantSignedBirthOperationTime (.visit (0 : Fin (n+1)))) := by
  let memo := giantSignedUniformBirthConditionalValues hPB
    (giantSignedBirthStageEmbedding d hH .initial)
    (giantSignedUniformBirthPrefixMemo d hH 0) (giantSignedBirthStageTuple d hH .initial)
  have h : memo = giantSignedInitialBirthMemo hPB d.initial := by
    unfold memo
    rw [giantSignedUniformBirthPrefixMemo_zero d hH]
    rfl
  exact ⟨h ▸ giantSignedUniformBirthPrefixGate_of_event hPB d hH σ hEvent .initial,
    h.symm.trans (giantSignedUniformBirthPrefixMemo_step hPB d hH .initial)⟩

theorem giantSignedVisitPrefixCondition_of_event
    (hEvent : MarkedBirthPermutationEvent (giantSignedUniformBirthValue d H hH) σ) (i : Fin (n+1)) :
    GiantSignedVisitPrefixCondition hPB d hH σ i (b i) (d.born i) := by
  refine ⟨hH i,?_⟩
  dsimp only
  unfold giantSignedVisitBirthMemo
  rw [giantSignedBirthClearCurrent_prefix d hH (.visit i)]
  exact ⟨giantSignedUniformBirthPrefixGate_of_event hPB d hH σ hEvent (.visit i),
    giantSignedUniformBirthPrefixMemo_step hPB d hH (.visit i)⟩

theorem giantSignedEdgePrefixCondition_of_event
    (hEvent : MarkedBirthPermutationEvent (giantSignedUniformBirthValue d H hH) σ) (i : Fin n) :
    GiantSignedEdgePrefixCondition hPB d hH σ i (d.target i) (d.promoted i) := by
  unfold GiantSignedEdgePrefixCondition
  dsimp only
  unfold giantSignedEdgeBirthMemo
  rw [giantSignedBirthClearCurrent_prefix d hH (.edge i), giantSignedRawFreshBirthValues_eq_stageTuple hPB d hH i]
  exact ⟨giantSignedUniformBirthPrefixGate_of_event hPB d hH σ hEvent (.edge i),
    giantSignedUniformBirthPrefixMemo_step hPB d hH (.edge i)⟩

end
end ArtinMatthews

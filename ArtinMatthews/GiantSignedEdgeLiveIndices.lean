module

public import ArtinMatthews.GiantSignedCanonicalSlots
public import ArtinMatthews.GiantSignedGhostLiveOrigin
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

/-! An edge consumes each old index at most once. The indices here are
the actual copied slots, retrieval injection, survivors and stored slots. -/
namespace ArtinMatthews
noncomputable section

def giantSignedRetrievalPartition {d a : ℕ} (e : Fin a ↪ Fin d) :
    Fin a ⊕ Fin ((Finset.univ.map e)ᶜ).card ≃ Fin d := by
  let R := Finset.univ.map e
  let f : Fin a → R := fun i => ⟨e i, Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      exact e.injective (congrArg Subtype.val h)
    · intro i
      obtain ⟨j, _, hj⟩ := Finset.mem_map.mp i.property
      exact ⟨j, Subtype.ext hj⟩
  exact (Equiv.sumCongr (Equiv.ofBijective f hf)
    ((Rᶜ.orderIsoOfFin rfl).toEquiv.trans (markedRawFinsetComplEquiv R))).trans
      (Equiv.sumCompl (fun i : Fin d => i ∈ R))

theorem giantSignedRetrievalPartition_promoted {d a : ℕ} (e : Fin a ↪ Fin d) (i : Fin a) :
    giantSignedRetrievalPartition e (.inl i) = e i := rfl

theorem giantSignedRetrievalPartition_survivor {d a : ℕ} (e : Fin a ↪ Fin d)
    (i : Fin ((Finset.univ.map e)ᶜ).card) :
    giantSignedRetrievalPartition e (.inr i) = ((Finset.univ.map e)ᶜ).orderEmbOfFin rfl i := rfl

private def giantSignedEdgeOriginOrder (A P F R S : Type*) :
    (A ⊕ (P ⊕ F)) ⊕ (R ⊕ S) ≃ ((A ⊕ S) ⊕ (P ⊕ R)) ⊕ F where
  toFun
    | .inl (.inl a) => .inl (.inl (.inl a))
    | .inl (.inr (.inl p)) => .inl (.inr (.inl p))
    | .inl (.inr (.inr f)) => .inr f
    | .inr (.inl r) => .inl (.inr (.inr r))
    | .inr (.inr s) => .inl (.inl (.inr s))
  invFun
    | .inl (.inl (.inl a)) => .inl (.inl a)
    | .inl (.inr (.inl p)) => .inl (.inr (.inl p))
    | .inr f => .inl (.inr (.inr f))
    | .inl (.inr (.inr r)) => .inr (.inl r)
    | .inl (.inl (.inr s)) => .inr (.inr s)
  left_inv := by rintro ((a | p | f) | r | s) <;> rfl
  right_inv := by rintro (((a | s) | p | r) | f) <;> rfl

variable {k ell degree : ℕ} (C : Finset (Fin k))
    (stores promotions : Finset (Fin (ell+C.card)))
    (retrieve : Fin promotions.card ↪ Fin degree)

def giantSignedEdgeLiveOrigin :
    GiantSignedLiveSlots (k+ell) (((Finset.univ.map retrieve)ᶜ).card+stores.card) ↪
      (GiantSignedLiveSlots (k+ell) degree ⊕ {i : Fin (ell+C.card) // i ∉ promotions}) :=
  let slots := giantSignedCanonicalSlotEquiv C ell
  let input := Equiv.sumCongr
    (slots.trans (Equiv.sumCongr (Equiv.refl _) (markedRawSubsetIndexEquiv promotions).symm))
    finSumFinEquiv.symm
  let oldActive := (Function.Embedding.sumMap (Function.Embedding.refl _)
    (stores.orderEmbOfFin rfl).toEmbedding).trans slots.symm.toEmbedding
  let oldPending := (giantSignedRetrievalPartition retrieve).toEmbedding
  let fresh := ((promotionsᶜ.orderIsoOfFin rfl).toEquiv.trans
    (markedRawFinsetComplEquiv promotions)).toEmbedding
  (input.trans (giantSignedEdgeOriginOrder _ _ _ _ _)).toEmbedding.trans
    (Function.Embedding.sumMap (Function.Embedding.sumMap oldActive oldPending) fresh)

theorem giantSignedEdgeLiveOrigin_copied (i : {i : Fin k // i ∉ C}) :
    giantSignedEdgeLiveOrigin C stores promotions retrieve (.inl (Fin.castAdd ell i.val)) =
      .inl (.inl (Fin.castAdd ell i.val)) := by
  unfold giantSignedEdgeLiveOrigin
  simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply, Equiv.trans_apply,
    Equiv.sumCongr_apply, Sum.map_inl, giantSignedCanonicalSlotEquiv_copied, Equiv.refl_apply]
  change Sum.inl (Sum.inl ((giantSignedCanonicalSlotEquiv C ell).symm (.inl i))) = _
  rw [giantSignedCanonicalSlotEquiv_symm_copied]

theorem giantSignedEdgeLiveOrigin_promoted (i : Fin promotions.card) :
    giantSignedEdgeLiveOrigin C stores promotions retrieve
      (.inl (giantSignedFreeSlotEmbedding C ell (promotions.orderEmbOfFin rfl i))) =
      .inl (.inr (retrieve i)) := by
  have hi : (markedRawSubsetIndexEquiv promotions).symm (promotions.orderEmbOfFin rfl i) =
      .inl i := (markedRawSubsetIndexEquiv promotions).symm_apply_apply (.inl i)
  unfold giantSignedEdgeLiveOrigin
  simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply, Equiv.trans_apply,
    Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, giantSignedCanonicalSlotEquiv_free, hi]
  rfl

theorem giantSignedEdgeLiveOrigin_fresh (i : {i : Fin (ell+C.card) // i ∉ promotions}) :
    giantSignedEdgeLiveOrigin C stores promotions retrieve
      (.inl (giantSignedFreeSlotEmbedding C ell i.val)) = .inr i := by
  let e := (promotionsᶜ.orderIsoOfFin rfl).toEquiv.trans (markedRawFinsetComplEquiv promotions)
  let j := e.symm i
  have hj : ((promotionsᶜ).orderEmbOfFin rfl j) = i.val :=
    congrArg Subtype.val (e.apply_symm_apply i)
  have hi : (markedRawSubsetIndexEquiv promotions).symm i.val = .inr j := by
    rw [← hj]
    exact (markedRawSubsetIndexEquiv promotions).symm_apply_apply (.inr j)
  unfold giantSignedEdgeLiveOrigin
  simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply, Equiv.trans_apply,
    Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, giantSignedCanonicalSlotEquiv_free, hi]
  exact congrArg Sum.inr (e.apply_symm_apply i)

theorem giantSignedEdgeLiveOrigin_survivor (i : Fin ((Finset.univ.map retrieve)ᶜ).card) :
    giantSignedEdgeLiveOrigin C stores promotions retrieve (.inr (Fin.castAdd stores.card i)) =
      .inl (.inr (((Finset.univ.map retrieve)ᶜ).orderEmbOfFin rfl i)) := by
  unfold giantSignedEdgeLiveOrigin
  simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply, Equiv.trans_apply,
    Equiv.sumCongr_apply, Sum.map_inr, finSumFinEquiv_symm_apply_castAdd]
  rfl

theorem giantSignedEdgeLiveOrigin_stored (i : Fin stores.card) :
    giantSignedEdgeLiveOrigin C stores promotions retrieve
      (.inr (Fin.natAdd ((Finset.univ.map retrieve)ᶜ).card i)) =
      .inl (.inl (giantSignedFreeSlotEmbedding C ell (stores.orderEmbOfFin rfl i))) := by
  unfold giantSignedEdgeLiveOrigin
  simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply, Equiv.trans_apply,
    Equiv.sumCongr_apply, Sum.map_inr, finSumFinEquiv_symm_apply_natAdd]
  change Sum.inl (Sum.inl ((giantSignedCanonicalSlotEquiv C ell).symm
    (.inr (stores.orderEmbOfFin rfl i)))) = _
  rw [giantSignedCanonicalSlotEquiv_symm_free]

end
end ArtinMatthews

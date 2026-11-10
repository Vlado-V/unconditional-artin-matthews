module

public import ArtinMatthews.GiantSignedChronologicalOriginalPath
public import ArtinMatthews.GiantSignedChronologicalPackedExt
public import ArtinMatthews.GiantSignedLifespanScheduleReplay
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

/-! Decoding a birth-distinct chronology and reconstructing it from
the exact lifespan choice and ordered batches recovers every move. -/

namespace ArtinMatthews
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}

local notation "Bands" => Sum.elim PS PB

theorem giantSignedChronologicalReconstruction
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (κ : Fin n → ℤ)
    (q : Fin (n+1) → ℝ) (ha : GiantSignedChronologicalAdmissible κ h)
    (hd : GiantSignedBirthDistinct (giantSignedChronologicalBirthData h))
    (hSB : ∀ s b, Disjoint (PS s) (PB b))
    (hP : ∀ (g : S ⊕ B) p, p ∈ Bands g → p.Prime)
    (hdis : Pairwise (fun i j : S ⊕ B => Disjoint (Bands i) (Bands j)))
    (hκ : ∀ i, 0 < (κ i).natAbs) (hsize : ∀ i g p, p ∈ Bands g → (κ i).natAbs < p)
    (decoded : GiantSignedChronologicalDecodedLifespans h κ q) :
    let path := giantSignedChronologicalOriginalPath h κ ha hd hSB
    let order := giantSignedChronologicalRecoveredBirthOrders h κ q decoded
    let data := path.schedule hP hdis hκ hsize decoded.supported order
    (⟨data.batch,path.chronology data⟩ : Σ b : Fin (n+1) → B → ℕ,
      GiantSignedChronologicalChoices PS PB ell C b) = ⟨batch,h⟩ := by
  let path := giantSignedChronologicalOriginalPath h κ ha hd hSB
  let order := giantSignedChronologicalRecoveredBirthOrders h κ q decoded
  let data := path.schedule hP hdis hκ hsize decoded.supported order
  let m := decoded.coefficientData
  let h' := path.chronology data
  have hghost := giantSignedChronologicalRecoveredBirthOrders_move h κ q decoded
  have hStep (i : Fin n) : data.increment i = κ i * (giantSignedChronologicalProduct h i : ℤ) :=
    giantSignedChronologicalJoinedIncrement_eq h κ i
  have hmem := giantSignedLifespanSchedule_replays data h κ ha.compatible ha.boundary.1
    m.before m.after hghost (fun _ => rfl) hStep m.edgeMatch
  have hb : data.batch = batch := by
    funext i g
    exact (congrArg (fun r : GiantSignedGhostMoves (giantSignedMemoryGroupEquiv PB (h.state i).2.2 g) => r.2.1)
      (hghost i g)).symm
  have hs : h'.state = h.state := by
    funext i
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · exact (giantSignedChronologicalSmallResidue_eq_translate h κ ha.compatible i).symm
      · rfl
    · exact Prod.ext rfl (congrArg Sigma.fst (hmem i))
  apply Sigma.ext hb
  refine giantSignedChronologicalChoices_heq h' h hb hs rfl rfl rfl rfl rfl ?_ ?_
  · intro i g
    change HEq (giantSignedFixedGhostMove (data.memory i).1 (data.batch i)
      (GiantSignedLifespanScheduleData.deleted i (data.memory i)) (data.born i) g)
      (giantSignedFixedGhostMove (h.state i).2.2 (batch i) (h.deleted i) (h.born i) g)
    rw [hmem i]
    exact heq_of_eq (hghost i g).symm
  · intro i
    change HEq (data.edge i (data.memory i.castSucc)) (h.edge i)
    rw [hmem i.castSucc,m.edgeMatch i]
    let before : GiantSignedLifespanScheduleData.Before (c := decoded.choice) (offset := path.offset) i.castSucc :=
      ⟨(h.state i.castSucc).2.2,m.before i.castSucc⟩
    let after := data.after i.castSucc before
    have hAfter := giantSignedLifespanSchedule_after_replay data h i.castSucc (m.before i.castSucc) (hghost i.castSucc)
    have hTransport {after' : GiantSignedMemory PB} (hm : after = after')
        (certificate : ∀ g, GiantSignedLifespanMemory (giantSignedGhostVisitAfter (decoded.choice g) i.castSucc)
          (giantSignedLifespanResidue (decoded.choice g) path.offset i.castSucc)
          (giantSignedMemoryGroupEquiv PB after' g)) :
        HEq (data.edge i before) (giantSignedLifespanEdgeChoice decoded.choice i.castSucc i.succ path.offset after'
          certificate (data.source i) (data.target i) (data.target_injective i)) := by
      subst after'
      have he : data.after_certificate i.castSucc before = certificate :=
        funext fun g => giantSignedLifespanMemory_eq _ _
      unfold GiantSignedLifespanScheduleData.edge
      rw [he]
      rfl
    exact hTransport hAfter (m.after i.castSucc)

end
end ArtinMatthews

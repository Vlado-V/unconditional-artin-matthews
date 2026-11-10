module

public import ArtinMatthews.GiantSignedBirthDisplacement
public import ArtinMatthews.GiantSignedChronologicalLifeEndpoints
public import ArtinMatthews.GiantSignedChronologicalAnchorHits
public import ArtinMatthews.GiantSignedChronologicalLifePending
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

/-! The original deletion subset and ordered ghost labels are exactly
the two ghost endpoints of the reconstructed prime lifetimes. -/

namespace ArtinMatthews
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}
    (h : GiantSignedChronologicalChoices PS PB ell C batch)
    (κ : Fin n → ℤ) (ha : GiantSignedChronologicalAdmissible κ h)
    (hd : GiantSignedBirthDistinct (giantSignedChronologicalBirthData h))

include ha hd in
theorem giantSignedChronologicalDeleted_iff_not_after (i : Fin (n+1)) (g : B)
    (j : Fin ((h.state i).2.2.1 g)) :
    j ∈ h.deleted i g ↔ ¬GiantSignedChronologicalPendingAfter h i g ((h.state i).2.2.2 g j).1 := by
  constructor
  · rintro hj ⟨w,hw⟩
    let m := giantSignedMemoryGroupEquiv PB (h.state i).2.2 g
    let D := h.deleted i g
    let b := h.born i g
    change Fin ((Dᶜ).card + batch i g) at w
    revert hw
    refine Fin.addCases ?_ ?_ w
    · intro u hu
      have hu' := congrArg Sigma.fst (giantSignedGhostTarget_survivor m D b u)
      let l := giantSignedChronologicalPreLineage h κ ha i g
      have he : ((Dᶜ.orderEmbOfFin rfl u) : Fin (m.1)) = j := by
        have hinj := giantSignedBirthLineage_injective l hd
        have heq : (Sum.inr (Dᶜ.orderEmbOfFin rfl u) : GiantSignedStateLiveSlots (h.state i) g) = Sum.inr j :=
          hinj (hu'.symm.trans hu)
        exact Sum.inr.inj heq
      exact (Finset.mem_compl.mp (Finset.orderEmbOfFin_mem Dᶜ rfl u)) (he.symm ▸ hj)
    · intro u hu
      let l := giantSignedChronologicalPreLineage h κ ha i g
      let born := giantSignedChronologicalVisitBirth h i g u
      have hp : (m.2 j).1 = b u := hu.symm.trans
        (congrArg Sigma.fst (giantSignedGhostTarget_born m D b u))
      have he : l.origin (.inr j) = born := hd ((l.prime_eq (.inr j)).trans (congrArg Subtype.val hp))
      have ht := l.time_le (.inr j)
      rw [he] at ht
      change 2*i.val+1 ≤ 2*i.val at ht
      omega
  · intro hn
    by_contra hj
    exact hn (giantSignedChronologicalOldGhost_survives h i g j hj)

namespace GiantSignedChronologicalLifeEndpoints

variable {h} {g : B} {p : PB g} (L : GiantSignedChronologicalLifeEndpoints h g p)

include hd in
theorem born_iff (i : Fin (n+1)) :
    (∃ j, h.born i g j = p) ↔ L.start = i ∧ L.startTime % 2 = 1 := by
  constructor
  · rintro ⟨j,hj⟩
    let b := giantSignedChronologicalVisitBirth h i g j
    have he : L.birth = b := hd (L.birth_prime.trans (congrArg Subtype.val hj).symm)
    have ht : L.startTime = 2*i.val+1 :=
      congrArg (giantSignedPerformedBirthTime (giantSignedChronologicalBirthData h)) he
    exact ⟨Fin.ext (by rw [L.start_val,ht]; omega),by omega⟩
  · rintro ⟨hi,ho⟩
    have ht : L.startTime = 2*i.val+1 := by
      have hv := congrArg Fin.val hi
      rw [L.start_val] at hv
      omega
    rcases hb : L.birth with a | (a | ⟨i',g',j⟩)
    · simp only [startTime,hb,giantSignedPerformedBirthTime] at ht
      omega
    · simp only [startTime,hb,giantSignedPerformedBirthTime] at ht
      omega
    · have hg := L.birth_group
      have hp := L.birth_prime
      rw [hb] at hg hp
      change g' = g at hg
      subst g'
      simp only [startTime,hb,giantSignedPerformedBirthTime] at ht
      have he : i' = i := Fin.ext (by omega)
      exact he ▸ (show ∃ j, h.born i' g j = p from ⟨j,Subtype.ext hp⟩)

include ha hd in
theorem deleted_iff (i : Fin (n+1)) (j : Fin ((h.state i).2.2.1 g))
    (hj : ((h.state i).2.2.2 g j).1 = p) :
    j ∈ h.deleted i g ↔ L.finish = i ∧ L.endTime % 2 = 0 := by
  have hp : GiantSignedChronologicalPendingBefore h i g p := ⟨j,hj⟩
  have hn := giantSignedChronologicalPendingBefore_not_active h κ ha hd i g p hp
  have he : j ∈ h.deleted i g ↔ ¬GiantSignedChronologicalPendingAfter h i g p :=
    hj ▸ giantSignedChronologicalDeleted_iff_not_after h κ ha hd i g j
  rw [he]
  constructor
  · intro hno
    have ht := (L.live _).mp ((giantSignedChronologicalLiveAt_before_iff h i g p).mpr (Or.inr hp))
    have hEnd : L.endTime = 2*i.val := by
      by_contra hb
      have hnLive := ((giantSignedChronologicalLiveAt_after_iff h i g p).mp
        ((L.live _).mpr ⟨ht.1.trans (by omega),by omega⟩)).resolve_left hn
      exact hno hnLive
    exact ⟨Fin.ext (by rw [L.finish_val,hEnd]; omega),by omega⟩
  · rintro ⟨hf,he⟩ hp'
    have ht := ((L.live _).mp ((giantSignedChronologicalLiveAt_after_iff h i g p).mpr (Or.inr hp'))).2
    have hv := congrArg Fin.val hf
    rw [L.finish_val] at hv
    omega

include ha hd in
theorem finish_offset :
    let offset := giantSignedChronologicalOffset κ h
    (offset L.finish : ZMod p.val) = (offset L.start : ZMod p.val) := by
  let o := giantSignedChronologicalOffset κ h
  by_cases hA : GiantSignedChronologicalActive h L.finish g p
  · exact L.active_offset κ ha hd L.finish hA
  · have he := (L.finish_inactive_iff κ ha).mp hA
    have ht : L.endTime = 2*L.finish.val := by rw [L.finish_val]; omega
    have hLive := (L.live L.endTime).mpr ⟨L.startTime_le,le_rfl⟩
    rw [ht] at hLive
    obtain ⟨j,hj⟩ := ((giantSignedChronologicalLiveAt_before_iff h L.finish g p).mp hLive).resolve_left hA
    have hdel := (L.deleted_iff κ ha hd L.finish j hj).mpr ⟨rfl,he⟩
    let l := giantSignedChronologicalPreLineage h κ ha L.finish g
    have hb : l.origin (.inr j) = L.birth :=
      hd ((l.prime_eq (.inr j)).trans ((congrArg Subtype.val hj).trans L.birth_prime.symm))
    have hz := giantSignedChronological_deleted_anchor κ h ha L.finish g j hdel
    change (o L.finish : ZMod ((h.state L.finish).2.2.2 g j).1.val) =
      (giantSignedBirthOffset o (giantSignedChronologicalBirthData h) (l.origin (.inr j)) :
        ZMod ((h.state L.finish).2.2.2 g j).1.val) at hz
    rw [hb,L.birthOffset_eq] at hz
    exact (congrArg Subtype.val hj) ▸ hz

end GiantSignedChronologicalLifeEndpoints
end
end ArtinMatthews

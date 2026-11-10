module

public import ArtinMatthews.GiantPrimeLifespanStatus
public import ArtinMatthews.GiantSignedBirthDisplacement
public import ArtinMatthews.GiantSignedChronologicalLifeEndpoints
public import ArtinMatthews.GiantPrimeLifespanInverse
public import ArtinMatthews.GiantPrimeLifespanInverseSupport
public import ArtinMatthews.GiantSignedChronologicalGhostLifecycle
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

/-! Extract the literal supported lifespan term of a prime from a
birth-distinct chronology, including its exact live residue anchors. -/

namespace ArtinMatthews
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (κ : Fin n → ℤ)
    (q : Fin (n+1) → ℝ) (g : B) (p : PB g) (A : Finset (Fin (n+1)))

local notation "BirthData" => giantSignedChronologicalBirthData h
local notation "Offset" => giantSignedChronologicalOffset κ h

def giantSignedChronologicalPrimeAnchor (c : GiantSignedResidueLifespanChoice A) (i : Fin (n+1)) : ZMod p.val :=
  (giantSignedPrimeLifespanView A c).elim 0
    (fun L => (Offset i : ZMod p.val) - (Offset L.start : ZMod p.val))

structure GiantSignedChronologicalPrimeMatch where
  choice : GiantSignedResidueLifespanChoice A
  supported : giantSignedResidueLifespanWeight p.val Offset q A choice ≠ 0
  before : ∀ i, GiantSignedChronologicalPendingBefore h i g p ↔ giantSignedPrimePendingBefore choice i
  after : ∀ i, GiantSignedChronologicalPendingAfter h i g p ↔ giantSignedPrimePendingAfter choice i
  born : ∀ i, (∃ j, h.born i g j = p) ↔ giantSignedPrimeGhostBirthAt choice i
  deleted : ∀ i (j : Fin ((h.state i).2.2.1 g)), ((h.state i).2.2.2 g j).1 = p →
    (j ∈ h.deleted i g ↔ giantSignedPrimeGhostDeathAt choice i)
  before_particle : ∀ i (j : Fin ((h.state i).2.2.1 g)), ((h.state i).2.2.2 g j).1 = p →
    (h.state i).2.2.2 g j = ⟨p,giantSignedChronologicalPrimeAnchor h κ g p A choice i⟩
  after_particle : ∀ i (j : Fin ((giantSignedChronologicalGhostTarget h i).1 g)),
    ((giantSignedChronologicalGhostTarget h i).2 g j).1 = p →
    (giantSignedChronologicalGhostTarget h i).2 g j = ⟨p,giantSignedChronologicalPrimeAnchor h κ g p A choice i⟩

private theorem lifetime_particle (L : GiantSignedChronologicalLifeEndpoints h g p)
    (hd : GiantSignedBirthDistinct BirthData) (i : Fin (n+1))
    (s : GiantSignedState PS PB (k+ell)) (time : ℕ) (l : GiantSignedBirthLineage BirthData s g time)
    (ha : GiantSignedLineageAnchored Offset (Offset i) l) (j : GiantSignedStateLiveSlots s g)
    (hj : giantSignedStateLivePrime s g j = p) :
    giantSignedStateLiveParticle s g j =
      ⟨p,(Offset i : ZMod p.val) - (Offset L.start : ZMod p.val)⟩ := by
  have hbirth : l.origin j = L.birth :=
    hd ((l.prime_eq j).trans ((congrArg Subtype.val hj).trans L.birth_prime.symm))
  have hz := ha j
  rw [hbirth,L.birthOffset_eq,hj] at hz
  exact hz.trans (by simp only [giantSignedParticleAt,Int.cast_sub])

private def representedPrimeMatch (ha : GiantSignedChronologicalAdmissible κ h)
    (hd : GiantSignedBirthDistinct BirthData) (L : GiantSignedChronologicalLifeEndpoints h g p)
    (hA : ∀ i, i ∈ A ↔ GiantSignedChronologicalActive h i g p) (hp : 0 < p.val)
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) : GiantSignedChronologicalPrimeMatch h κ q g p A := by
  let R := L.interval κ ha A hA
  let c := giantSignedResidueLifespanChoiceOfInterval R
  have hc : giantSignedPrimeLifespanView A c = some R := giantSignedPrimeLifespanView_choiceOfInterval R
  have hweight : giantSignedResidueLifespanWeight p.val Offset q A c ≠ 0 :=
    giantSignedResidueLifespanWeight_ne_zero_of_view p.val hp Offset q A c hc hq0 hq1
      (L.finish_offset κ ha hd) (fun i hi => L.active_offset κ ha hd i ((hA i).mp hi))
  refine ⟨c,hweight,?_,?_,?_,?_,?_,?_⟩
  · intro i
    rw [giantSignedPrimePendingBefore,hc,Option.elim_some,hA]
    exact L.pendingBefore_iff κ ha hd i
  · intro i
    rw [giantSignedPrimePendingAfter,hc,Option.elim_some,hA]
    exact L.pendingAfter_iff κ ha hd i
  · intro i
    rw [giantSignedPrimeGhostBirthAt,hc,Option.elim_some]
    change (∃ j, h.born i g j = p) ↔ L.start = i ∧ decide (L.startTime % 2 = 1) = true
    rw [decide_eq_true_eq]
    exact L.born_iff hd i
  · intro i j hj
    rw [giantSignedPrimeGhostDeathAt,hc,Option.elim_some]
    change j ∈ h.deleted i g ↔ L.finish = i ∧ decide (L.endTime % 2 = 0) = true
    rw [decide_eq_true_eq]
    exact L.deleted_iff κ ha hd i j hj
  · intro i j hj
    rw [giantSignedChronologicalPrimeAnchor,hc,Option.elim_some]
    exact lifetime_particle h κ g p L hd i (h.state i) (2*i.val)
      (giantSignedChronologicalPreLineage h κ ha i g)
      (giantSignedChronologicalPreLineage_anchored κ h ha i g) (.inr j) hj
  · intro i j hj
    rw [giantSignedChronologicalPrimeAnchor,hc,Option.elim_some]
    let l := giantSignedChronologicalPreLineage h κ ha i g
    exact lifetime_particle h κ g p L hd i (giantSignedChronologicalAfterVisitState h i) (2*i.val+1)
      (giantSignedChronologicalVisitLineage h i g l)
      (giantSignedChronologicalVisitLineage_anchored h Offset i g l
        (giantSignedChronologicalPreLineage_anchored κ h ha i g)) (.inr j) hj

private def absentPrimeMatch (ha : GiantSignedChronologicalAdmissible κ h)
    (hA : ∀ i, i ∈ A ↔ GiantSignedChronologicalActive h i g p)
    (hb : giantSignedPrimeResidueBaseline p.val q ≠ 0)
    (hNo : ¬∃ b : GiantSignedPerformedBirth BirthData, giantSignedPerformedBirthPrime BirthData b = p.val) :
    GiantSignedChronologicalPrimeMatch h κ q g p A := by
  have hLive (t : ℕ) : ¬GiantSignedChronologicalLiveAt h g p t := fun ht => by
    obtain ⟨b,hb,_⟩ := giantSignedChronologicalLiveAt_origin h κ ha g p ht
    exact hNo ⟨b,hb⟩
  have hBefore (i : Fin (n+1)) : ¬GiantSignedChronologicalPendingBefore h i g p :=
    fun hh => hLive _ ((giantSignedChronologicalLiveAt_before_iff h i g p).mpr (Or.inr hh))
  have hAfter (i : Fin (n+1)) : ¬GiantSignedChronologicalPendingAfter h i g p :=
    fun hh => hLive _ ((giantSignedChronologicalLiveAt_after_iff h i g p).mpr (Or.inr hh))
  have hEmpty : ¬A.Nonempty := fun ⟨i,hi⟩ =>
    hLive _ ((giantSignedChronologicalLiveAt_before_iff h i g p).mpr (Or.inl ((hA i).mp hi)))
  let c := giantSignedResidueLifespanAbsentChoice hEmpty
  have hc : giantSignedPrimeLifespanView A c = none := giantSignedPrimeLifespanView_absentChoice hEmpty
  have hweight : giantSignedResidueLifespanWeight p.val Offset q A c ≠ 0 := by
    rw [giantSignedResidueLifespanAbsentChoice_weight]
    exact hb
  refine ⟨c,hweight,?_,?_,?_,?_,?_,?_⟩
  · intro i
    rw [giantSignedPrimePendingBefore,hc,Option.elim_none]
    exact iff_false_intro (hBefore i)
  · intro i
    rw [giantSignedPrimePendingAfter,hc,Option.elim_none]
    exact iff_false_intro (hAfter i)
  · intro i
    rw [giantSignedPrimeGhostBirthAt,hc,Option.elim_none]
    refine iff_false_intro (fun ⟨j,hj⟩ => ?_)
    exact hNo ⟨giantSignedChronologicalVisitBirth h i g j,congrArg Subtype.val hj⟩
  · exact fun i j hj => (hBefore i ⟨j,hj⟩).elim
  · exact fun i j hj => (hBefore i ⟨j,hj⟩).elim
  · exact fun i j hj => (hAfter i ⟨j,hj⟩).elim

def giantSignedChronologicalPrimeMatch (ha : GiantSignedChronologicalAdmissible κ h)
    (hd : GiantSignedBirthDistinct BirthData)
    (hdis : Pairwise (fun g g' => Disjoint (PB g) (PB g')))
    (hA : ∀ i, i ∈ A ↔ GiantSignedChronologicalActive h i g p) (hp : 0 < p.val)
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) (hb : giantSignedPrimeResidueBaseline p.val q ≠ 0) :
    GiantSignedChronologicalPrimeMatch h κ q g p A := by
  classical
  by_cases hBirth : ∃ b : GiantSignedPerformedBirth BirthData, giantSignedPerformedBirthPrime BirthData b = p.val
  · let b := hBirth.choose
    have hp' : giantSignedPerformedBirthPrime BirthData b = p.val := hBirth.choose_spec
    have hg : giantSignedPerformedBirthGroup (h := h) b = g := by
      by_contra hne
      exact Finset.disjoint_left.mp (hdis hne) (hp' ▸ giantSignedPerformedBirthPrime_mem_group b) p.property
    have ht := giantSignedChronologicalLiveAt_interval h κ ha hd g p b hg hp'
    let L : GiantSignedChronologicalLifeEndpoints h g p :=
      ⟨b,hg,hp',ht.choose,ht.choose_spec.1,ht.choose_spec.2⟩
    exact representedPrimeMatch h κ q g p A ha hd L hA hp hq0 hq1
  · exact absentPrimeMatch h κ q g p A ha hA hb hBirth

end
end ArtinMatthews

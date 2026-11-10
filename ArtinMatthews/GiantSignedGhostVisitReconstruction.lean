module

public import ArtinMatthews.GiantSignedGhostRow
public import ArtinMatthews.GiantPrimeLifespanStatus
public import ArtinMatthews.GiantPrimeLifespanAnchors
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The actual ordered ghost update of one prime group, reconstructed from its
literal lifespan choices. -/

namespace ArtinMatthews

noncomputable section

variable {P : Finset ℕ} {n : ℕ} {A : (p : P) → Finset (Fin n)}
    (c : (p : P) → GiantSignedResidueLifespanChoice (A p))

def giantSignedGhostVisitBefore (i : Fin n) : Finset P := by
  classical
  exact Finset.univ.filter (fun p => giantSignedPrimePendingBefore (c p) i)

def giantSignedGhostVisitAfter (i : Fin n) : Finset P := by
  classical
  exact Finset.univ.filter (fun p => giantSignedPrimePendingAfter (c p) i)

def giantSignedGhostVisitBorn (i : Fin n) : Finset P := by
  classical
  exact Finset.univ.filter (fun p => giantSignedPrimeGhostBirthAt (c p) i)

@[simp] theorem mem_giantSignedGhostVisitBefore (i : Fin n) (p : P) :
    p ∈ giantSignedGhostVisitBefore c i ↔ giantSignedPrimePendingBefore (c p) i := by
  simp only [giantSignedGhostVisitBefore, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem mem_giantSignedGhostVisitAfter (i : Fin n) (p : P) :
    p ∈ giantSignedGhostVisitAfter c i ↔ giantSignedPrimePendingAfter (c p) i := by
  simp only [giantSignedGhostVisitAfter, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem mem_giantSignedGhostVisitBorn (i : Fin n) (p : P) :
    p ∈ giantSignedGhostVisitBorn c i ↔ giantSignedPrimeGhostBirthAt (c p) i := by
  simp only [giantSignedGhostVisitBorn, Finset.mem_filter, Finset.mem_univ, true_and]

def giantSignedLifespanResidue (offset : Fin n → ℤ) (i : Fin n) (p : P) : ZMod p.val :=
  (giantSignedPrimeLifespanView (A p) (c p)).elim 0
    (fun L => (offset i : ZMod p.val) - (offset L.start : ZMod p.val))

theorem giantSignedLifespanResidue_ghostBirth (offset : Fin n → ℤ) (i : Fin n) (p : P)
    (hb : giantSignedPrimeGhostBirthAt (c p) i) :
    giantSignedLifespanResidue c offset i p = 0 := by
  unfold giantSignedPrimeGhostBirthAt at hb
  unfold giantSignedLifespanResidue
  cases hv : giantSignedPrimeLifespanView (A p) (c p) with
  | none => rfl
  | some L =>
    have hb' : L.start = i ∧ L.ghostBirth = true := by
      simpa only [hv, Option.elim_some] using hb
    change (offset i : ZMod p.val) - (offset L.start : ZMod p.val) = 0
    rw [hb'.1, sub_self]

theorem giantSignedLifespanResidue_ghostDeath (offset : Fin n → ℤ) (q : Fin n → ℝ)
    (i : Fin n) (p : P) (hw : giantSignedResidueLifespanWeight p.val offset q (A p) (c p) ≠ 0)
    (hd : giantSignedPrimeGhostDeathAt (c p) i) :
    giantSignedLifespanResidue c offset i p = 0 := by
  unfold giantSignedPrimeGhostDeathAt at hd
  unfold giantSignedLifespanResidue
  cases hv : giantSignedPrimeLifespanView (A p) (c p) with
  | none => rfl
  | some L =>
    have hd' : L.finish = i ∧ L.ghostDeath = true := by
      simpa only [hv, Option.elim_some] using hd
    have he := (giantSignedPrimeLifespanView_offsets_of_weight_ne_zero
      p.val offset q (A p) (c p) hw hv).1
    change (offset i : ZMod p.val) - (offset L.start : ZMod p.val) = 0
    rw [← hd'.1, he, sub_self]

structure GiantSignedLifespanMemory (pending : Finset P)
    (anchor : (p : P) → ZMod p.val) (m : GiantSignedGroupMemory P) where
  enumeration : Fin m.1 ≃ ↥pending
  particle_eq : ∀ j, m.2 j = ⟨(enumeration j).val, anchor (enumeration j).val⟩

namespace GiantSignedLifespanMemory

variable {pending : Finset P} {anchor : (p : P) → ZMod p.val} {m : GiantSignedGroupMemory P}
    (h : GiantSignedLifespanMemory pending anchor m)

include h

theorem prime_mem (j : Fin m.1) : (m.2 j).1 ∈ pending := by
  rw [h.particle_eq j]
  exact (h.enumeration j).property

theorem particle_anchor (j : Fin m.1) : m.2 j = ⟨(m.2 j).1, anchor (m.2 j).1⟩ := by
  rw [h.particle_eq j]

theorem prime_injective : Function.Injective (fun j : Fin m.1 => (m.2 j).1) := by
  intro j k he
  apply h.enumeration.injective
  apply Subtype.ext
  exact (congrArg (fun z : GiantSignedParticle P => z.1) (h.particle_eq j)).symm.trans
    (he.trans (congrArg (fun z : GiantSignedParticle P => z.1) (h.particle_eq k)))

def index (p : ↥pending) : Fin m.1 :=
  h.enumeration.symm p

theorem index_particle_eq (p : ↥pending) : m.2 (h.index p) = ⟨p.val, anchor p.val⟩ := by
  change m.2 (h.enumeration.symm p) = _
  exact (h.particle_eq (h.enumeration.symm p)).trans
    (congrArg (fun q : ↥pending => (⟨q.val, anchor q.val⟩ : GiantSignedParticle P))
      (h.enumeration.apply_symm_apply p))

theorem index_prime (p : ↥pending) : (m.2 (h.index p)).1 = p.val :=
  congrArg (fun z : GiantSignedParticle P => z.1) (h.index_particle_eq p)

theorem index_eq_of_prime_eq (p : ↥pending) {j : Fin m.1} (hj : (m.2 j).1 = p.val) :
    h.index p = j :=
  h.prime_injective ((h.index_prime p).trans hj.symm)

end GiantSignedLifespanMemory

def giantSignedGhostVisitDeleted (i : Fin n) (m : GiantSignedGroupMemory P) : Finset (Fin m.1) := by
  classical
  exact Finset.univ.filter (fun j => giantSignedPrimeGhostDeathAt (c (m.2 j).1) i)

@[simp] theorem mem_giantSignedGhostVisitDeleted (i : Fin n) (m : GiantSignedGroupMemory P)
    (j : Fin m.1) :
    j ∈ giantSignedGhostVisitDeleted c i m ↔ giantSignedPrimeGhostDeathAt (c (m.2 j).1) i := by
  simp only [giantSignedGhostVisitDeleted, Finset.mem_filter, Finset.mem_univ, true_and]

def giantSignedGhostVisitBornLabels {born : Finset P} (order : Fin born.card ≃ ↥born) :
    Fin born.card → P :=
  fun j => (order j).val

theorem giantSignedGhostVisit_deleted_subset_zeros (offset : Fin n → ℤ) (q : Fin n → ℝ)
    (i : Fin n) (m : GiantSignedGroupMemory P)
    (h : GiantSignedLifespanMemory (giantSignedGhostVisitBefore c i)
      (giantSignedLifespanResidue c offset i) m)
    (hw : ∀ p : P, giantSignedResidueLifespanWeight p.val offset q (A p) (c p) ≠ 0) :
    giantSignedGhostVisitDeleted c i m ⊆ giantSignedGhostZeroIndices m := by
  intro j hj
  have hd := (mem_giantSignedGhostVisitDeleted c i m j).mp hj
  have hz := giantSignedLifespanResidue_ghostDeath c offset q i (m.2 j).1 (hw _) hd
  rw [giantSignedGhostZeroIndices, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  exact (congrArg (fun z : GiantSignedParticle P => z.2 = 0) (h.particle_anchor j)).mpr hz

def giantSignedGhostVisitTarget_memory (offset : Fin n → ℤ) (i : Fin n)
    (m : GiantSignedGroupMemory P)
    (h : GiantSignedLifespanMemory (giantSignedGhostVisitBefore c i)
      (giantSignedLifespanResidue c offset i) m)
    (birthOrder : Fin (giantSignedGhostVisitBorn c i).card ≃ ↥(giantSignedGhostVisitBorn c i)) :
    GiantSignedLifespanMemory (giantSignedGhostVisitAfter c i)
      (giantSignedLifespanResidue c offset i)
      (giantSignedGhostTarget m (giantSignedGhostVisitDeleted c i m)
        (giantSignedGhostVisitBornLabels birthOrder)) := by
  classical
  let deleted := giantSignedGhostVisitDeleted c i m
  let oldIndex := (deletedᶜ).orderEmbOfFin rfl
  let old := fun j : Fin (deletedᶜ).card => (m.2 (oldIndex j)).1
  let born := giantSignedGhostVisitBornLabels birthOrder
  have hOld (j : Fin (deletedᶜ).card) :
      giantSignedPrimePendingBefore (c (old j)) i ∧ ¬giantSignedPrimeGhostDeathAt (c (old j)) i := by
    refine ⟨(mem_giantSignedGhostVisitBefore c i _).mp (h.prime_mem (oldIndex j)), ?_⟩
    intro hd
    have hm : oldIndex j ∈ deletedᶜ := Finset.orderEmbOfFin_mem _ rfl j
    exact (Finset.mem_compl.mp hm) ((mem_giantSignedGhostVisitDeleted c i m _).mpr hd)
  have hBorn (j : Fin (giantSignedGhostVisitBorn c i).card) :
      giantSignedPrimeGhostBirthAt (c (born j)) i :=
    (mem_giantSignedGhostVisitBorn c i _).mp (birthOrder j).property
  let indexToPrime : Fin (deletedᶜ).card ⊕ Fin (giantSignedGhostVisitBorn c i).card →
      ↥(giantSignedGhostVisitAfter c i) := fun j =>
    ⟨Sum.elim old born j, by
      apply (mem_giantSignedGhostVisitAfter c i _).mpr
      cases j with
      | inl k =>
        exact (giantSignedPrimePendingAfter_ghostUpdate (c (old k)) i).mpr (Or.inl (hOld k))
      | inr k =>
        exact (giantSignedPrimePendingAfter_ghostUpdate (c (born k)) i).mpr (Or.inr (hBorn k))⟩
  have hinj : Function.Injective indexToPrime := by
    have hprime : Function.Injective (Sum.elim old born) := Sum.elim_injective.mpr
      ⟨h.prime_injective.comp oldIndex.injective, Subtype.val_injective.comp birthOrder.injective,
        fun j k he => (giantSignedPrimeGhostBirthAt_not_pendingBefore (c (born k)) i (hBorn k))
          (he ▸ (hOld j).1)⟩
    intro j k he
    exact hprime (congrArg Subtype.val he)
  have hsurj : Function.Surjective indexToPrime := by
    intro p
    rcases (giantSignedPrimePendingAfter_ghostUpdate (c p.val) i).mp
      ((mem_giantSignedGhostVisitAfter c i p.val).mp p.property) with hp | hp
    · let pBefore : ↥(giantSignedGhostVisitBefore c i) :=
        ⟨p.val, (mem_giantSignedGhostVisitBefore c i p.val).mpr hp.1⟩
      let j := h.index pBefore
      have hj : (m.2 j).1 = p.val := h.index_prime pBefore
      have hjSurvive : j ∈ deletedᶜ := Finset.mem_compl.mpr (fun hd =>
        hp.2 (hj ▸ (mem_giantSignedGhostVisitDeleted c i m j).mp hd))
      have hjRange : j ∈ Set.range oldIndex := by
        change j ∈ Set.range ((deletedᶜ).orderEmbOfFin rfl)
        rw [Finset.range_orderEmbOfFin]
        exact hjSurvive
      obtain ⟨k, hk⟩ := hjRange
      exact ⟨.inl k, Subtype.ext (by simpa only [indexToPrime, Sum.elim_inl, old, hk] using hj)⟩
    · let pBorn : ↥(giantSignedGhostVisitBorn c i) :=
        ⟨p.val, (mem_giantSignedGhostVisitBorn c i p.val).mpr hp⟩
      obtain ⟨k, hk⟩ := birthOrder.surjective pBorn
      refine ⟨.inr k, Subtype.ext ?_⟩
      change (birthOrder k).val = pBorn.val
      exact congrArg Subtype.val hk
  let e := Equiv.ofBijective indexToPrime ⟨hinj, hsurj⟩
  let anchored (p : P) : GiantSignedParticle P := ⟨p, giantSignedLifespanResidue c offset i p⟩
  refine ⟨finSumFinEquiv.symm.trans e, ?_⟩
  intro j
  change Fin ((deletedᶜ).card + (giantSignedGhostVisitBorn c i).card) at j
  refine Fin.addCases ?_ ?_ j
  · intro k
    rw [giantSignedGhostTarget_survivor]
    change m.2 (oldIndex k) = anchored
      (e (finSumFinEquiv.symm (Fin.castAdd (giantSignedGhostVisitBorn c i).card k))).val
    rw [finSumFinEquiv_symm_apply_castAdd]
    exact h.particle_anchor (oldIndex k)
  · intro k
    rw [giantSignedGhostTarget_born]
    change (⟨born k, 0⟩ : GiantSignedParticle P) =
      anchored (e (finSumFinEquiv.symm (Fin.natAdd (deletedᶜ).card k))).val
    rw [finSumFinEquiv_symm_apply_natAdd]
    change (⟨born k, 0⟩ : GiantSignedParticle P) =
      ⟨born k, giantSignedLifespanResidue c offset i (born k)⟩
    rw [giantSignedLifespanResidue_ghostBirth c offset i (born k) (hBorn k)]

theorem giantSignedGhostVisitBirthOrder_card (i : Fin n) :
    Fintype.card (Fin (giantSignedGhostVisitBorn c i).card ≃ ↥(giantSignedGhostVisitBorn c i)) =
      (giantSignedGhostVisitBorn c i).card.factorial := by
  classical
  let e := ((giantSignedGhostVisitBorn c i).orderIsoOfFin rfl).toEquiv
  calc
    _ = Fintype.card (Equiv.Perm (Fin (giantSignedGhostVisitBorn c i).card)) :=
      Fintype.card_congr (Equiv.equivCongr (Equiv.refl _) e.symm)
    _ = _ := by rw [Fintype.card_perm, Fintype.card_fin]

end

end ArtinMatthews

module

public import ArtinMatthews.GiantSignedGhostVisitReconstruction
public import ArtinMatthews.GiantSignedEdgeMemory
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

/-! A fixed family of actual lifespans determines stores, promotions,
and the unique ordered old-index retrieval on each free target list. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {P : Finset ℕ} {n t : ℕ} {A : (p : P) → Finset (Fin n)}
    (c : ∀ p, GiantSignedResidueLifespanChoice (A p))
    (v w : Fin n)

def giantSignedLifespanStoreSlots (source : Fin t → P) : Finset (Fin t) :=
  Finset.univ.filter (fun i => giantSignedPrimeStore (c (source i)) v w)

def giantSignedLifespanPromoteSlots (target : Fin t → P) : Finset (Fin t) :=
  Finset.univ.filter (fun i => giantSignedPrimePromote (c (target i)) v w)

theorem giantSignedLifespanStoreSlots_mem (source : Fin t → P) (i : Fin t) :
    i ∈ giantSignedLifespanStoreSlots c v w source ↔ giantSignedPrimeStore (c (source i)) v w := by
  simp only [giantSignedLifespanStoreSlots, Finset.mem_filter, Finset.mem_univ, true_and]

theorem giantSignedLifespanPromoteSlots_mem (target : Fin t → P) (i : Fin t) :
    i ∈ giantSignedLifespanPromoteSlots c v w target ↔ giantSignedPrimePromote (c (target i)) v w := by
  simp only [giantSignedLifespanPromoteSlots, Finset.mem_filter, Finset.mem_univ, true_and]

theorem giantSignedPrimeStore_active {p : P} (h : giantSignedPrimeStore (c p) v w) :
    v ∈ A p ∧ w ∉ A p := by
  unfold giantSignedPrimeStore at h
  cases hv : giantSignedPrimeLifespanView (A p) (c p) with
  | none => exact (by simpa only [hv, Option.elim_none] using h : False).elim
  | some L =>
      have hh : v ∈ A p ∧ w ∉ A p ∧ w ≤ L.finish := by
        simpa only [hv, Option.elim_some] using h
      exact ⟨hh.1, hh.2.1⟩

theorem giantSignedPrimePendingAfter_inactive {p : P} (h : giantSignedPrimePendingAfter (c p) v) :
    v ∉ A p := by
  unfold giantSignedPrimePendingAfter at h
  cases hv : giantSignedPrimeLifespanView (A p) (c p) with
  | none => exact (by simpa only [hv, Option.elim_none] using h : False).elim
  | some L =>
      have hh : L.start ≤ v ∧ v < L.finish ∧ v ∉ A p := by
        simpa only [hv, Option.elim_some] using h
      exact hh.2.2

theorem giantSignedLifespanPromotionPrime_mem_after (target : Fin t → P)
    (i : Fin (giantSignedLifespanPromoteSlots c v w target).card) :
    giantSignedEdgeSelected (giantSignedLifespanPromoteSlots c v w target) target i ∈ giantSignedGhostVisitAfter c v :=
  (mem_giantSignedGhostVisitAfter c v _).mpr
    (((giantSignedLifespanPromoteSlots_mem c v w target _).mp
      (Finset.orderEmbOfFin_mem _ rfl i)).1)

def giantSignedLifespanRetrieval (target : Fin t → P) (htarget : Function.Injective target)
    (offset : Fin n → ℤ) (m : GiantSignedGroupMemory P)
    (hm : GiantSignedLifespanMemory (giantSignedGhostVisitAfter c v) (giantSignedLifespanResidue c offset v) m) :
    Fin (giantSignedLifespanPromoteSlots c v w target).card ↪ Fin m.1 where
  toFun i := hm.index ⟨giantSignedEdgeSelected (giantSignedLifespanPromoteSlots c v w target) target i,
    giantSignedLifespanPromotionPrime_mem_after c v w target i⟩
  inj' := by
    intro i j h
    apply (giantSignedLifespanPromoteSlots c v w target).orderEmbOfFin rfl |>.injective
    apply htarget
    exact (hm.index_prime ⟨_,giantSignedLifespanPromotionPrime_mem_after c v w target i⟩).symm.trans
      ((congrArg (fun i => (m.2 i).1) h).trans
        (hm.index_prime ⟨_,giantSignedLifespanPromotionPrime_mem_after c v w target j⟩))

theorem giantSignedLifespanRetrieval_particle (target : Fin t → P) (htarget : Function.Injective target)
    (offset : Fin n → ℤ) (m : GiantSignedGroupMemory P)
    (hm : GiantSignedLifespanMemory (giantSignedGhostVisitAfter c v) (giantSignedLifespanResidue c offset v) m)
    (i : Fin (giantSignedLifespanPromoteSlots c v w target).card) :
    let p := giantSignedEdgeSelected (giantSignedLifespanPromoteSlots c v w target) target i
    m.2 (giantSignedLifespanRetrieval c v w target htarget offset m hm i) =
      ⟨p, giantSignedLifespanResidue c offset v p⟩ :=
  hm.index_particle_eq ⟨_,giantSignedLifespanPromotionPrime_mem_after c v w target i⟩

end
end ArtinMatthews

module

public import ArtinMatthews.GiantSignedLifespanEdgeSlots
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

/-! Literal retrieval removes exactly the newly active pending primes. -/
namespace ArtinMatthews
noncomputable section

variable {P : Finset ℕ} {n t : ℕ} {A : (p : P) → Finset (Fin n)}
    (c : ∀ p, GiantSignedResidueLifespanChoice (A p)) (v w : Fin n)
    (offset : Fin n → ℤ) (m : GiantSignedGroupMemory P)
    (hm : GiantSignedLifespanMemory (giantSignedGhostVisitAfter c v) (giantSignedLifespanResidue c offset v) m)
    (target : Fin t → P) (htarget : Function.Injective target)

def giantSignedLifespanRetrieved : Finset (Fin m.1) :=
  Finset.univ.map (giantSignedLifespanRetrieval c v w target htarget offset m hm)

theorem giantSignedLifespanRetrieved_mem
    (hcover : ∀ p, w ∈ A p → v ∉ A p → ∃ j, target j = p)
    (j : Fin m.1) :
    j ∈ giantSignedLifespanRetrieved c v w offset m hm target htarget ↔ w ∈ A (m.2 j).1 := by
  let T := giantSignedLifespanPromoteSlots c v w target
  let E := giantSignedLifespanRetrieval c v w target htarget offset m hm
  change j ∈ Finset.univ.map E ↔ _
  constructor
  · intro hj
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hj
    let p := giantSignedEdgeSelected T target i
    have hprime : (m.2 (E i)).1 = p := congrArg Sigma.fst
      (giantSignedLifespanRetrieval_particle c v w target htarget offset m hm i)
    have hprom : giantSignedPrimePromote (c p) v w :=
      (giantSignedLifespanPromoteSlots_mem c v w target _).mp (Finset.orderEmbOfFin_mem T rfl i)
    exact hprime.symm ▸ hprom.2
  · intro hw
    let p := (m.2 j).1
    have ha : giantSignedPrimePendingAfter (c p) v :=
      (mem_giantSignedGhostVisitAfter c v p).mp (hm.prime_mem j)
    obtain ⟨i,hi⟩ := hcover p hw (giantSignedPrimePendingAfter_inactive c v ha)
    have hT : i ∈ T := (giantSignedLifespanPromoteSlots_mem c v w target i).mpr
      (hi.symm ▸ (show giantSignedPrimePromote (c p) v w from ⟨ha,hw⟩))
    have hiRange : i ∈ Set.range (T.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hT
    obtain ⟨k,hk⟩ := hiRange
    refine Finset.mem_map.mpr ⟨k, Finset.mem_univ _, hm.prime_injective ?_⟩
    have hp : (m.2 (E k)).1 = giantSignedEdgeSelected T target k :=
      congrArg Sigma.fst (giantSignedLifespanRetrieval_particle c v w target htarget offset m hm k)
    exact hp.trans ((congrArg target hk).trans hi)

theorem giantSignedLifespanStoreSelected_surjective (source : Fin t → P)
    (hcover : ∀ p, v ∈ A p → w ∉ A p → ∃ j, source j = p)
    {p : P} (hp : giantSignedPrimeStore (c p) v w) :
    ∃ i : Fin (giantSignedLifespanStoreSlots c v w source).card,
      giantSignedEdgeSelected (giantSignedLifespanStoreSlots c v w source) source i = p := by
  let S := giantSignedLifespanStoreSlots c v w source
  have ha := giantSignedPrimeStore_active c v w hp
  obtain ⟨j,hj⟩ := hcover p ha.1 ha.2
  have hS : j ∈ S := (giantSignedLifespanStoreSlots_mem c v w source j).mpr (hj.symm ▸ hp)
  have hjRange : j ∈ Set.range (S.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact hS
  obtain ⟨i,hi⟩ := hjRange
  exact ⟨i,(congrArg source hi).trans hj⟩

end
end ArtinMatthews

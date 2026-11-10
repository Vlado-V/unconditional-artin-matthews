module

public import ArtinMatthews.MarkedMemoryIndependentEndpointVisits
public import ArtinMatthews.MarkedMemoryIndependentHistory
public import ArtinMatthews.MarkedMemoryNormalizedAnchors
public import ArtinMatthews.MarkedMemoryInitialMeasure
public import ArtinMatthews.MarkedMemoryNormalizedReverseExtraction
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

/-! Nonzero chronological support forces the actual static identity
anchor to agree with every active visit. Initial source atoms and the
normalization of otherwise unused static anchors remain separate. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (order : Fin n → J → Equiv.Perm (Fin pads))

local notation "H" => markedMemoryIndependentHistory hZ d order

theorem markedMemoryIndependent_active_anchor
    (hempty : ∀ j,(d.lifespan j).initial=[])
    (hn : MarkedMemoryBirthNormalized hZ d)
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ H)
    (v : Fin (n+1)) (j : J) (k : Fin (pads+1)) :
    d.particle j (d.activeId v.val j k)=
      markedRawAnchoredParticle (P j) (d.particle j (d.activeId v.val j k)).1
        (d.position v.val).1 (hZ _ (d.position v.val).2) := by
  have hs : ∀ j,((markedMemoryIndependentState hZ d 0 (Nat.zero_le n)).2.2.1.1 j:ℕ)=0 := by
    intro j
    change ((markedMemoryIndependentMemory hZ d 0 (by omega)).1.1 j:ℕ)=0
    rw [markedMemory_initial_memory_empty hZ d hempty]
    rfl
  have hp := markedMemoryBandAddressEquiv_particle hZ d order hs hn j
    (markedMemoryActualActiveIds hZ H (2*v.val) j k)
  rw [markedMemoryBandAddressEquiv_activeId hZ d order (2*v.val) (by omega) j k] at hp
  have ht : 2*v.val/2=v.val := by omega
  rw [ht] at hp
  rw [← hp,markedMemoryActualParticle_active hZ H ha]
  simp only [markedMemoryIndependentHistory_trace_even hZ d order v.val (by omega)]
  rfl

theorem markedMemoryIndependent_identity_active_anchor
    (hempty : ∀ j,(d.lifespan j).initial=[])
    (hn : MarkedMemoryBirthNormalized hZ d)
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ H)
    (j : J) (a : A j) (v : Fin (n+1))
    (hv : v∈markedMemoryIndependentIdentityVisits hZ d j a) :
    d.particle j a=markedRawAnchoredParticle (P j) (d.particle j a).1
      (d.position v.val).1 (hZ _ (d.position v.val).2) := by
  obtain ⟨k,hk⟩ := (d.active_mem v.val (by omega) j a).mp
    ((markedMemoryIndependentIdentityVisits_mem hZ d j a v).mp hv)
  simpa only [hk] using markedMemoryIndependent_active_anchor hZ d order hempty hn ha v j k

end
end ArtinMatthews

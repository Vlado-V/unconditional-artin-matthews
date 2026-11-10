module

public import ArtinMatthews.MarkedMemoryEndpointLaws
public import ArtinMatthews.MarkedMemoryPathEndpointData
public import ArtinMatthews.MarkedMemoryPathEndpointFields
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
public import Mathlib.Tactic.ENatToNat
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

/-! A compatible primewise lifespan assignment satisfies the actual
finite memory laws. The only capacity hypothesis here is the explicit
untruncated finite bound by the number of available band primes. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads n B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (d : MarkedMemoryActivePathData P pads Z n)
  (c : MarkedMemoryPathPrimeChoices (P := P) (n := n))
  (hc : MarkedMemoryPathChoicesCompatible d hZ c)

local notation "Used" => MarkedMemoryPathUsedPrime d c
local notation "E" => markedMemoryPathEndpointData hZ d c hc
local notation "C" => markedMemoryEndpointCanonicalData E
local notation "visits" => markedMemoryPathVisits d
local notation "lines" => markedMemoryPathPrimeLines hZ d

theorem markedMemoryPathEndpoint_queue_laws (j : J) : MarkedMemoryFiniteQueueLaws C j where
  nonempty a := markedMemoryPrimeLifespan_nonempty (lines a.1) (visits j a.1) (c j a.1) (hc j a.1) a.2
  initial_mem := by
    intro a
    constructor
    · intro h
      exact False.elim (List.not_mem_nil h)
    · rintro ⟨hf,_,hn⟩
      have hz : markedMemoryPrimeFirst (visits j a.1) (c j a.1)=0 := Nat.eq_zero_of_le_zero hf
      have hv := markedMemoryPrimeFirst_zero_active (lines a.1) (visits j a.1) (c j a.1) (hc j a.1) a.2 hz
      exact False.elim (hn ((markedMemoryPathEndpoint_active_even hZ d c hc 0 j a).mpr
        ((markedMemoryPathVisits_mem d j a.1 0).mp hv)))
  ghost_active := by
    intro t ht he a
    let v : Fin (n+1) := ⟨t/2,by omega⟩
    have htime : t=2*v.val := by dsimp [v]; omega
    rw [htime]
    exact (markedMemoryPathEndpoint_active_odd hZ d c hc v j a).trans
      (markedMemoryPathEndpoint_active_even hZ d c hc v j a).symm
  ghost_births := by
    intro t ht he a
    exact markedMemoryEndpoint_birthsAt_mem E (markedMemoryEndpointCanonicalBirths E) t ht he j a
  edge_distinct := by
    intro t ht ho
    obtain ⟨v,rfl⟩ := markedMemoryActualOddIndex t ht ho
    rw [markedMemoryPathEndpoint_incomingAt,markedMemoryPathEndpoint_outgoingAt]
    intro h
    exact markedMemoryPath_exchange_distinct d v j (congrArg Subtype.val h)
  edge_outgoing_active := by
    intro t ht ho
    obtain ⟨v,rfl⟩ := markedMemoryActualOddIndex t ht ho
    rw [markedMemoryPathEndpoint_outgoingAt]
    exact (markedMemoryPathEndpoint_active_odd hZ d c hc v.castSucc j _).mpr (d.outgoing_present v j)
  edge_outgoing_alive := by
    intro t ht ho
    obtain ⟨v,rfl⟩ := markedMemoryActualOddIndex t ht ho
    rw [markedMemoryPathEndpoint_outgoingAt]
    have hv := (markedMemoryPathVisits_mem d j (d.outgoing v j) v.castSucc).mpr (d.outgoing_present v j)
    have hf := markedMemoryPrimeFirst_active (lines (d.outgoing v j)) _ _ (hc j _) v.castSucc hv
    have hl := markedMemoryPrimeLast_active (lines (d.outgoing v j)) _ _ (hc j _) v.castSucc hv
    change markedMemoryPrimeFirst (visits j (d.outgoing v j)) (c j (d.outgoing v j)) ≤ 2*v.val+1 ∧
      2*v.val+1 ≤ markedMemoryPrimeLast (visits j (d.outgoing v j)) (c j (d.outgoing v j))
    simp only [Fin.val_castSucc] at hf hl
    omega
  edge_active := by
    intro t ht ho a
    obtain ⟨v,rfl⟩ := markedMemoryActualOddIndex t ht ho
    have hvs : v.succ.val=v.val+1 := rfl
    have hs : 2*v.val+1+1=2*v.succ.val := by omega
    have ha : (C).activeAt (2*v.val+1) j a ↔ ∃ k,d.active v.castSucc j k=a.1 := by
      simpa only [Fin.val_castSucc] using markedMemoryPathEndpoint_active_odd hZ d c hc v.castSucc j a
    rw [hs,markedMemoryPathEndpoint_active_even hZ d c hc v.succ j a,ha,
      markedMemoryPathEndpoint_outgoingAt hZ d c hc v j,
      markedMemoryPathEndpoint_incomingAt hZ d c hc v j]
    simpa only [ne_eq,Subtype.ext_iff,markedMemoryPathOutgoingUsed,markedMemoryPathIncomingUsed] using d.exchange v j a.1
  edge_births := by
    intro t ht ho a hf
    obtain ⟨v,rfl⟩ := markedMemoryActualOddIndex t ht ho
    rw [markedMemoryPathEndpoint_incomingAt]
    apply Subtype.ext
    have hh := markedMemoryPrimeFirst_even_birth (lines a.1) (visits j a.1) (c j a.1)
      (hc j a.1) a.2 v (by exact hf)
    exact markedMemoryPath_incoming_of_new d v j a.1 hh.1 hh.2
  edge_deaths := by
    intro t ht ho a hl
    obtain ⟨v,rfl⟩ := markedMemoryActualOddIndex t ht ho
    rw [markedMemoryPathEndpoint_outgoingAt]
    apply Subtype.ext
    have hh := markedMemoryPrimeLast_odd_death (lines a.1) (visits j a.1) (c j a.1) (hc j a.1) a.2 v hl
    exact markedMemoryPath_outgoing_of_last d v j a.1 hh.1 hh.2

theorem markedMemoryPathEndpoint_laws (hB : (∑ j,(P j).card)≤B) :
    MarkedMemoryFiniteTableauLaws hZ B C where
  lifespan := markedMemoryPathEndpoint_queue_laws hZ d c hc
  active_mem := by
    intro v hv j a
    let w : Fin (n+1) := ⟨v,by omega⟩
    rw [markedMemoryPathEndpoint_active_even hZ d c hc w j a]
    rw [(C).activeIdAt_valid w j]
    constructor
    · rintro ⟨k,hk⟩
      exact ⟨k,Subtype.ext hk⟩
    · rintro ⟨k,hk⟩
      exact ⟨k,congrArg Subtype.val hk⟩
  active_alive := by
    intro v hv j k
    let w : Fin (n+1) := ⟨v,by omega⟩
    rw [(C).activeIdAt_valid w j]
    have hmem := (markedMemoryPathVisits_mem d j (d.active w j k) w).mpr ⟨k,rfl⟩
    exact ⟨markedMemoryPrimeFirst_active (lines (d.active w j k)) _ _ (hc j _) w hmem,
      markedMemoryPrimeLast_active (lines (d.active w j k)) _ _ (hc j _) w hmem⟩
  cutoff := by
    intro t _
    apply le_trans _ hB
    apply Finset.sum_le_sum
    intro j _
    exact (Finset.card_le_univ _).trans ((Fintype.card_subtype_le _).trans (by simp))
  ghost_death_hit := by
    intro v hv j a _ hl _
    let w : Fin (n+1) := ⟨v,by omega⟩
    rw [markedMemoryPathEndpoint_positionAt hZ d c hc w]
    exact markedMemoryPrimeBirthVisit_ghost_death (lines a.1) (visits j a.1) (c j a.1) (hc j a.1) a.2 w hl
  ghost_birth_anchor := by
    intro v hv j a ha
    let w : Fin (n+1) := ⟨v,by omega⟩
    have hf := ((markedMemoryEndpoint_births_mem E (markedMemoryEndpointCanonicalBirths E) w j a).mp ha).1
    have he := markedMemoryPrimeBirthVisit_ghost_birth (visits j a.1) (c j a.1) w hf
    rw [markedMemoryPathEndpoint_positionAt hZ d c hc w]
    change markedRawAnchoredParticle (P j) a.1 _ _=markedRawAnchoredParticle (P j) a.1 _ _
    simp only [he]
  promotion_hit := by
    intro v hv j _ _ _
    let w : Fin n := ⟨v,hv⟩
    rw [markedMemoryPathEndpoint_incomingAt hZ d c hc w j]
    have hp : (C).positionAt (v+1)=d.position w.succ := by
      simpa only [Fin.val_succ] using markedMemoryPathEndpoint_positionAt hZ d c hc w.succ
    simp only [hp]
    have hm := (markedMemoryPathVisits_mem d j (d.incoming w j) w.succ).mpr (d.incoming_present w j)
    exact markedMemoryPrimeBirthVisit_active (lines (d.incoming w j)) _ _ (hc j _) w.succ hm
  store_anchor := by
    intro v hv j _
    let w : Fin n := ⟨v,hv⟩
    rw [markedMemoryPathEndpoint_outgoingAt hZ d c hc w j]
    have hp : (C).positionAt v=d.position w.castSucc := by
      exact markedMemoryPathEndpoint_positionAt hZ d c hc w.castSucc
    simp only [hp]
    have hm := (markedMemoryPathVisits_mem d j (d.outgoing w j) w.castSucc).mpr (d.outgoing_present w j)
    have hh := markedMemoryPrimeBirthVisit_active (lines (d.outgoing w j)) _ _ (hc j _) w.castSucc hm
    change markedRawAnchoredParticle (P j) (d.outgoing w j) _ _=
      markedRawAnchoredParticle (P j) (d.outgoing w j) _ _
    exact Sigma.ext rfl (heq_of_eq hh)

end
end ArtinMatthews

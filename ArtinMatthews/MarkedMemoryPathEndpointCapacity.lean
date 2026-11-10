module

public import ArtinMatthews.MarkedMemoryPathEndpointFamily
public import ArtinMatthews.MarkedMemoryInitialMeasure
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

/-! Endpoint reconstruction at the actual supplied capacity. Only the
literal computed pending-count support is needed. Qualitative fields are
borrowed from the finite laws; no analytic budget uses a larger capacity. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads n B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (d : MarkedMemoryActivePathData P pads Z n)
  (c : MarkedMemoryPathPrimeChoices (P := P) (n := n))
  (hc : MarkedMemoryPathChoicesCompatible d hZ c)

local notation "Used" => MarkedMemoryPathUsedPrime d c
local notation "E" => markedMemoryPathEndpointData hZ d c hc
local notation "C" => markedMemoryEndpointCanonicalData E

abbrev MarkedMemoryPathCapacity (B : ℕ) : Prop :=
  ∀ t,t≤2*n+1 → (∑ j,((C).pendingAt t j).card)≤B

theorem markedMemoryPathEndpoint_laws_of_cutoff
    (hcap : MarkedMemoryPathCapacity hZ d c hc B) :
    MarkedMemoryFiniteTableauLaws hZ B C := by
  let hbase := markedMemoryPathEndpoint_laws (B := ∑ j,(P j).card) hZ d c hc le_rfl
  exact
    { lifespan := hbase.lifespan
      active_mem := hbase.active_mem
      active_alive := hbase.active_alive
      cutoff := hcap
      ghost_death_hit := hbase.ghost_death_hit
      ghost_birth_anchor := hbase.ghost_birth_anchor
      promotion_hit := hbase.promotion_hit
      store_anchor := hbase.store_anchor }

def markedMemoryPathEndpointFamily_of_cutoff
    (hcap : MarkedMemoryPathCapacity hZ d c hc B) :
    MarkedMemoryEndpointFamily (A := Used) (n := n) hZ (markedMemoryActivePathSource (B := B) d) := by
  let hl := markedMemoryPathEndpoint_laws_of_cutoff hZ d c hc hcap
  let f : MarkedMemoryFiniteTableau (A := Used) (P := P) (pads := pads) (B := B) hZ n := ⟨C,hl⟩
  let g := markedMemoryFiniteTableau_toIndependent hZ f
  refine ⟨E,⟨hl,?_,?_⟩⟩
  · have he : ∀ j,(g.lifespan j).initial=[] := by
      intro j
      change markedMemoryFiniteList_toList (markedMemoryFiniteList_ofList [] List.nodup_nil)=[]
      exact markedMemoryFiniteList_toList_ofList [] List.nodup_nil
    have hm := markedMemory_initial_memory_empty hZ g he
    change markedMemoryIndependentState hZ g 0 (Nat.zero_le n)=_
    unfold markedMemoryIndependentState
    rw [hm]
    apply Prod.ext
    · exact markedMemoryPathEndpoint_positionAt hZ d c hc 0
    · apply Prod.ext
      · rfl
      · rfl
  · apply (markedMemoryFiniteAnchorNormalize_fixed_iff hZ C).mpr
    exact markedMemoryPathEndpoint_anchor hZ d c hc

theorem markedMemoryPathEndpoint_pending_le_used (t : ℕ) :
    (∑ j,((C).pendingAt t j).card)≤∑ j,Fintype.card (Used j) := by
  apply Finset.sum_le_sum
  intro j _
  exact Finset.card_le_univ _

theorem markedMemoryPathCapacity_of_used_card
    (hused : (∑ j,Fintype.card (Used j))≤B) : MarkedMemoryPathCapacity hZ d c hc B := by
  intro t _
  exact (markedMemoryPathEndpoint_pending_le_used hZ d c hc t).trans hused

end
end ArtinMatthews

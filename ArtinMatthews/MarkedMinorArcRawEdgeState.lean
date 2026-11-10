module

public import ArtinMatthews.MarkedMinorArcRawGhostState
public import ArtinMatthews.MarkedMinorArcRawStateSplit
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! The literal store/promote edge state transition. Promotions select only
indexed old particles; stored source labels are appended afterwards, so a
new store can never be promoted on the same edge. Fresh labels exist only
in the groups actually drawn freshly, preventing multiplicity inflation. -/
namespace ArtinMatthews
open scoped BigOperators

abbrev MarkedRawEdgePromotions {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {B : ℕ} (m : MarkedRawMemory P B) := (j : J) → Option (Fin (m.1.1 j : ℕ))

/-- Fresh label type is a singleton for a promoted group, so such a group
has no redundant prime-label choice or prime integration. -/
abbrev MarkedRawEdgeFreshLabels {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {B : ℕ} {m : MarkedRawMemory P B} (prom : MarkedRawEdgePromotions m) :=
  (j : J) → match prom j with | none => ↥(P j) | some _ => PUnit

/-- Exactly the selected old promotion indices are removed. -/
def markedRawEdgePromotionDeletion {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {B : ℕ} {m : MarkedRawMemory P B} (prom : MarkedRawEdgePromotions m) : MarkedRawGhostDeletion m :=
  fun j => (prom j).toFinset

/-- The one unshared target slot is either the actual chosen old particle's
prime or the actual fresh prime, with no promotion of newly stored labels. -/
def markedRawEdgeTargetLast {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {B : ℕ} (m : MarkedRawMemory P B) (prom : MarkedRawEdgePromotions m)
    (fresh : MarkedRawEdgeFreshLabels prom) (j : J) : ↥(P j) :=
  match h : prom j with
  | none => by simpa only [h] using fresh j
  | some k => (m.2 j k).1

/-- Literal finite edge choices, preserving the source total pending cutoff. -/
structure MarkedRawEdgeChoice {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z) where
  target : Z
  store : J → Bool
  promotions : MarkedRawEdgePromotions s.2.2
  fresh : MarkedRawEdgeFreshLabels promotions
  promotion_hits : ∀ j k, promotions j=some k →
    MarkedRawParticleHits (P j) target.1 (hZ _ target.2) (s.2.2.2 j k)
  memory_bound : (∑ j, ((markedRawGhostSurvivors s.2.2 (markedRawEdgePromotionDeletion promotions) j).card+
    (if store j then 1 else 0))) ≤ B

/-- The actual stores are a zero-or-one birth batch per group. -/
def markedRawEdgeStoreSizes {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) :
    MarkedRawGhostBirthSizes s.2.2 (markedRawEdgePromotionDeletion choice.promotions) :=
  ⟨fun j => ⟨if choice.store j then 1 else 0,by
      have hh := (Finset.single_le_sum (fun i _ => Nat.zero_le
        ((markedRawGhostSurvivors s.2.2 (markedRawEdgePromotionDeletion choice.promotions) i).card+
          (if choice.store i then 1 else 0))) (Finset.mem_univ j)).trans choice.memory_bound
      omega⟩,choice.memory_bound⟩

/-- Literal edge target memory: remove selected old promotions, then store
chosen source last labels at the source anchors, not at target anchors. -/
noncomputable def markedRawEdgeTargetMemory {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) : MarkedRawMemory P B :=
  markedRawGhostTargetMemory s.2.2 s.1.1 (hZ _ s.1.2)
    (markedRawEdgePromotionDeletion choice.promotions) (markedRawEdgeStoreSizes hZ s choice)
    (fun j _ => ((markedRawActiveSplit pads) s.2.1).2 j)

/-- The exact literal store/promote target state, with copied slots retained. -/
noncomputable def markedRawEdgeTargetState {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) : MarkedRawState P (pads+1) B Z :=
  (choice.target,((markedRawActiveSplit pads).symm
    (((markedRawActiveSplit pads) s.2.1).1,
      markedRawEdgeTargetLast s.2.2 choice.promotions choice.fresh),markedRawEdgeTargetMemory hZ s choice))

/-- Every shared slot is copied literally in the real edge transition. -/
theorem markedRawEdgeTargetState_copied {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) :
    ((markedRawActiveSplit pads) (markedRawEdgeTargetState hZ s choice).2.1).1=
      ((markedRawActiveSplit pads) s.2.1).1 := by
  change ((markedRawActiveSplit pads) ((markedRawActiveSplit pads).symm _)).1=_
  rw [Equiv.apply_symm_apply]

/-- The old promotion choice supplies exactly the corresponding old prime. -/
theorem markedRawEdgeTargetLast_promoted {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {B : ℕ} (m : MarkedRawMemory P B) (prom : MarkedRawEdgePromotions m)
    (fresh : MarkedRawEdgeFreshLabels prom) (j : J) (k : Fin (m.1.1 j : ℕ)) (hk : prom j=some k) :
    markedRawEdgeTargetLast m prom fresh j=(m.2 j k).1 := by
  unfold markedRawEdgeTargetLast
  split
  · rename_i hn
    rw [hk] at hn
    cases hn
  · rename_i k' hsome
    have he : k'=k := Option.some.inj (hsome.symm.trans hk)
    rw [he]

/-- Actual deletion masks are eligible at the target because promotion
indices are chosen from the old hit set, before any newly stored particle. -/
theorem markedRawEdgePromotionDeletion_allowed {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) :
    MarkedRawGhostDeletionAllowed s.2.2 choice.target.1 (hZ _ choice.target.2)
      (markedRawEdgePromotionDeletion choice.promotions) := by
  classical
  intro j k hk
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _,choice.promotion_hits j k (by simpa only [markedRawEdgePromotionDeletion,Option.mem_toFinset,Option.mem_def] using hk)⟩

end ArtinMatthews

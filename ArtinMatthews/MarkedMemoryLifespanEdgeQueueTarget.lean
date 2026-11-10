module

public import ArtinMatthews.MarkedMemoryLifespanEdgeQueue
public import ArtinMatthews.MarkedMemoryQueueState
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

/-! The independently constructed edge queue is the literal target
memory: promotion removes an old identity before an optional source-last
store is appended. Both its prime and its source anchor are preserved. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

variable {J : Type*} [Fintype J] {A : J → Type*} [∀ j, DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z target : Z)
  (active : MarkedRawActive P (pads+1)) (queue : (j : J) → List (A j))
  (hq : ∀ j, (queue j).Nodup) (incoming outgoing : (j : J) → A j) (store : J → Bool)
  (particle : (j : J) → A j → MarkedRawParticle (P j))
  (hsource : (∑ j, (queue j).length) ≤ B)
  (hhit : ∀ j k, (queue j).get k = incoming j →
    MarkedRawParticleHits (P j) target.1 (hZ _ target.2) (particle j ((queue j).get k)))
  (htarget : (∑ j, (markedMemoryEdgeQueueAfter queue hq incoming outgoing store j).length) ≤ B)

omit [∀ j, DecidableEq (A j)] in
/-- The store condition is needed only in bands whose outgoing active
identity continues. All other entries are copied from the old queue. -/
theorem markedMemoryEdgeQueueChoice_target_memory
    (hstore : ∀ j, store j = true → particle j (outgoing j) =
      markedRawAnchoredParticle (P j) (((markedRawActiveSplit pads) active).2 j)
        z.1 (hZ _ z.2)) :
    markedRawEdgeTargetMemory hZ (z,(active,markedMemoryLabeledQueueState queue particle hsource))
      (markedMemoryEdgeQueueChoice hZ z target active queue hq incoming outgoing store
        particle hsource hhit htarget) =
      markedMemoryLabeledQueueState (markedMemoryEdgeQueueAfter queue hq incoming outgoing store)
        particle htarget := by
  apply markedMemoryState_eq_of_lists
  intro j
  unfold markedRawEdgeTargetMemory
  rw [markedMemoryGhostTargetMemory_list, markedMemoryLabeledQueueState_list]
  change List.ofFn (fun k => particle j ((queue j).get
      ((Finset.univ \ (markedMemoryEdgeQueuePromotion queue hq incoming j).toFinset).orderEmbOfFin rfl k))) ++
      List.ofFn (fun _ : Fin (if store j then 1 else 0) => markedRawAnchoredParticle (P j)
        (((markedRawActiveSplit pads) active).2 j) z.1 (hZ _ z.2)) = _
  rw [markedMemoryEdgeQueueAfter, List.map_append]
  apply congrArg₂ (fun x y => x ++ y)
  · simp only [markedMemoryRetainedQueue, List.map_ofFn]
    rfl
  · cases hs : store j with
    | false => simp
    | true => simp [hstore j hs]

end
end ArtinMatthews

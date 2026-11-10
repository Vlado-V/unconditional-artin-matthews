module

public import ArtinMatthews.MarkedMemoryEdgeOriginLabels
public import ArtinMatthews.MarkedMemoryLifespanEdgeQueue
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

/-! The target identity list of a queue-reconstructed edge is its
literal promotion-then-store queue. This small constructor calculation
avoids unfolding a whole independent schedule during later transport. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

variable {J : Type*} [Fintype J] {A : J → Type*}
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z target : Z)
  (active : MarkedRawActive P (pads+1)) (ids : (j : J) → Fin (pads+1) → A j)
  (queue : (j : J) → List (A j)) (hq : ∀ j, (queue j).Nodup)
  (incoming outgoing : (j : J) → A j) (store : J → Bool)
  (particle : (j : J) → A j → MarkedRawParticle (P j)) (hsource : (∑ j, (queue j).length) ≤ B)
  (hhit : ∀ j k, (queue j).get k = incoming j →
    MarkedRawParticleHits (P j) target.1 (hZ _ target.2) (particle j ((queue j).get k)))
  (htarget : (∑ j, (markedMemoryEdgeQueueAfter queue hq incoming outgoing store j).length) ≤ B)

theorem markedMemoryEdgeQueueLabel_pending_list
    (hout : ∀ j, ids j (Fin.last pads) = outgoing j) (j : J) :
    List.ofFn (fun k => markedMemoryEdgeTargetGroupLabel hZ
      (z,(active,markedMemoryLabeledQueueState queue particle hsource))
      (markedMemoryEdgeQueueChoice hZ z target active queue hq incoming outgoing store particle hsource hhit htarget)
      ids (fun j => (queue j).get) incoming j (Sum.inr k)) =
      markedMemoryEdgeQueueAfter queue hq incoming outgoing store j := by
  calc
    _ = _ := markedMemoryEdgeTargetGroupLabel_pending_list hZ
      (z,(active,markedMemoryLabeledQueueState queue particle hsource))
      (markedMemoryEdgeQueueChoice hZ z target active queue hq incoming outgoing store particle hsource hhit htarget)
      ids (fun j => (queue j).get) incoming j
    _ = _ := by
      change List.ofFn (fun k => (queue j).get
          ((Finset.univ \ (markedMemoryEdgeQueuePromotion queue hq incoming j).toFinset).orderEmbOfFin rfl k)) ++
          List.ofFn (fun _ : Fin (if store j then 1 else 0) => ids j (Fin.last pads)) = _
      rw [hout]
      unfold markedMemoryEdgeQueueAfter
      apply congrArg₂ (fun x y => x ++ y)
      · rfl
      · cases store j <;> simp

end
end ArtinMatthews

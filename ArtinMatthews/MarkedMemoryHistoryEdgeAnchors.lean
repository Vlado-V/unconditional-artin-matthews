module

public import ArtinMatthews.MarkedMemoryHistoryAnchors
public import ArtinMatthews.MarkedMemoryHistoryEdgeOrigins
public import ArtinMatthews.MarkedMinorArcProjectiveLine
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

/-! Actual edge origins transport prime-and-projective-anchor marks. Copied
slots use the literal shared-product determinant gate; old promotions use
their actual hit proof, and stores retain the source anchor. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

 theorem markedMemoryPositionLine_eq_of_prime_dvd (p : Nat.Primes)
    (z v : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (hv : IsCoprime v.1 v.2)
    (hd : (p : ℤ) ∣ markedMinorIntegerDet z v) :
    markedPrimePositionLine (p : ℕ) z hz = markedPrimePositionLine (p : ℕ) v hv := by
  obtain ⟨w, hw⟩ := markedPrimitivePosition_completion z hz
  apply (markedPrimePositionLine_eq_iff_same (p : ℕ) z v hz hv).mpr
  exact (markedMinorSamePrimeLine_iff_dvd p.2 z w v hw hv).mpr hd

 theorem markedRawCopiedProduct_dvd_slot {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads : ℕ} (copied : MarkedRawActive P pads)
    (j : J) (k : Fin pads) : ((copied j k).1 : ℕ) ∣ markedRawCopiedProduct copied := by
  classical
  exact (Finset.dvd_prod_of_mem (fun k : Fin pads => ((copied j k).1 : ℕ)) (Finset.mem_univ k)).trans
    (Finset.dvd_prod_of_mem (fun j : J => ∏ k : Fin pads, ((copied j k).1 : ℕ)) (Finset.mem_univ j))

 def MarkedMemoryRawEdgeAnchorGate {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) : Prop :=
  (markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1 : ℤ) ∣
    markedMinorIntegerDet s.1.1 choice.target.1

 theorem markedMemoryRawEdge_copied_line {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) (hg : MarkedMemoryRawEdgeAnchorGate hZ s choice)
    (j : J) (k : Fin pads) :
    markedPrimePositionLine ((s.2.1 j k.castSucc).1 : ℕ) s.1.1 (hZ _ s.1.2) =
      markedPrimePositionLine ((s.2.1 j k.castSucc).1 : ℕ) choice.target.1 (hZ _ choice.target.2) := by
  apply markedMemoryPositionLine_eq_of_prime_dvd
  have hd : (((s.2.1 j k.castSucc).1 : ℕ) : ℤ) ∣
      (markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1 : ℤ) := by
    exact_mod_cast markedRawCopiedProduct_dvd_slot ((markedRawActiveSplit pads) s.2.1).1 j k
  exact hd.trans hg

 theorem markedMemoryRawEdge_active_last {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) (j : J) :
    (markedRawEdgeTargetState hZ s choice).2.1 j (Fin.last pads) =
      markedRawEdgeTargetLast s.2.2 choice.promotions choice.fresh j := by
  change Fin.snoc (α := fun _ => ↥(P j)) (fun k : Fin pads => s.2.1 j k.castSucc)
    (markedRawEdgeTargetLast s.2.2 choice.promotions choice.fresh j) (Fin.last pads) = _
  exact Fin.snoc_last (α := fun _ => ↥(P j)) _ _

 theorem markedMemoryRawEdge_active_copied {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) (j : J) (k : Fin pads) :
    (markedRawEdgeTargetState hZ s choice).2.1 j k.castSucc = s.2.1 j k.castSucc := by
  change Fin.snoc (α := fun _ => ↥(P j)) (fun k : Fin pads => s.2.1 j k.castSucc)
    (markedRawEdgeTargetLast s.2.2 choice.promotions choice.fresh j) k.castSucc = _
  exact Fin.snoc_castSucc (α := fun _ => ↥(P j)) _ _ _

 def markedMemoryPopulationGroupAnchor {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P M B Z) (j : J) :
    (Fin M ⊕ Fin (s.2.2.1.1 j : ℕ)) → MarkedMemoryAnchoredPrime :=
  Sum.elim (fun i => ⟨(s.2.1 j i).1,
    markedPrimePositionLine ((s.2.1 j i).1 : ℕ) s.1.1 (hZ _ s.1.2)⟩)
    (fun i => markedMemoryForgetBandParticle (s.2.2.2 j i))

 def markedMemoryEdgeFreshOriginAnchor {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) (_j : {j : J // choice.promotions j = none}) :
    MarkedMemoryAnchoredPrime :=
  ⟨(markedRawEdgeTargetLast s.2.2 choice.promotions choice.fresh _j.1).1,
    markedPrimePositionLine
      ((markedRawEdgeTargetLast s.2.2 choice.promotions choice.fresh _j.1).1 : ℕ)
      choice.target.1 (hZ _ choice.target.2)⟩

 theorem markedMemoryForgetBandParticle_eq_current {P : Finset Nat.Primes}
    (a : MarkedRawParticle P) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (ha : MarkedRawParticleHits P z hz a) :
    markedMemoryForgetBandParticle a = ⟨a.1.1, markedPrimePositionLine (a.1.1 : ℕ) z hz⟩ :=
  congrArg (Sigma.mk a.1.1) ha

 theorem markedMemoryEdgeGroupOrigin_anchor {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) (hg : MarkedMemoryRawEdgeAnchorGate hZ s choice) (j : J)
    (i : Fin (pads+1) ⊕ Fin ((markedRawEdgeTargetMemory hZ s choice).1.1 j : ℕ)) :
    Sum.elim (markedMemoryPopulationGroupAnchor hZ s j)
      (fun _ : PLift (choice.promotions j = none) =>
        (⟨(markedRawEdgeTargetLast s.2.2 choice.promotions choice.fresh j).1,
          markedPrimePositionLine
            ((markedRawEdgeTargetLast s.2.2 choice.promotions choice.fresh j).1 : ℕ)
            choice.target.1 (hZ _ choice.target.2)⟩ : MarkedMemoryAnchoredPrime))
      (markedMemoryEdgeGroupOrigin hZ s choice j i) =
      markedMemoryPopulationGroupAnchor hZ (markedRawEdgeTargetState hZ s choice) j i := by
  rcases i with i | i
  · refine Fin.lastCases ?_ (fun k => ?_) i
    · by_cases hn : choice.promotions j = none
      · rw [markedMemoryEdgeGroupOrigin_last_none hZ s choice j hn]
        change (⟨(markedRawEdgeTargetLast s.2.2 choice.promotions choice.fresh j).1,
          markedPrimePositionLine ((markedRawEdgeTargetLast s.2.2 choice.promotions choice.fresh j).1 : ℕ)
            choice.target.1 (hZ _ choice.target.2)⟩ : MarkedMemoryAnchoredPrime) =
          ⟨((markedRawEdgeTargetState hZ s choice).2.1 j (Fin.last pads)).1,
            markedPrimePositionLine (((markedRawEdgeTargetState hZ s choice).2.1 j (Fin.last pads)).1 : ℕ)
              choice.target.1 (hZ _ choice.target.2)⟩
        rw [markedMemoryRawEdge_active_last]
      · obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hn
        rw [markedMemoryEdgeGroupOrigin_last_some hZ s choice j k hk]
        change markedMemoryForgetBandParticle (s.2.2.2 j k) =
          ⟨((markedRawEdgeTargetState hZ s choice).2.1 j (Fin.last pads)).1,
            markedPrimePositionLine (((markedRawEdgeTargetState hZ s choice).2.1 j (Fin.last pads)).1 : ℕ)
              choice.target.1 (hZ _ choice.target.2)⟩
        rw [markedMemoryRawEdge_active_last,
          markedRawEdgeTargetLast_promoted s.2.2 choice.promotions choice.fresh j k hk]
        exact markedMemoryForgetBandParticle_eq_current (s.2.2.2 j k) choice.target.1
          (hZ _ choice.target.2) (choice.promotion_hits j k hk)
    · rw [markedMemoryEdgeGroupOrigin_copied]
      change (⟨(s.2.1 j k.castSucc).1,
        markedPrimePositionLine ((s.2.1 j k.castSucc).1 : ℕ) s.1.1 (hZ _ s.1.2)⟩ : MarkedMemoryAnchoredPrime) =
        ⟨((markedRawEdgeTargetState hZ s choice).2.1 j k.castSucc).1,
          markedPrimePositionLine (((markedRawEdgeTargetState hZ s choice).2.1 j k.castSucc).1 : ℕ)
            choice.target.1 (hZ _ choice.target.2)⟩
      rw [markedMemoryRawEdge_active_copied]
      exact congrArg (fun l : MarkedRawPrimeLine (s.2.1 j k.castSucc).1 =>
        (⟨(s.2.1 j k.castSucc).1, l⟩ : MarkedMemoryAnchoredPrime))
          (markedMemoryRawEdge_copied_line hZ s choice hg j k)
  · obtain ⟨v, rfl⟩ := (markedMemoryGhostOrigin s.2.2
      (markedRawEdgePromotionDeletion choice.promotions) (markedRawEdgeStoreSizes hZ s choice) j).symm.surjective i
    cases v with
    | inl old =>
      rw [markedMemoryEdgeGroupOrigin_survivor]
      exact congrArg markedMemoryForgetBandParticle
        (markedMemoryGhostOrigin_old s.2.2 s.1.1 (hZ _ s.1.2)
          (markedRawEdgePromotionDeletion choice.promotions) (markedRawEdgeStoreSizes hZ s choice)
          (fun j _ => ((markedRawActiveSplit pads) s.2.1).2 j) j old).symm
    | inr stored =>
      rw [markedMemoryEdgeGroupOrigin_store]
      change (⟨(s.2.1 j (Fin.last pads)).1,
        markedPrimePositionLine ((s.2.1 j (Fin.last pads)).1 : ℕ) s.1.1 (hZ _ s.1.2)⟩ : MarkedMemoryAnchoredPrime) =
        markedMemoryForgetBandParticle
          ((markedRawEdgeTargetMemory hZ s choice).2 j
            ((markedMemoryGhostOrigin s.2.2 (markedRawEdgePromotionDeletion choice.promotions)
              (markedRawEdgeStoreSizes hZ s choice) j).symm (Sum.inr stored)))
      exact congrArg markedMemoryForgetBandParticle
        (markedMemoryGhostOrigin_birth s.2.2 s.1.1 (hZ _ s.1.2)
          (markedRawEdgePromotionDeletion choice.promotions) (markedRawEdgeStoreSizes hZ s choice)
          (fun j _ => ((markedRawActiveSplit pads) s.2.1).2 j) j stored).symm

end
end ArtinMatthews

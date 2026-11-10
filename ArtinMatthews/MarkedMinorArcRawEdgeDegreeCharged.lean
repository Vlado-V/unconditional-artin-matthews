module

public import ArtinMatthews.MarkedMinorArcRawEdgeChargedAction
public import ArtinMatthews.MarkedMinorArcRawEdgeCoupledTranspose
public import ArtinMatthews.MarkedMinorArcRawEdgeDegreeTransport
public import ArtinMatthews.MarkedMinorArcRawEdgeDegreeEligibility
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

/-! Exact transport of the charged literal choice sum to the previously
proved coupled indexed store/promote component. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem markedRawEdge_degree_charge
    {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (x : Z) (active : MarkedRawActive P (pads+1))
    (y : Z) (a : MarkedRawEdgeDegreeShape J B)
    (data : MarkedRawEdgeDegreePayload P y.1 (hZ _ y.2) a) :
    let c := markedRawEdgeDegreeMemoryChoice hZ x active y a data
    markedRawEdgeChoiceCharge δ γ hZ (x,(active,c.1)) c.2 =
      ∏ j, δ j ^ markedRawEdgeBit (a.1.promoted j) *
        γ j ^ markedRawEdgeBit (a.1.stored j) := by
  dsimp only
  unfold markedRawEdgeChoiceCharge
  apply Finset.prod_congr rfl
  intro j _
  rw [markedRawEdge_degree_promoted, markedRawEdge_degree_stored]
  rfl

theorem markedRawEdge_degree_fresh_mass
    {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (x : Z) (active : MarkedRawActive P (pads+1))
    (y : Z) (a : MarkedRawEdgeDegreeShape J B)
    (data : MarkedRawEdgeDegreePayload P y.1 (hZ _ y.2) a) :
    let c := markedRawEdgeDegreeMemoryChoice hZ x active y a data
    markedRawEdgeChoiceFreshMass ν hZ (x,(active,c.1)) c.2 =
      markedRawEdgeFreePrimeMass (fun j p => (ν j p : ℂ))
        (fun j => markedRawEdgeBit (a.1.promoted j)) data.2.1 := by
  dsimp only
  unfold markedRawEdgeChoiceFreshMass
  rw [markedRawEdge_degree_prime_mass]
  simp only [Complex.ofReal_prod]
  unfold markedRawEdgeFreePrimeMass
  apply Finset.prod_congr rfl
  intro j _
  by_cases hp : a.1.promoted j <;> simp [markedRawEdgeBit,hp]

def markedRawEdgeDegreeChoicePairing
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (x : Z) (active : MarkedRawActive P (pads+1))
    (y : Z) (a : MarkedRawEdgeDegreeShape J B)
    (data : MarkedRawEdgeDegreePayload P y.1 (hZ _ y.2) a)
    (K : MarkedRawState P (pads+1) B Z → MarkedRawState P (pads+1) B Z → ℂ) : ℂ :=
  let c := markedRawEdgeDegreeMemoryChoice hZ x active y a data
  (markedRawMemoryMass ν c.1 : ℂ) * markedRawEdgeChoiceCharge δ γ hZ (x,(active,c.1)) c.2 *
    markedRawEdgeChoiceFreshMass ν hZ (x,(active,c.1)) c.2 *
    K (x,(active,c.1)) (markedRawEdgeTargetState hZ (x,(active,c.1)) c.2)

theorem markedRawEdge_degree_choice_pairing
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (x : Z) (active : MarkedRawActive P (pads+1))
    (y : Z) (a : MarkedRawEdgeDegreeShape J B)
    (data : MarkedRawEdgeDegreePayload P y.1 (hZ _ y.2) a)
    (K : MarkedRawState P (pads+1) B Z → MarkedRawState P (pads+1) B Z → ℂ) :
    markedRawEdgeDegreeChoicePairing ν δ γ hZ x active y a data K =
      ((∏ j, ∏ i, (ν j (data.1.1 j i).1 : ℂ)) /
        (∏ j, (Nat.factorial (a.1.survivors j + markedRawEdgeBit (a.1.promoted j)) : ℂ))) *
      (∏ j, δ j ^ markedRawEdgeBit (a.1.promoted j) * γ j ^ markedRawEdgeBit (a.1.stored j)) *
      markedRawEdgeFreePrimeMass (fun j p => (ν j p : ℂ))
        (fun j => markedRawEdgeBit (a.1.promoted j)) data.2.1 *
      K (x,(active,markedRawMemoryOfDegrees P
        (fun j => a.1.survivors j + markedRawEdgeBit (a.1.promoted j)) a.1.source_le data.1.1))
        (y,((markedRawActiveSplit pads).symm (((markedRawActiveSplit pads) active).1,data.2.1),
          markedRawMemoryOfDegrees P
            (fun j => a.1.survivors j + markedRawEdgeBit (a.1.stored j)) a.1.target_le
            (markedRawEdgeDegreeTargetTuple hZ x active y a data))) := by
  unfold markedRawEdgeDegreeChoicePairing
  dsimp only
  rw [markedRawEdge_degree_charge, markedRawEdge_degree_fresh_mass,
    markedRawEdge_degree_target, markedRawEdge_degree_source,
    markedRawMemoryOfDegrees_mass_complex]
  rfl

def markedRawEdgeDegreeIntegrand
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (x : Z) (active : MarkedRawActive P (pads+1))
    (y : Z) (a : MarkedRawEdgeDegreeShape J B)
    (K : MarkedRawState P (pads+1) B Z → MarkedRawState P (pads+1) B Z → ℂ)
    (old : (j : J) → Fin (a.1.survivors j + markedRawEdgeBit (a.1.promoted j)) →
      MarkedRawParticle (P j)) (b : (j : J) → ↥(P j)) : ℂ :=
  ((∏ j, ∏ i, (ν j (old j i).1 : ℂ)) /
    (∏ j, (Nat.factorial (a.1.survivors j + markedRawEdgeBit (a.1.promoted j)) : ℂ))) *
  (∏ j, δ j ^ markedRawEdgeBit (a.1.promoted j) * γ j ^ markedRawEdgeBit (a.1.stored j)) *
  markedRawEdgeFreePrimeMass (fun j p => (ν j p : ℂ))
    (fun j => markedRawEdgeBit (a.1.promoted j)) b *
  K (x,(active,markedRawMemoryOfDegrees P
    (fun j => a.1.survivors j + markedRawEdgeBit (a.1.promoted j)) a.1.source_le old))
    (y,((markedRawActiveSplit pads).symm (((markedRawActiveSplit pads) active).1,b),
      markedRawMemoryOfDegrees P
        (fun j => a.1.survivors j + markedRawEdgeBit (a.1.stored j)) a.1.target_le
        (fun j => Fin.addCases
          (markedRawSurvivorTupleCast (a.2 j).1
            (markedRawDeletionBatch_survivor_card rfl (a.2 j)) (old j))
          (fun _ => markedRawAnchoredParticle (P j) (((markedRawActiveSplit pads) active).2 j)
            x.1 (hZ _ x.2)))))

theorem markedRawEdge_degree_choice_integrand
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (x : Z) (active : MarkedRawActive P (pads+1))
    (y : Z) (a : MarkedRawEdgeDegreeShape J B)
    (data : MarkedRawEdgeDegreePayload P y.1 (hZ _ y.2) a)
    (K : MarkedRawState P (pads+1) B Z → MarkedRawState P (pads+1) B Z → ℂ) :
    markedRawEdgeDegreeChoicePairing ν δ γ hZ x active y a data K =
      markedRawEdgeDegreeIntegrand ν δ γ hZ x active y a K data.1.1 data.2.1 := by
  rw [markedRawEdge_degree_choice_pairing]
  unfold markedRawEdgeDegreeIntegrand
  rfl

attribute [local irreducible] markedRawEdgeDegreeIntegrand

set_option backward.isDefEq.respectTransparency true in
theorem markedRawEdge_degree_payload_charged_sum
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (x : Z) (active : MarkedRawActive P (pads+1))
    (y : Z) (a : MarkedRawEdgeDegreeShape J B)
    (K : MarkedRawState P (pads+1) B Z → MarkedRawState P (pads+1) B Z → ℂ) :
    (∑ data : MarkedRawEdgeDegreePayload P y.1 (hZ _ y.2) a,
      markedRawEdgeDegreeChoicePairing ν δ γ hZ x active y a data K) =
      ∑ old : (j : J) → Fin (a.1.survivors j + markedRawEdgeBit (a.1.promoted j)) →
        MarkedRawParticle (P j), ∑ b : (j : J) → ↥(P j),
          (∏ j, ∏ i, if MarkedRawParticleHits (P j) y.1 (hZ _ y.2)
            (markedRawDeletedTupleCast (a.2 j).1 (markedRawDeletionBatch_deleted_card (a.2 j))
              (old j) i) then (1 : ℂ) else 0) *
          (if MarkedRawEdgeRetrievedSlots (fun j i =>
            (markedRawDeletedTupleCast (a.2 j).1 (markedRawDeletionBatch_deleted_card (a.2 j))
              (old j) i).1) b then (1 : ℂ) else 0) *
          markedRawEdgeDegreeIntegrand ν δ γ hZ x active y a K old b := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  calc
    _ = ∑ data : MarkedRawEdgeDegreePayload P y.1 (hZ _ y.2) a,
        markedRawEdgeDegreeIntegrand ν δ γ hZ x active y a K data.1.1 data.2.1 := by
      apply Finset.sum_congr rfl
      intro data _
      exact markedRawEdge_degree_choice_integrand ν δ γ hZ x active y a data K
    _ = _ := by
      have hpayload := markedRawEdge_degree_payload_indicator_sum (J := J) (B := B)
        P y.1 (hZ _ y.2) a (markedRawEdgeDegreeIntegrand ν δ γ hZ x active y a K)
      exact hpayload

/-- Every original old-index choice and constrained target label becomes
exactly the coupled component used in the factorial transpose. -/
theorem markedRawEdge_degree_component_sum
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (x y : Z)
    (copied : MarkedRawActive P pads) (last : (j : J) → ↥(P j))
    (t : MarkedRawEdgeDegrees J B)
    (K : MarkedRawState P (pads+1) B Z → MarkedRawState P (pads+1) B Z → ℂ) :
    (∑ S : (j : J) → MarkedRawDeletionBatch
      (t.survivors j + markedRawEdgeBit (t.promoted j)) (markedRawEdgeBit (t.promoted j)),
      ∑ data : MarkedRawEdgeDegreePayload P y.1 (hZ _ y.2) ⟨t,S⟩,
        markedRawEdgeDegreeChoicePairing ν δ γ hZ x
          ((markedRawActiveSplit pads).symm (copied,last)) y ⟨t,S⟩ data K) =
      ∑ old : (j : J) → Fin (t.survivors j + markedRawEdgeBit (t.promoted j)) →
        MarkedRawParticle (P j),
        ((∏ j, ∏ i, (ν j (old j i).1 : ℂ)) /
          (∏ j, (Nat.factorial (t.survivors j + markedRawEdgeBit (t.promoted j)) : ℂ))) *
          markedRawEdgeSlotComponent P (fun j p => (ν j p : ℂ)) x.1 y.1 (hZ _ x.2) (hZ _ y.2)
            t.survivors (fun j => markedRawEdgeBit (t.promoted j))
            (fun j => markedRawEdgeBit (t.stored j)) δ γ last
            (fun old b new => K
              (x,((markedRawActiveSplit pads).symm (copied,last),
                markedRawMemoryOfDegrees P
                  (fun j => t.survivors j + markedRawEdgeBit (t.promoted j)) t.source_le old))
              (y,((markedRawActiveSplit pads).symm (copied,b),
                markedRawMemoryOfDegrees P
                  (fun j => t.survivors j + markedRawEdgeBit (t.stored j)) t.target_le new))) old := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  let W := fun (S : (j : J) → MarkedRawDeletionBatch
      (t.survivors j + markedRawEdgeBit (t.promoted j)) (markedRawEdgeBit (t.promoted j)))
      (old : (j : J) → Fin (t.survivors j + markedRawEdgeBit (t.promoted j)) →
        MarkedRawParticle (P j)) (b : (j : J) → ↥(P j)) =>
    (∏ j, ∏ i, if MarkedRawParticleHits (P j) y.1 (hZ _ y.2)
      (markedRawDeletedTupleCast (S j).1 (markedRawDeletionBatch_deleted_card (S j)) (old j) i)
      then (1 : ℂ) else 0) *
    (if MarkedRawEdgeRetrievedSlots (fun j i =>
      (markedRawDeletedTupleCast (S j).1 (markedRawDeletionBatch_deleted_card (S j)) (old j) i).1) b
      then (1 : ℂ) else 0) *
    markedRawEdgeDegreeIntegrand ν δ γ hZ x ((markedRawActiveSplit pads).symm (copied,last))
      y ⟨t,S⟩ K old b
  calc
    _ = ∑ S, ∑ old, ∑ b, W S old b := by
      apply Finset.sum_congr rfl
      intro S _
      exact markedRawEdge_degree_payload_charged_sum ν δ γ hZ x
        ((markedRawActiveSplit pads).symm (copied,last)) y ⟨t,S⟩ K
    _ = ∑ old, ∑ S, ∑ b, W S old b := Finset.sum_comm
    _ = _ := by
      simp only [markedRawEdgeSlotComponent, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro old _
      apply Finset.sum_congr rfl
      intro S _
      apply Finset.sum_congr rfl
      intro b _
      dsimp only [W]
      unfold markedRawEdgeDegreeIntegrand
      simp only [Equiv.apply_symm_apply]
      unfold markedRawAnchoredBatch
      ring

end
end ArtinMatthews

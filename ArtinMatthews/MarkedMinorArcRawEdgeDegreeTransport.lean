module

public import ArtinMatthews.MarkedMinorArcRawEdgeDegreeFibers
public import ArtinMatthews.MarkedMinorArcRawEdgeSymmetryCoefficients
public import ArtinMatthews.MarkedMinorArcRawGhostDegreeTransport


set_option backward.privateInPublic true
@[expose] public section

/-! Exact transport of every literal edge factor and of its physical
target. Source stores are appended only after old promotions are removed. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem markedRawEdgeSurvivorTupleCast_congr {X : Type*} {k n : ℕ}
    {S T : Finset (Fin k)} (hST : S=T) (hS : (Sᶜ).card=n) (hT : (Tᶜ).card=n)
    (old : Fin k → X) :
    markedRawSurvivorTupleCast S hS old=markedRawSurvivorTupleCast T hT old := by
  subst T
  rfl

theorem markedRawEdge_degree_target_position {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z) (active : MarkedRawActive P (pads+1))
    (target : Z) (a : MarkedRawEdgeDegreeShape J B)
    (data : MarkedRawEdgeDegreePayload P target.1 (hZ _ target.2) a) :
    (markedRawEdgeDegreeMemoryChoice hZ z active target a data).2.target=target := rfl

theorem markedRawEdge_degree_stored {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z) (active : MarkedRawActive P (pads+1))
    (target : Z) (a : MarkedRawEdgeDegreeShape J B)
    (data : MarkedRawEdgeDegreePayload P target.1 (hZ _ target.2) a) :
    (markedRawEdgeDegreeMemoryChoice hZ z active target a data).2.store=a.1.stored := rfl

theorem markedRawEdge_degree_promoted {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z) (active : MarkedRawActive P (pads+1))
    (target : Z) (a : MarkedRawEdgeDegreeShape J B)
    (data : MarkedRawEdgeDegreePayload P target.1 (hZ _ target.2) a) (j : J) :
    ((markedRawEdgeDegreeMemoryChoice hZ z active target a data).2.promotions j).isSome=
      a.1.promoted j := markedRawEdgeBatchOption_isSome (a.2 j)

theorem markedRawEdge_degree_deletion {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z) (active : MarkedRawActive P (pads+1))
    (target : Z) (a : MarkedRawEdgeDegreeShape J B)
    (data : MarkedRawEdgeDegreePayload P target.1 (hZ _ target.2) a) (j : J) :
    markedRawEdgePromotionDeletion
      (markedRawEdgeDegreeMemoryChoice hZ z active target a data).2.promotions j=(a.2 j).1 :=
  markedRawEdgeBatchOption_toFinset (a.2 j)

theorem markedRawEdge_degree_targetLast {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z) (active : MarkedRawActive P (pads+1))
    (target : Z) (a : MarkedRawEdgeDegreeShape J B)
    (data : MarkedRawEdgeDegreePayload P target.1 (hZ _ target.2) a) :
    let c := markedRawEdgeDegreeMemoryChoice hZ z active target a data
    markedRawEdgeTargetLast c.1 c.2.promotions c.2.fresh=data.2.1 := by
  let m : MarkedRawMemory P B := ⟨markedRawEdgeDegreesSourceSizes a.1,data.1.1⟩
  let prom : MarkedRawEdgePromotions m := fun j => markedRawEdgeBatchOption (a.2 j)
  change markedRawEdgeTargetLast m prom
    ((markedRawEdgeDegreeLabelsEquiv m prom).symm data.2)=data.2.1
  exact (markedRawEdgeDegreeLabelsEquiv_value m prom
    ((markedRawEdgeDegreeLabelsEquiv m prom).symm data.2)).symm.trans
      (congrArg Subtype.val ((markedRawEdgeDegreeLabelsEquiv m prom).apply_symm_apply data.2))

theorem markedRawEdge_degree_prime_mass {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z) (active : MarkedRawActive P (pads+1))
    (target : Z) (a : MarkedRawEdgeDegreeShape J B)
    (data : MarkedRawEdgeDegreePayload P target.1 (hZ _ target.2) a) :
    let c := markedRawEdgeDegreeMemoryChoice hZ z active target a data
    markedRawEdgeChoicePrimeMass ν V hZ (z,(active,c.1)) c.2=
      ∏ j, if a.1.promoted j then (V j)⁻¹ else ν j (data.2.1 j) := by
  dsimp only
  rw [markedRawEdgeChoicePrimeMass_eq_targetLast,
    markedRawEdge_degree_targetLast]
  apply Finset.prod_congr rfl
  intro j _
  rw [markedRawEdge_degree_promoted]

theorem markedRawEdge_degree_target_sizes {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z) (active : MarkedRawActive P (pads+1))
    (target : Z) (a : MarkedRawEdgeDegreeShape J B)
    (data : MarkedRawEdgeDegreePayload P target.1 (hZ _ target.2) a) (j : J) :
    let c := markedRawEdgeDegreeMemoryChoice hZ z active target a data
    ((markedRawEdgeTargetMemory hZ (z,(active,c.1)) c.2).1.1 j:ℕ)=
      a.1.survivors j+markedRawEdgeBit (a.1.stored j) := by
  change (Finset.univ \ (markedRawEdgeBatchOption (a.2 j)).toFinset).card+
    markedRawEdgeBit (a.1.stored j)=_
  rw [markedRawEdgeBatchOption_toFinset,← Finset.compl_eq_univ_sdiff,
    markedRawDeletionBatch_survivor_card rfl]

def markedRawEdgeDegreeTargetTuple {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z) (active : MarkedRawActive P (pads+1))
    (target : Z) (a : MarkedRawEdgeDegreeShape J B)
    (data : MarkedRawEdgeDegreePayload P target.1 (hZ _ target.2) a) :
    (j : J) → Fin (a.1.survivors j+markedRawEdgeBit (a.1.stored j)) → MarkedRawParticle (P j) :=
  fun j => Fin.addCases
    (markedRawSurvivorTupleCast (a.2 j).1 (markedRawDeletionBatch_survivor_card rfl (a.2 j))
      (data.1.1 j))
    (fun _ => markedRawAnchoredParticle (P j) (((markedRawActiveSplit pads) active).2 j)
      z.1 (hZ _ z.2))

theorem markedRawEdge_degree_target_tuple {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z) (active : MarkedRawActive P (pads+1))
    (target : Z) (a : MarkedRawEdgeDegreeShape J B)
    (data : MarkedRawEdgeDegreePayload P target.1 (hZ _ target.2) a)
    (j : J) (i : Fin (a.1.survivors j+markedRawEdgeBit (a.1.stored j))) :
    let c := markedRawEdgeDegreeMemoryChoice hZ z active target a data
    (markedRawEdgeTargetMemory hZ (z,(active,c.1)) c.2).2 j
      (Fin.cast (markedRawEdge_degree_target_sizes hZ z active target a data j).symm i)=
      markedRawEdgeDegreeTargetTuple hZ z active target a data j i := by
  let c := markedRawEdgeDegreeMemoryChoice hZ z active target a data
  have hn : ((markedRawEdgePromotionDeletion c.2.promotions j)ᶜ).card=a.1.survivors j := by
    rw [markedRawEdge_degree_deletion]
    exact markedRawDeletionBatch_survivor_card rfl (a.2 j)
  have hi := markedRawGhost_target_tuple_cast c.1 z.1 (hZ _ z.2)
    (markedRawEdgePromotionDeletion c.2.promotions) (markedRawEdgeStoreSizes hZ (z,(active,c.1)) c.2)
    (fun j _ => ((markedRawActiveSplit pads) active).2 j) j hn i
  have hs := markedRawEdgeSurvivorTupleCast_congr
    (markedRawEdge_degree_deletion hZ z active target a data j) hn
    (markedRawDeletionBatch_survivor_card rfl (a.2 j)) (c.1.2 j)
  dsimp only [c] at hi
  dsimp only [c] at hs
  rw [hs] at hi
  dsimp only [markedRawEdgeTargetMemory]
  exact hi

theorem markedRawEdge_degree_target_memory {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z) (active : MarkedRawActive P (pads+1))
    (target : Z) (a : MarkedRawEdgeDegreeShape J B)
    (data : MarkedRawEdgeDegreePayload P target.1 (hZ _ target.2) a) :
    let c := markedRawEdgeDegreeMemoryChoice hZ z active target a data
    markedRawEdgeTargetMemory hZ (z,(active,c.1)) c.2=
      markedRawMemoryOfDegrees P (fun j => a.1.survivors j+markedRawEdgeBit (a.1.stored j))
        a.1.target_le (markedRawEdgeDegreeTargetTuple hZ z active target a data) := by
  exact markedRawMemory_eq_of_degrees _ _ _ _
    (markedRawEdge_degree_target_sizes hZ z active target a data)
    (markedRawEdge_degree_target_tuple hZ z active target a data)

theorem markedRawEdge_degree_target {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z) (active : MarkedRawActive P (pads+1))
    (target : Z) (a : MarkedRawEdgeDegreeShape J B)
    (data : MarkedRawEdgeDegreePayload P target.1 (hZ _ target.2) a) :
    let c := markedRawEdgeDegreeMemoryChoice hZ z active target a data
    markedRawEdgeTargetState hZ (z,(active,c.1)) c.2=
      (target,((markedRawActiveSplit pads).symm
        (((markedRawActiveSplit pads) active).1,data.2.1),
          markedRawMemoryOfDegrees P (fun j => a.1.survivors j+markedRawEdgeBit (a.1.stored j))
            a.1.target_le (markedRawEdgeDegreeTargetTuple hZ z active target a data))) := by
  dsimp only [markedRawEdgeTargetState]
  rw [markedRawEdge_degree_target_memory,markedRawEdge_degree_targetLast]
  rfl

theorem markedRawEdge_degree_target_mass {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z) (active : MarkedRawActive P (pads+1))
    (target : Z) (a : MarkedRawEdgeDegreeShape J B)
    (data : MarkedRawEdgeDegreePayload P target.1 (hZ _ target.2) a) :
    let c := markedRawEdgeDegreeMemoryChoice hZ z active target a data
    markedRawMemoryMass ν (markedRawEdgeTargetMemory hZ (z,(active,c.1)) c.2)=
      ∏ j, (∏ i,ν j (markedRawEdgeDegreeTargetTuple hZ z active target a data j i).1)/
        (Nat.factorial (a.1.survivors j+markedRawEdgeBit (a.1.stored j)):ℝ) := by
  dsimp only
  rw [markedRawEdge_degree_target_memory]
  rfl

/-- The exact factorial source measure and every original prime factor
under the finite degree reindex. The observable may include the full
physical coefficient and the actual target-state test. -/
theorem markedRawEdge_weighted_choice_degree_sum {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z) (active : MarkedRawActive P (pads+1))
    (f : MarkedRawEdgeMemoryChoice (B := B) hZ z active → ℂ) :
    (∑ m : MarkedRawMemory P B, (markedRawMemoryMass ν m:ℂ)*
      ∑ c : MarkedRawEdgeChoice hZ (z,(active,m)),
        (markedRawEdgeChoicePrimeMass ν V hZ (z,(active,m)) c:ℂ)*f ⟨m,c⟩)=
      ∑ target : Z, ∑ a : MarkedRawEdgeDegreeShape J B,
        ∑ data : MarkedRawEdgeDegreePayload P target.1 (hZ _ target.2) a,
          ((∏ j, ∏ i,(ν j (data.1.1 j i).1:ℂ))/
            (∏ j,(Nat.factorial (a.1.survivors j+markedRawEdgeBit (a.1.promoted j)):ℂ)))*
          ((∏ j, if a.1.promoted j then (V j)⁻¹ else ν j (data.2.1 j):ℝ):ℂ)*
          f (markedRawEdgeDegreeMemoryChoice hZ z active target a data) := by
  classical
  refine (markedRawEdge_weighted_memory_degree_sum ν hZ z active
    (fun c => (markedRawEdgeChoicePrimeMass ν V hZ (z,(active,c.1)) c.2:ℂ)*f c)).trans ?_
  apply Finset.sum_congr rfl
  intro target _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro data _
  rw [markedRawEdge_degree_prime_mass]
  exact (mul_assoc _ _ _).symm

end
end ArtinMatthews

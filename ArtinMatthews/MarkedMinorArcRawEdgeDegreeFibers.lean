module

public import ArtinMatthews.MarkedMinorArcRawEdgeDegreeChoices
public import ArtinMatthews.MarkedMinorArcRawEdgeDegreeLabels
public import ArtinMatthews.MarkedMinorArcRawMemoryDegreeFamily


set_option backward.privateInPublic true
@[expose] public section

/-! Literal old-particle and target-label fibers over the edge degrees.
Eligibility is kept as the actual old-particle hit condition. Promoted
groups have a single constrained label and no redundant fresh choice. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

abbrev MarkedRawEdgeMemoryChoice {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z) (active : MarkedRawActive P (pads+1)) :=
  Σ m : MarkedRawMemory P B, MarkedRawEdgeChoice hZ (z,(active,m))

abbrev MarkedRawEdgeShapeOld {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (a : MarkedRawEdgeShape J B) :=
  {old : (j : J) → Fin (a.1.1 j:ℕ) → MarkedRawParticle (P j) //
    ∀ j k, a.2.1 j=some k → MarkedRawParticleHits (P j) z hz (old j k)}

abbrev MarkedRawEdgeShapeFreshPayload {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (a : MarkedRawEdgeShape J B) :=
  Σ old : MarkedRawEdgeShapeOld P z hz a,
    MarkedRawEdgeFreshLabels (m := (⟨a.1,old.1⟩ : MarkedRawMemory P B)) a.2.1

abbrev MarkedRawEdgeShapePayload {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (a : MarkedRawEdgeShape J B) :=
  Σ old : MarkedRawEdgeShapeOld P z hz a,
    {b : (j : J) → ↥(P j) // ∀ j k, a.2.1 j=some k → b j=(old.1 j k).1}

abbrev MarkedRawEdgeDegreePayload {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (a : MarkedRawEdgeDegreeShape J B) :=
  MarkedRawEdgeShapePayload P z hz (markedRawEdgeDegreeShapeToShape a)

def markedRawEdgeShapePayloadFreshEquiv {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (a : MarkedRawEdgeShape J B) :
    MarkedRawEdgeShapePayload P z hz a ≃ MarkedRawEdgeShapeFreshPayload P z hz a :=
  Equiv.sigmaCongrRight (fun old =>
    (markedRawEdgeDegreeLabelsEquiv (⟨a.1,old.1⟩ : MarkedRawMemory P B) a.2.1).symm)

def markedRawEdgeShapeFreshMemoryChoiceEquiv {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z) (active : MarkedRawActive P (pads+1)) :
    (Σ target : Z, Σ a : MarkedRawEdgeShape J B,
      MarkedRawEdgeShapeFreshPayload P target.1 (hZ _ target.2) a) ≃
      MarkedRawEdgeMemoryChoice (B := B) hZ z active where
  toFun a := ⟨⟨a.2.1.1,a.2.2.1.1⟩,
    { target := a.1
      store := a.2.1.2.2.1
      promotions := a.2.1.2.1
      fresh := a.2.2.2
      promotion_hits := a.2.2.1.2
      memory_bound := a.2.1.2.2.2 }⟩
  invFun c := ⟨c.2.target,⟨c.1.1,c.2.promotions,⟨c.2.store,c.2.memory_bound⟩⟩,
    ⟨c.1.2,c.2.promotion_hits⟩,c.2.fresh⟩
  left_inv := by
    rintro ⟨target,⟨k,p,⟨stored,hbound⟩⟩,⟨old,hits⟩,fresh⟩
    rfl
  right_inv := by
    rintro ⟨⟨k,old⟩,⟨target,stored,p,fresh,hits,hbound⟩⟩
    rfl

def markedRawEdgeShapeMemoryChoiceEquiv {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z) (active : MarkedRawActive P (pads+1)) :
    (Σ target : Z, Σ a : MarkedRawEdgeShape J B,
      MarkedRawEdgeShapePayload P target.1 (hZ _ target.2) a) ≃
      MarkedRawEdgeMemoryChoice (B := B) hZ z active :=
  (Equiv.sigmaCongrRight (fun target : Z => Equiv.sigmaCongrRight (fun a : MarkedRawEdgeShape J B =>
    markedRawEdgeShapePayloadFreshEquiv P target.1 (hZ _ target.2) a))).trans
      (markedRawEdgeShapeFreshMemoryChoiceEquiv hZ z active)

def markedRawEdgeDegreeMemoryChoiceEquiv {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z) (active : MarkedRawActive P (pads+1)) :
    (Σ target : Z, Σ a : MarkedRawEdgeDegreeShape J B,
      MarkedRawEdgeDegreePayload P target.1 (hZ _ target.2) a) ≃
      MarkedRawEdgeMemoryChoice (B := B) hZ z active :=
  (Equiv.sigmaCongrRight (fun _ => Equiv.sigmaCongr markedRawEdgeDegreeShapeEquiv
    (fun _ => Equiv.refl _))).trans (markedRawEdgeShapeMemoryChoiceEquiv hZ z active)

def markedRawEdgeDegreeMemoryChoice {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z) (active : MarkedRawActive P (pads+1))
    (target : Z) (a : MarkedRawEdgeDegreeShape J B)
    (data : MarkedRawEdgeDegreePayload P target.1 (hZ _ target.2) a) :
    MarkedRawEdgeMemoryChoice (B := B) hZ z active :=
  markedRawEdgeShapeMemoryChoiceEquiv hZ z active
    ⟨target,markedRawEdgeDegreeShapeToShape a,data⟩

theorem markedRawEdgeDegreeMemoryChoiceEquiv_apply {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z) (active : MarkedRawActive P (pads+1))
    (target : Z) (a : MarkedRawEdgeDegreeShape J B)
    (data : MarkedRawEdgeDegreePayload P target.1 (hZ _ target.2) a) :
    markedRawEdgeDegreeMemoryChoiceEquiv hZ z active ⟨target,a,data⟩=
      markedRawEdgeDegreeMemoryChoice hZ z active target a data := rfl

theorem markedRawEdge_memory_degree_sum {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z) (active : MarkedRawActive P (pads+1))
    {T : Type*} [AddCommMonoid T] (f : MarkedRawEdgeMemoryChoice (B := B) hZ z active → T) :
    (∑ m : MarkedRawMemory P B, ∑ c : MarkedRawEdgeChoice hZ (z,(active,m)), f ⟨m,c⟩)=
      ∑ target : Z, ∑ a : MarkedRawEdgeDegreeShape J B,
        ∑ data : MarkedRawEdgeDegreePayload P target.1 (hZ _ target.2) a,
          f (markedRawEdgeDegreeMemoryChoice hZ z active target a data) := by
  classical
  simpa only [Fintype.sum_sigma,markedRawEdgeDegreeMemoryChoiceEquiv_apply] using
    (Equiv.sum_comp (markedRawEdgeDegreeMemoryChoiceEquiv hZ z active) f).symm

theorem markedRawEdge_degree_source {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z) (active : MarkedRawActive P (pads+1))
    (target : Z) (a : MarkedRawEdgeDegreeShape J B)
    (data : MarkedRawEdgeDegreePayload P target.1 (hZ _ target.2) a) :
    (markedRawEdgeDegreeMemoryChoice hZ z active target a data).1=
      markedRawMemoryOfDegrees P (fun j => a.1.survivors j+markedRawEdgeBit (a.1.promoted j))
        a.1.source_le data.1.1 := rfl

theorem markedRawEdge_degree_source_mass {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z) (active : MarkedRawActive P (pads+1))
    (target : Z) (a : MarkedRawEdgeDegreeShape J B)
    (data : MarkedRawEdgeDegreePayload P target.1 (hZ _ target.2) a) :
    markedRawMemoryMass ν (markedRawEdgeDegreeMemoryChoice hZ z active target a data).1=
      ∏ j, (∏ i,ν j (data.1.1 j i).1)/
        (Nat.factorial (a.1.survivors j+markedRawEdgeBit (a.1.promoted j)):ℝ) := rfl

theorem markedRawEdge_degree_source_mass_complex {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z) (active : MarkedRawActive P (pads+1))
    (target : Z) (a : MarkedRawEdgeDegreeShape J B)
    (data : MarkedRawEdgeDegreePayload P target.1 (hZ _ target.2) a) :
    (markedRawMemoryMass ν (markedRawEdgeDegreeMemoryChoice hZ z active target a data).1:ℂ)=
      (∏ j, ∏ i,(ν j (data.1.1 j i).1:ℂ))/
        (∏ j,(Nat.factorial (a.1.survivors j+markedRawEdgeBit (a.1.promoted j)):ℂ)) := by
  rw [markedRawEdge_degree_source]
  exact markedRawMemoryOfDegrees_mass_complex _ _ _ _ _

/-- Literal weighted source-memory integration, with every factorial
visible and with an arbitrary coupled observable of the whole choice. -/
theorem markedRawEdge_weighted_memory_degree_sum {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z) (active : MarkedRawActive P (pads+1))
    (f : MarkedRawEdgeMemoryChoice (B := B) hZ z active → ℂ) :
    (∑ m : MarkedRawMemory P B, (markedRawMemoryMass ν m:ℂ)*
      ∑ c : MarkedRawEdgeChoice hZ (z,(active,m)), f ⟨m,c⟩)=
      ∑ target : Z, ∑ a : MarkedRawEdgeDegreeShape J B,
        ∑ data : MarkedRawEdgeDegreePayload P target.1 (hZ _ target.2) a,
          ((∏ j, ∏ i,(ν j (data.1.1 j i).1:ℂ))/
            (∏ j,(Nat.factorial (a.1.survivors j+markedRawEdgeBit (a.1.promoted j)):ℂ)))*
              f (markedRawEdgeDegreeMemoryChoice hZ z active target a data) := by
  classical
  simp_rw [Finset.mul_sum]
  rw [markedRawEdge_memory_degree_sum hZ z active (fun c => (markedRawMemoryMass ν c.1:ℂ)*f c)]
  simp only [markedRawEdge_degree_source_mass_complex]

end
end ArtinMatthews

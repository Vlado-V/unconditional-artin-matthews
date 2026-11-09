module

public import ArtinMatthews.MarkedPhysicalMarking
public import ArtinMatthews.MarkedMinorArcBanRawCollision


set_option backward.privateInPublic true
@[expose] public section

/-! Exact ordered union-label coordinates for one physical edge. A shared
prefix and its two final labels are counted once, without a permutation or
factorial quotient. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedPhysicalMarkingSplit {J : Type*} {P : J → Finset ℕ} (M : ℕ) :
    MarkedPhysicalMarking P (M+1) ≃
      (MarkedPhysicalMarking P M × ((j : J) → ↥(P j))) where
  toFun a := (fun j k => a j k.castSucc, fun j => a j (Fin.last M))
  invFun a j := Fin.snoc (a.1 j) (a.2 j)
  left_inv a := by funext j; exact Fin.snoc_init_self (a j)
  right_inv a := by ext j k <;> simp

def markedPhysicalEdgeSource {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (u : MarkedPhysicalMarking P (M+2)) : MarkedPhysicalMarking P (M+1) :=
  (markedPhysicalMarkingSplit (M+1) u).1

def markedPhysicalEdgeTarget {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (u : MarkedPhysicalMarking P (M+2)) : MarkedPhysicalMarking P (M+1) :=
  (markedPhysicalMarkingSplit M).symm
    ((markedPhysicalMarkingSplit M (markedPhysicalEdgeSource u)).1,
      (markedPhysicalMarkingSplit (M+1) u).2)

def markedPhysicalEdgeUnion {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (a b : MarkedPhysicalMarking P (M+1)) : MarkedPhysicalMarking P (M+2) :=
  (markedPhysicalMarkingSplit (M+1)).symm (a,(markedPhysicalMarkingSplit M b).2)

@[simp] theorem markedPhysicalEdgeSource_union {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (a b : MarkedPhysicalMarking P (M+1)) :
    markedPhysicalEdgeSource (markedPhysicalEdgeUnion a b) = a := by
  simp [markedPhysicalEdgeSource, markedPhysicalEdgeUnion]

theorem markedPhysicalEdgeTarget_union {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (a b : MarkedPhysicalMarking P (M+1))
    (hab : (markedPhysicalMarkingSplit M a).1 = (markedPhysicalMarkingSplit M b).1) :
    markedPhysicalEdgeTarget (markedPhysicalEdgeUnion a b) = b := by
  unfold markedPhysicalEdgeTarget
  rw [markedPhysicalEdgeSource_union]
  simp only [markedPhysicalEdgeUnion, Equiv.apply_symm_apply]
  rw [hab]
  exact (markedPhysicalMarkingSplit M).symm_apply_apply b

@[simp] theorem markedPhysicalEdgeUnion_source_target {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (u : MarkedPhysicalMarking P (M+2)) :
    markedPhysicalEdgeUnion (markedPhysicalEdgeSource u) (markedPhysicalEdgeTarget u) = u := by
  unfold markedPhysicalEdgeUnion markedPhysicalEdgeTarget
  rw [Equiv.apply_symm_apply]
  exact (markedPhysicalMarkingSplit (M+1)).symm_apply_apply u

theorem markedPhysicalEdge_shared {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (u : MarkedPhysicalMarking P (M+2)) :
    (markedPhysicalMarkingSplit M (markedPhysicalEdgeSource u)).1 =
      (markedPhysicalMarkingSplit M (markedPhysicalEdgeTarget u)).1 := by
  simp [markedPhysicalEdgeTarget]

def markedPhysicalEdgeLabelsEquiv {J : Type*} {P : J → Finset ℕ} (M : ℕ) :
    MarkedPhysicalMarking P (M+2) ≃
      {ab : MarkedPhysicalMarking P (M+1) × MarkedPhysicalMarking P (M+1) //
        (markedPhysicalMarkingSplit M ab.1).1 = (markedPhysicalMarkingSplit M ab.2).1} where
  toFun u := ⟨(markedPhysicalEdgeSource u,markedPhysicalEdgeTarget u),markedPhysicalEdge_shared u⟩
  invFun ab := markedPhysicalEdgeUnion ab.1.1 ab.1.2
  left_inv := markedPhysicalEdgeUnion_source_target
  right_inv ab := by
    apply Subtype.ext
    exact Prod.ext (markedPhysicalEdgeSource_union _ _) (markedPhysicalEdgeTarget_union _ _ ab.2)

theorem markedPhysicalMarkingSplit_raw {J : Type*} (P : J → Finset ℕ)
    (hP : ∀ j p,p ∈ P j → p.Prime) (M : ℕ)
    (a : MarkedRawActive (fun j => markedRawPrimeBand (P j)) (M+1)) :
    (markedPhysicalMarkingSplit M (markedPhysicalMarkingEquiv P hP (M+1) a)).1 =
      markedPhysicalMarkingEquiv P hP M ((markedRawActiveSplit M a).1) := rfl

def MarkedPhysicalCrossBan {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (a : MarkedPhysicalMarking P M) (b : (j : J) → ↥(P j)) : Prop :=
  ∃ i j k,(b i : ℕ) = (a j k : ℕ)

theorem markedPhysicalCrossBan_raw {J : Type*} (P : J → Finset ℕ)
    (hP : ∀ j p,p ∈ P j → p.Prime) {M : ℕ}
    (a : MarkedRawActive (fun j => markedRawPrimeBand (P j)) M)
    (b : (j : J) → ↥(markedRawPrimeBand (P j))) :
    MarkedRawFullCrossBan a b ↔ MarkedPhysicalCrossBan
      (markedPhysicalMarkingEquiv P hP M a)
      (fun j => markedRawPrimeBandEquiv (P j) (hP j) (b j)) := by
  constructor
  · rintro ⟨i,j,k,h⟩
    exact ⟨i,j,k,congrArg (fun p : Nat.Primes => (p : ℕ)) h⟩
  · rintro ⟨i,j,k,h⟩
    exact ⟨i,j,k,Subtype.ext h⟩

theorem markedPhysicalEdgeUnion_distinct {J : Type*} {P : J → Finset ℕ}
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) {M : ℕ}
    (a b : MarkedPhysicalMarking P (M+1)) :
    MarkedPhysicalMarkingDistinct (markedPhysicalEdgeUnion a b) ↔
      MarkedPhysicalMarkingDistinct a ∧
        ¬MarkedPhysicalCrossBan a (markedPhysicalMarkingSplit M b).2 := by
  change (∀ j,Function.Injective (Fin.snoc (a j) ((markedPhysicalMarkingSplit M b).2 j))) ↔ _
  simp only [Fin.snoc_injective_iff]
  constructor
  · intro h
    refine ⟨fun j => (h j).1,?_⟩
    rintro ⟨i,j,k,he⟩
    have hij : i=j := by
      by_contra hn
      exact Finset.disjoint_left.mp (hdis hn) ((markedPhysicalMarkingSplit M b).2 i).2
        (by simpa only [he] using (a j k).2)
    subst j
    exact (h i).2 ⟨k,Subtype.ext he.symm⟩
  · rintro ⟨ha,hban⟩ j
    refine ⟨ha j,?_⟩
    rintro ⟨k,hk⟩
    exact hban ⟨j,j,k,congrArg Subtype.val hk.symm⟩

end ArtinMatthews

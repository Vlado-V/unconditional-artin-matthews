module

public import ArtinMatthews.MarkedPhysicalEdgeLabelSplit
public import ArtinMatthews.MarkedPhysicalEndpointState


set_option backward.privateInPublic true
@[expose] public section

/-! Literal pad-collision flags for one shared-prefix physical edge.
The equality of the two unshared labels is retained separately; it is
not an event whose probability is small under the auxiliary pad law.
Primitive-position and endpoint-divisibility tests remain explicit. -/

namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

theorem markedPadCollision_pair_iff {Ω : Type*} [DecidableEq Ω] {M : ℕ}
    (c : Fin M → Ω) (b a : Ω) :
    ¬MarkedPadCollision {b,a} c ↔
      Function.Injective c ∧ b ∉ Set.range c ∧ a ∉ Set.range c := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij
      by_contra hne
      exact h (Or.inl ⟨i,j,hne,hij⟩)
    · rintro ⟨k,hk⟩
      exact h (Or.inr ⟨k, by simp only [hk, Finset.mem_insert, Finset.mem_singleton, true_or]⟩)
    · rintro ⟨k,hk⟩
      exact h (Or.inr ⟨k, by simp only [hk, Finset.mem_insert, Finset.mem_singleton, or_true]⟩)
  · rintro ⟨hinj,hb,ha⟩ (hrep | hforb)
    · obtain ⟨i,j,hne,hij⟩ := hrep
      exact hne (hinj hij)
    · obtain ⟨k,hk⟩ := hforb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      exact hk.elim (fun h => hb ⟨k,h⟩) (fun h => ha ⟨k,h⟩)

theorem markedPadDoubleSnoc_injective_iff {Ω : Type*} [DecidableEq Ω] {M : ℕ}
    (c : Fin M → Ω) (b a : Ω) :
    Function.Injective (Fin.snoc (Fin.snoc c b) a) ↔
      ¬MarkedPadCollision {b,a} c ∧ b ≠ a := by
  constructor
  · intro h
    obtain ⟨hcb,ha⟩ := Fin.snoc_injective_iff.mp h
    obtain ⟨hinj,hb⟩ := Fin.snoc_injective_iff.mp hcb
    have hac : a ∉ Set.range c := by
      rintro ⟨k,hk⟩
      exact ha ⟨k.castSucc, by simpa only [Fin.snoc_castSucc] using hk⟩
    have hba : b ≠ a := by
      intro hba
      exact ha ⟨Fin.last M, by simpa only [Fin.snoc_last] using hba⟩
    exact ⟨(markedPadCollision_pair_iff c b a).mpr ⟨hinj,hb,hac⟩,hba⟩
  · rintro ⟨hgood,hba⟩
    obtain ⟨hinj,hb,ha⟩ := (markedPadCollision_pair_iff c b a).mp hgood
    apply Fin.snoc_injective_iff.mpr
    refine ⟨Fin.snoc_injective_iff.mpr ⟨hinj,hb⟩, ?_⟩
    rw [Fin.range_snoc]
    intro h
    exact (Set.mem_insert_iff.mp h).elim (fun hab => hba hab.symm) ha

def markedPhysicalPadUnion {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (c : MarkedPhysicalMarking P M) (b a : (j : J) → ↥(P j)) :
    MarkedPhysicalMarking P (M+2) :=
  fun j => Fin.snoc (Fin.snoc (c j) (b j)) (a j)

theorem markedPhysicalPadUnion_eq_edgeUnion {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (c : MarkedPhysicalMarking P M) (b a : (j : J) → ↥(P j)) :
    markedPhysicalPadUnion c b a =
      markedPhysicalEdgeUnion ((markedPhysicalMarkingSplit M).symm (c,b))
        ((markedPhysicalMarkingSplit M).symm (c,a)) := by
  unfold markedPhysicalEdgeUnion
  rw [(markedPhysicalMarkingSplit M).apply_symm_apply (c,a)]
  rfl

theorem markedPhysicalPadUnion_distinct_iff {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (c : MarkedPhysicalMarking P M) (b a : (j : J) → ↥(P j)) :
    MarkedPhysicalMarkingDistinct (markedPhysicalPadUnion c b a) ↔
      (∀ j, ¬MarkedPadCollision {b j,a j} (c j)) ∧ ∀ j, b j ≠ a j := by
  simp only [MarkedPhysicalMarkingDistinct, markedPhysicalPadUnion,
    markedPadDoubleSnoc_injective_iff, forall_and]

theorem markedPhysicalPad_target_distinct {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (c : MarkedPhysicalMarking P M) (b a : (j : J) → ↥(P j))
    (hgood : ∀ j, ¬MarkedPadCollision {b j,a j} (c j)) :
    MarkedPhysicalMarkingDistinct ((markedPhysicalMarkingSplit M).symm (c,a)) := by
  intro j
  obtain ⟨hinj,_,ha⟩ := (markedPadCollision_pair_iff (c j) (b j) (a j)).mp (hgood j)
  exact Fin.snoc_injective_iff.mpr ⟨hinj,ha⟩

theorem markedPhysicalPad_source_crossBan_iff {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (c : MarkedPhysicalMarking P M) (b a : (j : J) → ↥(P j)) :
    (MarkedPhysicalMarkingDistinct ((markedPhysicalMarkingSplit M).symm (c,b)) ∧
      ¬MarkedPhysicalCrossBan ((markedPhysicalMarkingSplit M).symm (c,b)) a) ↔
      (∀ j, ¬MarkedPadCollision {b j,a j} (c j)) ∧ ∀ j, b j ≠ a j := by
  have he := markedPhysicalEdgeUnion_distinct hdis
    ((markedPhysicalMarkingSplit M).symm (c,b)) ((markedPhysicalMarkingSplit M).symm (c,a))
  have hu : MarkedPhysicalMarkingDistinct (markedPhysicalPadUnion c b a) ↔
      MarkedPhysicalMarkingDistinct ((markedPhysicalMarkingSplit M).symm (c,b)) ∧
        ¬MarkedPhysicalCrossBan ((markedPhysicalMarkingSplit M).symm (c,b)) a := by
    simpa only [markedPhysicalPadUnion_eq_edgeUnion, Equiv.apply_symm_apply] using he
  exact hu.symm.trans (markedPhysicalPadUnion_distinct_iff c b a)

theorem markedPhysicalPad_state_flags_iff {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (c : MarkedPhysicalMarking P M) (b a : (j : J) → ↥(P j)) (z w : ℤ × ℤ) :
    (MarkedPhysicalStateCondition z ((markedPhysicalMarkingSplit M).symm (c,b)) ∧
      MarkedPhysicalStateCondition w ((markedPhysicalMarkingSplit M).symm (c,a)) ∧
      ¬MarkedPhysicalCrossBan ((markedPhysicalMarkingSplit M).symm (c,b)) a) ↔
      IsCoprime z.1 z.2 ∧ IsCoprime w.1 w.2 ∧
        (∀ j k, ((((markedPhysicalMarkingSplit M).symm (c,b)) j k:ℕ):ℤ) ∣ z.1) ∧
        (∀ j k, ((((markedPhysicalMarkingSplit M).symm (c,a)) j k:ℕ):ℤ) ∣ w.1) ∧
        (∀ j, ¬MarkedPadCollision {b j,a j} (c j)) ∧ ∀ j, b j ≠ a j := by
  constructor
  · rintro ⟨⟨hz,hs,hzd⟩,⟨hw,_,hwd⟩,hban⟩
    obtain ⟨hgood,hba⟩ := (markedPhysicalPad_source_crossBan_iff hdis c b a).mp ⟨hs,hban⟩
    exact ⟨hz,hw,hzd,hwd,hgood,hba⟩
  · rintro ⟨hz,hw,hzd,hwd,hgood,hba⟩
    obtain ⟨hs,hban⟩ := (markedPhysicalPad_source_crossBan_iff hdis c b a).mpr ⟨hgood,hba⟩
    exact ⟨⟨hz,hs,hzd⟩,⟨hw,markedPhysicalPad_target_distinct c b a hgood,hwd⟩,hban⟩

end
end ArtinMatthews

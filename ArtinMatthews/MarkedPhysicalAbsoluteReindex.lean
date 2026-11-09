module

public import ArtinMatthews.MarkedPhysicalPairingIncidence
public import ArtinMatthews.MarkedPhysicalGoodPairingReverse


set_option backward.privateInPublic true
@[expose] public section

/-! Exact canonical reindexing of the absolute physical pairing. Norms
stay inside every finite sum throughout the change of variables. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalStateExtend_norm_sum {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {M : ℕ} {Z : Finset (ℤ × ℤ)}
    (F : MarkedPhysicalState P M Z → ℂ) :
    (∑ s : Z × MarkedPhysicalMarking P M,‖markedPhysicalStateExtend F s‖) = ∑ s,‖F s‖ := by
  exact Finset.sum_congr_set {s : Z × MarkedPhysicalMarking P M | MarkedPhysicalStateCondition s.1.1 s.2}
    (fun s => ‖markedPhysicalStateExtend F s‖) (fun s => ‖F s‖)
    (fun s hs => by
      change MarkedPhysicalStateCondition s.1.1 s.2 at hs
      simp only [markedPhysicalStateExtend,dite_eq_left hs])
    (fun s hs => by
      change ¬MarkedPhysicalStateCondition s.1.1 s.2 at hs
      simp only [markedPhysicalStateExtend,dite_eq_right hs,norm_zero])

theorem markedPhysical_shared_label_sum_real {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ)
    (F : MarkedPhysicalMarking P (M+1) → MarkedPhysicalMarking P (M+1) → ℝ) :
    (∑ a,∑ b,if (markedPhysicalMarkingSplit M a).1=(markedPhysicalMarkingSplit M b).1
      then F a b else 0) =
      ∑ u : MarkedPhysicalMarking P (M+2),F (markedPhysicalEdgeSource u) (markedPhysicalEdgeTarget u) := by
  let p := fun ab : MarkedPhysicalMarking P (M+1) × MarkedPhysicalMarking P (M+1) =>
    (markedPhysicalMarkingSplit M ab.1).1=(markedPhysicalMarkingSplit M ab.2).1
  have hs := Finset.sum_subtype (p := p) (F := inferInstance) (Finset.univ.filter p) (by simp)
    (fun ab => F ab.1 ab.2)
  have he := Equiv.sum_comp (markedPhysicalEdgeLabelsEquiv (P := P) M)
    (fun ab => F ab.1.1 ab.1.2)
  have hsum : (∑ a,∑ b,if (markedPhysicalMarkingSplit M a).1=(markedPhysicalMarkingSplit M b).1
      then F a b else 0) =
      ∑ ab : {ab : MarkedPhysicalMarking P (M+1) × MarkedPhysicalMarking P (M+1) // p ab},F ab.1.1 ab.1.2 := by
    simpa only [p,Finset.sum_filter,Fintype.sum_prod_type] using hs
  exact hsum.trans he.symm

theorem markedPhysicalEdgeAbsolutePairing_ambient {J : Type*} [Fintype J] [decJ : DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (f g : MarkedPhysicalState P (pads+1) Z → ℂ) :
    markedPhysicalEdgeAbsolutePairing P hP V pads Z hZ ψ η d₀ Y Q q f g =
      ∑ s,∑ t,‖markedPhysicalEdgePairTerm P hP V pads Z hZ ψ η d₀ Y Q q f g s t‖ := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  have hs : (∑ s : Z × MarkedPhysicalMarking P (pads+1),
      ∑ t : Z × MarkedPhysicalMarking P (pads+1),
        ‖markedPhysicalEdgePairTerm P hP V pads Z hZ ψ η d₀ Y Q q f g s t‖) =
      ∑ s : MarkedPhysicalState P (pads+1) Z,∑ t : MarkedPhysicalState P (pads+1) Z,
        ‖markedPhysicalEdgeCoefficient P hP V pads Z hZ ψ η d₀ Y Q q s t * star (f s) * g t‖ := Finset.sum_congr_set
    {s : Z × MarkedPhysicalMarking P (pads+1) | MarkedPhysicalStateCondition s.1.1 s.2}
    (fun s => ∑ t,‖markedPhysicalEdgePairTerm P hP V pads Z hZ ψ η d₀ Y Q q f g s t‖)
    (fun s : MarkedPhysicalState P (pads+1) Z => ∑ t : MarkedPhysicalState P (pads+1) Z,
      ‖markedPhysicalEdgeCoefficient P hP V pads Z hZ ψ η d₀ Y Q q s t * star (f s) * g t‖)
    (fun s hs => by
      change MarkedPhysicalStateCondition s.1.1 s.2 at hs
      unfold markedPhysicalEdgePairTerm
      simp only [markedPhysicalStateExtend,dite_eq_left hs]
      simpa only [markedPhysicalStateExtend] using
        markedPhysicalStateExtend_norm_sum (fun t =>
          markedPhysicalEdgeCoefficient P hP V pads Z hZ ψ η d₀ Y Q q ⟨s,hs⟩ t * star (f ⟨s,hs⟩) * g t))
    (fun s hs => by
      change ¬MarkedPhysicalStateCondition s.1.1 s.2 at hs
      simp only [markedPhysicalEdgePairTerm,markedPhysicalStateExtend,dite_eq_right hs,
        norm_zero,Finset.sum_const_zero])
  simpa only [markedPhysicalEdgeAbsolutePairing,norm_mul,norm_star] using hs.symm

theorem markedPhysicalEdgeAbsolutePairing_positions {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (f g : MarkedPhysicalState P (pads+1) Z → ℂ) :
    markedPhysicalEdgeAbsolutePairing P hP V pads Z hZ ψ η d₀ Y Q q f g =
      ∑ u : MarkedPhysicalMarking P (pads+2),∑ z ∈ Z,∑ w ∈ Z,
        ‖markedPhysicalEdgePositionTerm P hP V pads Z hZ ψ η d₀ Y Q q f g
          (markedPhysicalEdgeSource u) (markedPhysicalEdgeTarget u) z w‖ := by
  let F := markedPhysicalEdgePairTerm P hP V pads Z hZ ψ η d₀ Y Q q f g
  have hzw (z : Z) (a : MarkedPhysicalMarking P (pads+1)) :
      (∑ w : Z,∑ b : MarkedPhysicalMarking P (pads+1),‖F (z,a) (w,b)‖) =
        ∑ b : MarkedPhysicalMarking P (pads+1),∑ w : Z,‖F (z,a) (w,b)‖ := Finset.sum_comm
  rw [markedPhysicalEdgeAbsolutePairing_ambient]
  simp only [Fintype.sum_prod_type]
  change (∑ z : Z,∑ a,∑ w : Z,∑ b,‖F (z,a) (w,b)‖) = _
  simp_rw [hzw]
  rw [Finset.sum_comm]
  have hz (a : MarkedPhysicalMarking P (pads+1)) :
      (∑ z : Z,∑ b : MarkedPhysicalMarking P (pads+1),∑ w : Z,‖F (z,a) (w,b)‖) =
        ∑ b : MarkedPhysicalMarking P (pads+1),∑ z : Z,∑ w : Z,‖F (z,a) (w,b)‖ := Finset.sum_comm
  simp_rw [hz]
  have hp : (∑ a : MarkedPhysicalMarking P (pads+1),∑ b,∑ z : Z,∑ w : Z,‖F (z,a) (w,b)‖) =
      ∑ a : MarkedPhysicalMarking P (pads+1),∑ b,
        if (markedPhysicalMarkingSplit pads a).1=(markedPhysicalMarkingSplit pads b).1 then
          ∑ z : Z,∑ w : Z,‖F (z,a) (w,b)‖ else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases hab : (markedPhysicalMarkingSplit pads a).1=(markedPhysicalMarkingSplit pads b).1
    · rw [ite_eq_left hab]
    · rw [ite_eq_right hab]
      apply Finset.sum_eq_zero
      intro z _
      apply Finset.sum_eq_zero
      intro w _
      rw [show F (z,a) (w,b)=0 from markedPhysicalEdgePairTerm_off_prefix P hP V pads Z hZ
        ψ η d₀ Y Q q f g a b hab z w,norm_zero]
  rw [hp,markedPhysical_shared_label_sum_real]
  apply Finset.sum_congr rfl
  intro u _
  let H := fun z w => ‖markedPhysicalEdgePositionTerm P hP V pads Z hZ ψ η d₀ Y Q q f g
    (markedPhysicalEdgeSource u) (markedPhysicalEdgeTarget u) z w‖
  have he : (∑ z : Z,∑ w : Z,H z.1 w.1) = ∑ z ∈ Z,∑ w ∈ Z,H z w := by
    calc
      _ = ∑ z : Z,∑ w ∈ Z,H z.1 w := by
        apply Finset.sum_congr rfl
        intro z _
        exact Finset.sum_coe_sort Z (H z.1)
      _ = _ := Finset.sum_coe_sort Z (fun z => ∑ w ∈ Z,H z w)
  rw [← he]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro w _
  simp only [H,F,markedPhysicalEdgePositionTerm,dite_eq_left z.2,dite_eq_left w.2]

def markedPhysicalCanonicalAbsolutePairingSum
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (f g : MarkedPhysicalState P (pads+1) Z → ℂ)
    {A B C D : ℝ} (hA : 1 < A) (hC : 1 < C) : ℝ :=
  ∑ u : MarkedPhysicalMarking P (pads+2),
    if hu : MarkedPhysicalMarkingDistinct u then
      letI : NeZero (markedPhysicalMarkingProduct u) := ⟨(markedPhysicalMarkingProduct_pos hP u).ne'⟩
      let hS := markedPhysicalMarkingProduct_squarefree hP hdis u hu
      ∑ r : MarkedPhysicalCanonicalRoot (markedPhysicalMarkingProduct u) A B C D,
        ∑ z ∈ markedPhysicalCanonicalTargets hA hC r Z,
          ‖if markedPhysicalEdgeRootLineEvent u hS r.1 z then
            markedPhysicalEdgePositionTerm P hP V pads Z hZ ψ η d₀ Y Q q f g
              (markedPhysicalEdgeSource u) (markedPhysicalEdgeTarget u)
              (markedPhysicalCanonicalRootPosition r) ((markedPhysicalCanonicalTargetEquiv hA hC r).symm z)
          else 0‖
    else 0

theorem markedPhysicalEdgeAbsolutePairing_eq_canonical_sum
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (f g : MarkedPhysicalState P (pads+1) Z → ℂ)
    {A B C D : ℝ} (hA : 1 < A) (hC : 1 < C)
    (hbox : Z ⊆ markedPhysicalPrimitiveBox A B C D) :
    markedPhysicalEdgeAbsolutePairing P hP V pads Z hZ ψ η d₀ Y Q q f g =
      markedPhysicalCanonicalAbsolutePairingSum P hP hdis V pads Z hZ ψ η d₀ Y Q q f g
        (B := B) (D := D) hA hC := by
  let : ∀ u : MarkedPhysicalMarking P (pads+2),NeZero (markedPhysicalMarkingProduct u) :=
    fun u => ⟨(markedPhysicalMarkingProduct_pos hP u).ne'⟩
  rw [markedPhysicalEdgeAbsolutePairing_positions]
  unfold markedPhysicalCanonicalAbsolutePairingSum
  apply Finset.sum_congr rfl
  intro u _
  let H := fun z w => ‖markedPhysicalEdgePositionTerm P hP V pads Z hZ ψ η d₀ Y Q q f g
    (markedPhysicalEdgeSource u) (markedPhysicalEdgeTarget u) z w‖
  have hext : (∑ z ∈ Z,∑ w ∈ Z,H z w) =
      ∑ z ∈ markedPhysicalPrimitiveBox A B C D,∑ w ∈ Z,H z w := by
    apply Finset.sum_subset hbox
    intro z _ hz
    apply Finset.sum_eq_zero
    intro w _
    simp only [H,markedPhysicalEdgePositionTerm,dite_eq_right hz,norm_zero]
  rw [hext]
  have he := Equiv.sum_comp
    (markedPhysicalCanonicalRootEquiv (S := markedPhysicalMarkingProduct u) (B := B) (D := D) hA hC)
    (fun z => ∑ w ∈ Z,H z.1 w)
  have hroot : (∑ z ∈ markedPhysicalPrimitiveBox A B C D,∑ w ∈ Z,H z w) =
      ∑ r : MarkedPhysicalCanonicalRoot (markedPhysicalMarkingProduct u) A B C D,
        ∑ w ∈ Z,H (markedPhysicalCanonicalRootPosition r) w := by
    calc
      _ = ∑ z : ↥(markedPhysicalPrimitiveBox A B C D),∑ w ∈ Z,H z.1 w :=
        (Finset.sum_coe_sort _ (fun z => ∑ w ∈ Z,H z w)).symm
      _ = _ := he.symm
  rw [hroot]
  by_cases hu : MarkedPhysicalMarkingDistinct u
  · rw [dite_eq_left hu]
    apply Finset.sum_congr rfl
    intro r _
    have ht : (∑ w ∈ Z,H (markedPhysicalCanonicalRootPosition r) w) =
        ∑ z ∈ markedPhysicalCanonicalTargets hA hC r Z,
          H (markedPhysicalCanonicalRootPosition r) ((markedPhysicalCanonicalTargetEquiv hA hC r).symm z) := by
      unfold markedPhysicalCanonicalTargets
      rw [Finset.sum_image]
      · simp only [Equiv.symm_apply_apply]
      · exact fun _ _ _ _ h => (markedPhysicalCanonicalTargetEquiv hA hC r).injective h
    rw [ht]
    apply Finset.sum_congr rfl
    intro z _
    exact (congrArg norm (markedPhysicalEdgePositionTerm_incidence P hP V pads Z hZ ψ η d₀ Y Q q f g u
      (markedPhysicalMarkingProduct_squarefree hP hdis u hu) hA hC r z)).symm
  · rw [dite_eq_right hu]
    apply Finset.sum_eq_zero
    intro r _
    apply Finset.sum_eq_zero
    intro w _
    dsimp only [H]
    rw [show markedPhysicalEdgePositionTerm P hP V pads Z hZ ψ η d₀ Y Q q f g
        (markedPhysicalEdgeSource u) (markedPhysicalEdgeTarget u) (markedPhysicalCanonicalRootPosition r) w=0 from
      markedPhysicalEdgePositionTerm_off_distinct P hP hdis V pads Z hZ ψ η d₀ Y Q q f g u hu _ _]
    exact norm_zero

end ArtinMatthews

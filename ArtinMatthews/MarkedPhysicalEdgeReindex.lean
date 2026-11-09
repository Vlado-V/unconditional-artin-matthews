module

public import ArtinMatthews.MarkedPhysicalEdgeLabelSplit
public import ArtinMatthews.MarkedPhysicalEdgeKernelFormula


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite reindexing of the original damped physical pairing by one
ordered union list and two physical positions. No estimate is an input. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysical_shared_label_sum {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ)
    (F : MarkedPhysicalMarking P (M+1) → MarkedPhysicalMarking P (M+1) → ℂ) :
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

def markedPhysicalStateExtend {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    {Z : Finset (ℤ × ℤ)} (F : MarkedPhysicalState P M Z → ℂ)
    (s : Z × MarkedPhysicalMarking P M) : ℂ :=
  if h : MarkedPhysicalStateCondition s.1.1 s.2 then F ⟨s,h⟩ else 0

theorem markedPhysicalStateExtend_sum {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {M : ℕ} {Z : Finset (ℤ × ℤ)}
    (F : MarkedPhysicalState P M Z → ℂ) :
    (∑ s : Z × MarkedPhysicalMarking P M,markedPhysicalStateExtend F s) = ∑ s,F s := by
  exact Finset.sum_congr_set {s : Z × MarkedPhysicalMarking P M | MarkedPhysicalStateCondition s.1.1 s.2}
    (markedPhysicalStateExtend F) F
    (fun s hs => by
      change MarkedPhysicalStateCondition s.1.1 s.2 at hs
      simp only [markedPhysicalStateExtend,dite_eq_left hs])
    (fun s hs => by
      change ¬MarkedPhysicalStateCondition s.1.1 s.2 at hs
      simp only [markedPhysicalStateExtend,dite_eq_right hs])

def markedPhysicalEdgePairTerm {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (f g : MarkedPhysicalState P (pads+1) Z → ℂ)
    (s t : Z × MarkedPhysicalMarking P (pads+1)) : ℂ :=
  markedPhysicalStateExtend (fun ss => markedPhysicalStateExtend (fun tt =>
    markedPhysicalEdgeCoefficient P hP V pads Z hZ ψ η d₀ Y Q q ss tt * star (f ss) * g tt) t) s

theorem markedPhysicalEdgePairing_ambient {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (f g : MarkedPhysicalState P (pads+1) Z → ℂ) :
    markedPhysicalEdgePairing P hP V pads Z hZ ψ η d₀ Y Q q f g =
      ∑ s,∑ t,markedPhysicalEdgePairTerm P hP V pads Z hZ ψ η d₀ Y Q q f g s t := by
  symm
  unfold markedPhysicalEdgePairTerm
  have he (s : Z × MarkedPhysicalMarking P (pads+1)) :
      (∑ t : Z × MarkedPhysicalMarking P (pads+1),markedPhysicalStateExtend (fun ss =>
        markedPhysicalStateExtend (fun tt => markedPhysicalEdgeCoefficient P hP V pads Z hZ
          ψ η d₀ Y Q q ss tt * star (f ss) * g tt) t) s) =
      markedPhysicalStateExtend (fun ss => ∑ tt,markedPhysicalEdgeCoefficient P hP V pads Z hZ
        ψ η d₀ Y Q q ss tt * star (f ss) * g tt) s := by
    by_cases hs : MarkedPhysicalStateCondition s.1.1 s.2
    · simp only [markedPhysicalStateExtend,dite_eq_left hs]
      simpa only [markedPhysicalStateExtend] using
        (markedPhysicalStateExtend_sum (fun tt => markedPhysicalEdgeCoefficient P hP V pads Z hZ
          ψ η d₀ Y Q q ⟨s,hs⟩ tt * star (f ⟨s,hs⟩) * g tt))
    · simp only [markedPhysicalStateExtend,dite_eq_right hs,Finset.sum_const_zero]
  simp_rw [he]
  exact markedPhysicalStateExtend_sum _

theorem markedPhysicalStateToRaw_copied_eq_iff {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (pads : ℕ)
    (Z : Finset (ℤ × ℤ)) (s t : MarkedPhysicalState P (pads+1) Z) :
    ((markedRawActiveSplit pads) (markedPhysicalStateToRaw P hP (pads+1) Z s).2.1).1 =
        ((markedRawActiveSplit pads) (markedPhysicalStateToRaw P hP (pads+1) Z t).2.1).1 ↔
      (markedPhysicalMarkingSplit pads s.1.2).1=(markedPhysicalMarkingSplit pads t.1.2).1 := by
  apply (markedPhysicalMarkingEquiv P hP pads).injective.eq_iff.symm.trans
  rw [← markedPhysicalMarkingSplit_raw,← markedPhysicalMarkingSplit_raw]
  simp only [markedPhysicalStateToRaw,Equiv.apply_symm_apply]

theorem markedPhysicalEdgePairTerm_off_prefix {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (f g : MarkedPhysicalState P (pads+1) Z → ℂ)
    (a b : MarkedPhysicalMarking P (pads+1))
    (hab : (markedPhysicalMarkingSplit pads a).1≠(markedPhysicalMarkingSplit pads b).1)
    (z w : Z) : markedPhysicalEdgePairTerm P hP V pads Z hZ ψ η d₀ Y Q q f g (z,a) (w,b)=0 := by
  unfold markedPhysicalEdgePairTerm markedPhysicalStateExtend
  split_ifs with hs ht
  · have hp : ((markedRawActiveSplit pads) (markedPhysicalStateToRaw P hP (pads+1) Z ⟨(z,a),hs⟩).2.1).1 ≠
        ((markedRawActiveSplit pads) (markedPhysicalStateToRaw P hP (pads+1) Z ⟨(w,b),ht⟩).2.1).1 :=
      fun h => hab ((markedPhysicalStateToRaw_copied_eq_iff P hP pads Z _ _).mp h)
    simp only [markedPhysicalEdgeCoefficient,hp,ite_false,mul_zero,zero_mul]
  · rfl
  · rfl

theorem markedPhysicalEdgePairing_union_labels {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (f g : MarkedPhysicalState P (pads+1) Z → ℂ) :
    markedPhysicalEdgePairing P hP V pads Z hZ ψ η d₀ Y Q q f g =
      ∑ u : MarkedPhysicalMarking P (pads+2),∑ z : Z,∑ w : Z,
        markedPhysicalEdgePairTerm P hP V pads Z hZ ψ η d₀ Y Q q f g
          (z,markedPhysicalEdgeSource u) (w,markedPhysicalEdgeTarget u) := by
  let F := markedPhysicalEdgePairTerm P hP V pads Z hZ ψ η d₀ Y Q q f g
  have hzw (z : Z) (a : MarkedPhysicalMarking P (pads+1)) :
      (∑ w : Z,∑ b : MarkedPhysicalMarking P (pads+1),F (z,a) (w,b)) =
        ∑ b : MarkedPhysicalMarking P (pads+1),∑ w : Z,F (z,a) (w,b) := Finset.sum_comm
  rw [markedPhysicalEdgePairing_ambient]
  simp only [Fintype.sum_prod_type]
  change (∑ z : Z,∑ a,∑ w : Z,∑ b,F (z,a) (w,b)) = _
  simp_rw [hzw]
  rw [Finset.sum_comm]
  have hz (a : MarkedPhysicalMarking P (pads+1)) :
      (∑ z : Z,∑ b : MarkedPhysicalMarking P (pads+1),∑ w : Z,F (z,a) (w,b)) =
        ∑ b : MarkedPhysicalMarking P (pads+1),∑ z : Z,∑ w : Z,F (z,a) (w,b) := Finset.sum_comm
  simp_rw [hz]
  rw [← markedPhysical_shared_label_sum P pads (fun a b => ∑ z : Z,∑ w : Z,F (z,a) (w,b))]
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
    exact markedPhysicalEdgePairTerm_off_prefix P hP V pads Z hZ ψ η d₀ Y Q q f g a b hab z w

end ArtinMatthews

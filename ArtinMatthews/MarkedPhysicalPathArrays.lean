module

public import ArtinMatthews.MarkedPhysicalSupportedMoment
public import ArtinMatthews.MarkedPhysicalEdgeReindex


set_option backward.privateInPublic true
@[expose] public section

/-! Exact ordered marking-array and position-array enumeration of all
physical paths. Invalid arrays contribute zero; no list order is quotiented. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section
attribute [local instance] markedPhysicalMomentFintype markedPhysicalMomentDecidableEq

abbrev MarkedPhysicalPositionPath (Z : Finset (ℤ × ℤ)) (n : ℕ) := Fin (n+1) → Z
abbrev MarkedPhysicalLabelPath {J : Type*} (P : J → Finset ℕ) (M n : ℕ) :=
  Fin (n+1) → MarkedPhysicalMarking P M

def MarkedPhysicalPathArrayValid {J : Type*} {P : J → Finset ℕ} {M n : ℕ}
    {Z : Finset (ℤ × ℤ)}
    (pos : MarkedPhysicalPositionPath Z n) (labels : MarkedPhysicalLabelPath P M n) : Prop :=
  ∀ v,MarkedPhysicalStateCondition (pos v).1 (labels v)

def markedPhysicalPathOfArrays {J : Type*} {P : J → Finset ℕ} {M n : ℕ}
    {Z : Finset (ℤ × ℤ)}
    (pos : MarkedPhysicalPositionPath Z n) (labels : MarkedPhysicalLabelPath P M n)
    (h : MarkedPhysicalPathArrayValid pos labels) : Fin (n+1) → MarkedPhysicalState P M Z :=
  fun v => ⟨(pos v,labels v),h v⟩

def markedPhysicalPathArrayEquiv {J : Type*} (P : J → Finset ℕ)
    (M : ℕ) (Z : Finset (ℤ × ℤ)) (n : ℕ) :
    (Fin (n+1) → MarkedPhysicalState P M Z) ≃
      {a : MarkedPhysicalPositionPath Z n × MarkedPhysicalLabelPath P M n //
        MarkedPhysicalPathArrayValid a.1 a.2} where
  toFun p := ⟨(fun v => (p v).1.1,fun v => (p v).1.2),fun v => (p v).2⟩
  invFun a := markedPhysicalPathOfArrays a.1.1 a.1.2 a.2
  left_inv p := by funext v; apply Subtype.ext; rfl
  right_inv a := by apply Subtype.ext; rfl

def markedPhysicalPathArrayExtend {J : Type*} {P : J → Finset ℕ} {M n : ℕ}
    {Z : Finset (ℤ × ℤ)} (F : (Fin (n+1) → MarkedPhysicalState P M Z) → ℂ)
    (pos : MarkedPhysicalPositionPath Z n) (labels : MarkedPhysicalLabelPath P M n) : ℂ :=
  if h : MarkedPhysicalPathArrayValid pos labels then F (markedPhysicalPathOfArrays pos labels h) else 0

theorem markedPhysicalPathArrayExtend_sum {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) (n : ℕ)
    (F : (Fin (n+1) → MarkedPhysicalState P M Z) → ℂ) :
    (∑ p,F p)=∑ labels : MarkedPhysicalLabelPath P M n,
      ∑ pos : MarkedPhysicalPositionPath Z n,markedPhysicalPathArrayExtend F pos labels := by
  let C := fun a : MarkedPhysicalPositionPath Z n × MarkedPhysicalLabelPath P M n =>
    MarkedPhysicalPathArrayValid a.1 a.2
  let H := fun a : {a // C a} => F (markedPhysicalPathOfArrays a.1.1 a.1.2 a.2)
  have hE := Equiv.sum_comp (markedPhysicalPathArrayEquiv P M Z n) H
  have hsub : (∑ a : {a // C a},H a) =
      ∑ a : MarkedPhysicalPositionPath Z n × MarkedPhysicalLabelPath P M n,
        markedPhysicalPathArrayExtend F a.1 a.2 := by
    symm
    exact Finset.sum_congr_set {a | C a}
      (fun a => markedPhysicalPathArrayExtend F a.1 a.2) H
      (fun a ha => by
        change MarkedPhysicalPathArrayValid a.1 a.2 at ha
        simp only [markedPhysicalPathArrayExtend,dite_eq_left ha,H])
      (fun a ha => by
        change ¬MarkedPhysicalPathArrayValid a.1 a.2 at ha
        simp only [markedPhysicalPathArrayExtend,dite_eq_right ha])
  calc
    _ = ∑ p,H ((markedPhysicalPathArrayEquiv P M Z n) p) := by
      apply Finset.sum_congr rfl
      intro p _
      exact congrArg F ((markedPhysicalPathArrayEquiv P M Z n).symm_apply_apply p).symm
    _ = ∑ a : {a // C a},H a := hE
    _ = _ := by rw [hsub,Fintype.sum_prod_type,Finset.sum_comm]

theorem markedPhysicalPathArrayOfArrays_position {J : Type*} {P : J → Finset ℕ} {M n : ℕ}
    {Z : Finset (ℤ × ℤ)} (pos : MarkedPhysicalPositionPath Z n) (labels : MarkedPhysicalLabelPath P M n)
    (h : MarkedPhysicalPathArrayValid pos labels) (v : Fin (n+1)) :
    (markedPhysicalPathOfArrays pos labels h v).1.1=pos v := rfl

theorem markedPhysicalPathArrayOfArrays_labels {J : Type*} {P : J → Finset ℕ} {M n : ℕ}
    {Z : Finset (ℤ × ℤ)} (pos : MarkedPhysicalPositionPath Z n) (labels : MarkedPhysicalLabelPath P M n)
    (h : MarkedPhysicalPathArrayValid pos labels) (v : Fin (n+1)) :
    (markedPhysicalPathOfArrays pos labels h v).1.2=labels v := rfl

end
end ArtinMatthews

module

public import ArtinMatthews.MarkedPhysicalJointBonferroni
public import ArtinMatthews.MarkedPhysicalDampingSchedule
public import ArtinMatthews.MarkedPhysicalCoordinateCopyBounds


set_option backward.privateInPublic true
@[expose] public section

/-! Performed inactive-prime truncation on the original signed physical
geometric path/copy summand. Both endpoint damping multiplicities and the
fixed coordinate kernel are identified exactly before bounding the error. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalVisitQ_mem_unitInterval {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (N : ℕ) (v : Fin (N+1)) : 0 ≤ markedMemoryVisitQ q N v ∧ markedMemoryVisitQ q N v ≤ 1 := by
  have h := markedMemoryEta_mem_unitInterval hq0 hq1 N v
  unfold markedMemoryEta at h
  constructor <;> linarith

theorem markedPhysicalPathDamping_joint {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) {q : ℝ} (hq : 0 ≤ q)
    (n : ℕ) (path : Fin (n+2) → MarkedPhysicalState P M Z) :
    (∏ v : Fin (n+1),markedPhysicalEndpointDamping P M q (path v.castSucc).1.1.1*
      markedPhysicalEndpointDamping P M q (path v.succ).1.1.1) =
      markedPhysicalJointPrimeWeight Finset.univ (fun v => (path v).1.2) (markedMemoryVisitQ q (n+1))
        (fun v => (path v).1.1.1.1.natAbs) :=
  markedPhysicalPathDamping_visit_schedule P M Z hq n path

theorem markedPhysicalPathDamping_bonferroni_bounds {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (M : ℕ) (Z : Finset (ℤ × ℤ)) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (n : ℕ) (path : Fin (n+2) → MarkedPhysicalState P M Z) (m : ℕ) :
    markedPhysicalJointBonferroni Finset.univ (fun v => (path v).1.2) (markedMemoryVisitQ q (n+1))
        (fun v => (path v).1.1.1.1.natAbs) (2*m+1) ≤
      (∏ v : Fin (n+1),markedPhysicalEndpointDamping P M q (path v.castSucc).1.1.1*
        markedPhysicalEndpointDamping P M q (path v.succ).1.1.1) ∧
      (∏ v : Fin (n+1),markedPhysicalEndpointDamping P M q (path v.castSucc).1.1.1*
        markedPhysicalEndpointDamping P M q (path v.succ).1.1.1) ≤
        markedPhysicalJointBonferroni Finset.univ (fun v => (path v).1.2) (markedMemoryVisitQ q (n+1))
          (fun v => (path v).1.1.1.1.natAbs) (2*m) := by
  rw [markedPhysicalPathDamping_joint P M Z hq0 n path]
  exact markedPhysicalJointBonferroni_bounds hdis Finset.univ _ _
    (fun v _ => markedPhysicalVisitQ_mem_unitInterval hq0 hq1 _ v) _ m

theorem markedPhysicalMomentGeometricCopies_joint_damping
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ) (hV : ∀ j,0<V j)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ) (hq : 0 ≤ q) (n : ℕ)
    (path : Fin (n+2) → MarkedPhysicalState P (pads+1) Z)
    (copies : Fin (n+1) → (J → Equiv.Perm (Fin (pads+1))) × (J → Equiv.Perm (Fin (pads+1))))
    (root completion : ℤ × ℤ) (z : Fin (n+2) → ℤ × ℤ)
    (hdet : markedMinorIntegerDet root completion=1)
    (hpos : ∀ v,(path v).1.1.1=markedPhysicalRootLift root completion (z v)) :
    (∏ v : Fin (n+1),markedPhysicalMomentGeometricCopy P hP V pads Z hZ ψ η d₀ Y Q q v.val
      (path v.castSucc) (path v.succ) (copies v)) =
      (markedPhysicalJointPrimeWeight Finset.univ (fun v => (path v).1.2) (markedMemoryVisitQ q (n+1))
        (fun v => (path v).1.1.1.1.natAbs):ℂ)*
      markedPhysicalCoordinatePathKernel P hP V pads Z ψ η d₀ Y Q (n+1) path copies z := by
  have hs := congrArg (fun t : ℝ => (t:ℂ)) (markedPhysicalPathDamping_joint P (pads+1) Z hq n path)
  push_cast at hs
  rw [markedPhysicalMomentGeometricCopies_coordinate P hP V pads Z ψ η d₀ Y Q hZ hV q (n+1)
    path copies root completion z hdet hpos,hs]
  rfl

theorem markedPhysicalMomentGeometricCopies_bonferroni_error
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) (V : J → ℝ) (hV : ∀ j,0<V j)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ)
    (path : Fin (n+2) → MarkedPhysicalState P (pads+1) Z)
    (copies : Fin (n+1) → (J → Equiv.Perm (Fin (pads+1))) × (J → Equiv.Perm (Fin (pads+1))))
    (root completion : ℤ × ℤ) (z : Fin (n+2) → ℤ × ℤ)
    (hdet : markedMinorIntegerDet root completion=1)
    (hpos : ∀ v,(path v).1.1.1=markedPhysicalRootLift root completion (z v)) (m : ℕ) :
    ‖(∏ v : Fin (n+1),markedPhysicalMomentGeometricCopy P hP V pads Z hZ ψ η d₀ Y Q q v.val
        (path v.castSucc) (path v.succ) (copies v))-
      markedPhysicalCoordinatePathKernel P hP V pads Z ψ η d₀ Y Q (n+1) path copies z*
        (markedPhysicalJointBonferroni Finset.univ (fun v => (path v).1.2) (markedMemoryVisitQ q (n+1))
          (fun v => (path v).1.1.1.1.natAbs) (2*m):ℂ)‖ ≤
      ‖markedPhysicalCoordinatePathKernel P hP V pads Z ψ η d₀ Y Q (n+1) path copies z‖*
        markedPhysicalJointBonferroniTail Finset.univ (fun v => (path v).1.2) (markedMemoryVisitQ q (n+1))
          (fun v => (path v).1.1.1.1.natAbs) (2*m+1) := by
  rw [markedPhysicalMomentGeometricCopies_joint_damping P hP V hV pads Z hZ ψ η d₀ Y Q q hq0
    n path copies root completion z hdet hpos,mul_comm (_:ℂ)]
  exact markedPhysicalJointBonferroni_complex_error hdis Finset.univ _ _
    (fun v _ => markedPhysicalVisitQ_mem_unitInterval hq0 hq1 _ v) _ m _

end ArtinMatthews

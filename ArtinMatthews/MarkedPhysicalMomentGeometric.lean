module

public import ArtinMatthews.MarkedPhysicalMomentGuarded
public import ArtinMatthews.MarkedPhysicalGeometricAdjoint
public import ArtinMatthews.MarkedPhysicalRawMatrixEntry


set_option backward.privateInPublic true
@[expose] public section

/-! The true physical even moment as a forward chronological path with
alternating geometric cutoffs. All source charges and good tests remain
literal; the different tilted-memory adjoint is not substituted. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Classical ComplexOrder
noncomputable section
attribute [local instance] markedPhysicalMomentFintype markedPhysicalMomentDecidableEq

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ)
  (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)

local notation "State" => MarkedPhysicalState P (pads+1) Z
local notation "Slots" => J → Equiv.Perm (Fin (pads+1))

def markedPhysicalMomentGeometricCopy (j : ℕ) (s t : State) (c : Slots × Slots) : ℂ :=
  ((Fintype.card Slots:ℂ)⁻¹)^2 *
    (if j%2=0 then markedPhysicalEdgeMatrix P hP V pads Z hZ ψ η d₀ Y Q q
      else markedPhysicalEdgeMatrix P hP V pads Z hZ (markedRawEdgeAdjointCutoff ψ)
        (fun u => star (η u)) d₀ Y Q q)
      (markedPhysicalSlotEquiv P (pads+1) Z c.1 s) (markedPhysicalSlotEquiv P (pads+1) Z c.2 t)

theorem markedPhysicalMomentBareEdgeCopy_sum_geometric
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j))) (j : ℕ) (s t : State) :
    (∑ c : Slots × Slots, markedPhysicalMomentBareEdgeCopy P hP V pads Z hZ ψ η d₀ Y Q q j s t c) =
      ∑ c : Slots × Slots, markedPhysicalMomentGeometricCopy P hP V pads Z hZ ψ η d₀ Y Q q j s t c := by
  by_cases hj : j%2=0
  · simp only [markedPhysicalMomentBareEdgeCopy,markedPhysicalMomentGeometricCopy,hj,ite_true]
  · have hs (u v : State) :
        star (markedPhysicalEdgeMatrix P hP V pads Z hZ ψ η d₀ Y Q q u v) =
          markedPhysicalEdgeMatrix P hP V pads Z hZ (markedRawEdgeAdjointCutoff ψ)
            (fun x => star (η x)) d₀ Y Q q v u :=
      congrFun (congrFun (markedPhysicalEdgeMatrix_geometric_adjoint P hP hdisj V pads Z hZ ψ η d₀ Y Q q) v) u
    simp only [markedPhysicalMomentBareEdgeCopy,markedPhysicalMomentGeometricCopy,hj,ite_false,
      Fintype.sum_prod_type,hs]
    rw [Finset.sum_comm]

theorem markedPhysicalMomentBareCopies_sum_geometric
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j))) (n j : ℕ) (p : Fin (n+1) → State) :
    (∑ copies : Fin n → Slots × Slots, ∏ v : Fin n,
      markedPhysicalMomentBareEdgeCopy P hP V pads Z hZ ψ η d₀ Y Q q
        (j+v.val) (p v.castSucc) (p v.succ) (copies v)) =
    ∑ copies : Fin n → Slots × Slots, ∏ v : Fin n,
      markedPhysicalMomentGeometricCopy P hP V pads Z hZ ψ η d₀ Y Q q
        (j+v.val) (p v.castSucc) (p v.succ) (copies v) := by
  calc
    _ = ∏ v : Fin n, ∑ c : Slots × Slots,
        markedPhysicalMomentBareEdgeCopy P hP V pads Z hZ ψ η d₀ Y Q q
          (j+v.val) (p v.castSucc) (p v.succ) c := (Fintype.prod_sum _).symm
    _ = ∏ v : Fin n, ∑ c : Slots × Slots,
        markedPhysicalMomentGeometricCopy P hP V pads Z hZ ψ η d₀ Y Q q
          (j+v.val) (p v.castSucc) (p v.succ) c := by
      apply Finset.prod_congr rfl
      intro v _
      exact markedPhysicalMomentBareEdgeCopy_sum_geometric P hP V pads Z hZ ψ η d₀ Y Q q hdisj _ _ _
    _ = _ := Fintype.prod_sum _

theorem markedPhysicalPositionMoment_geometric_paths
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j)))
    (G : State → Prop) (hV : ∀ j,0≤V j) (R : ℕ) (hR : 0<R) :
    markedPhysicalPositionMoment P (pads+1) Z V
      (markedPhysicalRestrictedMatrix P hP V pads Z hZ ψ η d₀ Y Q q G) R =
      markedPhysicalMass V (pads+1) *
        (∑ p : MarkedPhysicalMomentPath P (pads+1) Z R,
          if (p 0).1.1=(p (Fin.last (2*R))).1.1 ∧ (∀ v,G (p v)) then
            ∑ copies : Fin (2*R) → Slots × Slots, ∏ v : Fin (2*R),
              markedPhysicalMomentGeometricCopy P hP V pads Z hZ ψ η d₀ Y Q q
                v.val (p v.castSucc) (p v.succ) (copies v)
          else 0).re := by
  rw [markedPhysicalPositionMoment_guarded_copies P hP V pads Z hZ ψ η d₀ Y Q q G hV R hR]
  congr 2
  apply Finset.sum_congr rfl
  intro p _
  split_ifs
  · simpa only [zero_add] using markedPhysicalMomentBareCopies_sum_geometric
      P hP V pads Z hZ ψ η d₀ Y Q q hdisj (2*R) 0 p
  · rfl

end
end ArtinMatthews

module

public import ArtinMatthews.MarkedPhysicalCoordinateKernel
public import ArtinMatthews.MarkedPhysicalMomentGeometric


set_option backward.privateInPublic true
@[expose] public section

/-! Exact factorization on the original physical path/copy carrier.
Complex coordinate kernels are fixed at the path and labels, while the
original q-hit dampings are left as separate arithmetic factors. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ)
  (pads : ℕ) (Z : Finset (ℤ × ℤ))
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)

def markedPhysicalCoordinateCopy (j : ℕ) (s t : MarkedPhysicalState P (pads+1) Z)
    (c : (J → Equiv.Perm (Fin (pads+1))) × (J → Equiv.Perm (Fin (pads+1))))
    (z z' : ℤ × ℤ) : ℂ :=
  ((Fintype.card (J → Equiv.Perm (Fin (pads+1))):ℂ)⁻¹)^2 *
    (if j%2=0 then markedPhysicalCoordinateKernel V pads ψ η d₀ Y Q
      else markedPhysicalCoordinateKernel V pads (markedRawEdgeAdjointCutoff ψ) (fun u => star (η u)) d₀ Y Q)
      (markedPhysicalStateToRaw P hP (pads+1) Z (markedPhysicalSlotEquiv P (pads+1) Z c.1 s)).2.1
      (markedPhysicalStateToRaw P hP (pads+1) Z (markedPhysicalSlotEquiv P (pads+1) Z c.2 t)).2.1 z z'

theorem markedPhysicalMomentGeometricCopy_coordinate
    (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (hV : ∀ j,0<V j) (q : ℝ)
    (j : ℕ) (s t : MarkedPhysicalState P (pads+1) Z)
    (c : (J → Equiv.Perm (Fin (pads+1))) × (J → Equiv.Perm (Fin (pads+1))))
    (root completion z z' : ℤ × ℤ) (hdet : markedMinorIntegerDet root completion=1)
    (hs : s.1.1.1=markedPhysicalRootLift root completion z)
    (ht : t.1.1.1=markedPhysicalRootLift root completion z') :
    markedPhysicalMomentGeometricCopy P hP V pads Z hZ ψ η d₀ Y Q q j s t c =
      (markedPhysicalEndpointDamping P (pads+1) q s.1.1.1:ℂ)*
        markedPhysicalCoordinateCopy P hP V pads Z ψ η d₀ Y Q j s t c z z' *
        (markedPhysicalEndpointDamping P (pads+1) q t.1.1.1:ℂ) := by
  unfold markedPhysicalMomentGeometricCopy markedPhysicalCoordinateCopy
  split_ifs
  · rw [markedPhysicalEdgeMatrix_coordinate_kernel P hP V hV pads Z hZ ψ η d₀ Y Q q
      (markedPhysicalSlotEquiv P (pads+1) Z c.1 s) (markedPhysicalSlotEquiv P (pads+1) Z c.2 t)
      root completion z z' hdet hs ht]
    simp only [markedPhysicalSlotEquiv_position]
    ring
  · rw [markedPhysicalEdgeMatrix_coordinate_kernel P hP V hV pads Z hZ (markedRawEdgeAdjointCutoff ψ)
      (fun u => star (η u)) d₀ Y Q q
      (markedPhysicalSlotEquiv P (pads+1) Z c.1 s) (markedPhysicalSlotEquiv P (pads+1) Z c.2 t)
      root completion z z' hdet hs ht]
    simp only [markedPhysicalSlotEquiv_position]
    ring

theorem markedPhysicalMomentGeometricCopies_coordinate
    (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (hV : ∀ j,0<V j) (q : ℝ) (n : ℕ)
    (path : Fin (n+1) → MarkedPhysicalState P (pads+1) Z)
    (copies : Fin n → (J → Equiv.Perm (Fin (pads+1))) × (J → Equiv.Perm (Fin (pads+1))))
    (root completion : ℤ × ℤ) (z : Fin (n+1) → ℤ × ℤ)
    (hdet : markedMinorIntegerDet root completion=1)
    (hpos : ∀ v,(path v).1.1.1=markedPhysicalRootLift root completion (z v)) :
    (∏ v : Fin n,markedPhysicalMomentGeometricCopy P hP V pads Z hZ ψ η d₀ Y Q q v.val
      (path v.castSucc) (path v.succ) (copies v)) =
      (∏ v : Fin n,(markedPhysicalEndpointDamping P (pads+1) q (path v.castSucc).1.1.1:ℂ)*
        (markedPhysicalEndpointDamping P (pads+1) q (path v.succ).1.1.1:ℂ)) *
      ∏ v : Fin n,markedPhysicalCoordinateCopy P hP V pads Z ψ η d₀ Y Q v.val
        (path v.castSucc) (path v.succ) (copies v) (z v.castSucc) (z v.succ) := by
  calc
    _ = ∏ v : Fin n,((markedPhysicalEndpointDamping P (pads+1) q (path v.castSucc).1.1.1:ℂ)*
        (markedPhysicalEndpointDamping P (pads+1) q (path v.succ).1.1.1:ℂ))*
      markedPhysicalCoordinateCopy P hP V pads Z ψ η d₀ Y Q v.val
        (path v.castSucc) (path v.succ) (copies v) (z v.castSucc) (z v.succ) := by
      apply Finset.prod_congr rfl
      intro v _
      rw [markedPhysicalMomentGeometricCopy_coordinate P hP V pads Z ψ η d₀ Y Q hZ hV q v.val
        (path v.castSucc) (path v.succ) (copies v) root completion _ _ hdet (hpos _) (hpos _)]
      ring
    _ = _ := Finset.prod_mul_distrib

end ArtinMatthews

module

public import ArtinMatthews.MarkedPhysicalHilbertMatrix
public import ArtinMatthews.MarkedMinorArcRawEdgeGeometricAdjoint


set_option backward.privateInPublic true
@[expose] public section

/-! The actual constant-mass physical adjoint is geometric reversal.
The original real q damping and mass denominator are unchanged. No
adjoint claim is made for the different tilted-memory charged operator. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Classical
noncomputable section
attribute [local instance] Classical.propDecidable

theorem markedRawJoint_geometric_adjoint_of_copied
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s t : MarkedRawState P (pads+1) B Z)
    (hcopy : ((markedRawActiveSplit pads) s.2.1).1=((markedRawActiveSplit pads) t.2.1).1) :
    markedRawEdgeJointCoefficient hZ (markedRawEdgeAdjointCutoff ψ) (fun u => star (η u))
      d₀ Y Q ρ (fun u => star (χ u)) t s =
        star (markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ s t) := by
  let copied := ((markedRawActiveSplit pads) s.2.1).1
  let a := ((markedRawActiveSplit pads) s.2.1).2
  let b := ((markedRawActiveSplit pads) t.2.1).2
  have hs : (s.1,((markedRawActiveSplit pads).symm (copied,a),s.2.2))=s := by
    change (s.1,((markedRawActiveSplit pads).symm ((markedRawActiveSplit pads) s.2.1),s.2.2))=s
    rw [Equiv.symm_apply_apply]
  have ht : (t.1,((markedRawActiveSplit pads).symm (copied,b),t.2.2))=t := by
    dsimp only [copied,b]
    rw [hcopy]
    change (t.1,((markedRawActiveSplit pads).symm ((markedRawActiveSplit pads) t.2.1),t.2.2))=t
    rw [Equiv.symm_apply_apply]
  have h := markedRawEdgeJointCoefficient_geometric_adjoint hdisj hZ ψ η d₀ Y Q ρ χ
    copied s.1 t.1 a b s.2.2 t.2.2
  rwa [hs,ht] at h

theorem markedPhysicalEdgeCoefficient_geometric_adjoint
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime)
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j))) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (s t : MarkedPhysicalState P (pads+1) Z) :
    markedPhysicalEdgeCoefficient P hP V pads Z hZ (markedRawEdgeAdjointCutoff ψ)
      (fun u => star (η u)) d₀ Y Q q s t =
        star (markedPhysicalEdgeCoefficient P hP V pads Z hZ ψ η d₀ Y Q q t s) := by
  have hd : Pairwise (fun i j => Disjoint (markedRawPrimeBand (P i)) (markedRawPrimeBand (P j))) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (Finset.disjoint_left.mp (hdisj hij)) ((mem_markedRawPrimeBand _ _).mp hp)
      ((mem_markedRawPrimeBand _ _).mp hq)
  unfold markedPhysicalEdgeCoefficient
  dsimp only
  by_cases hc : ((markedRawActiveSplit pads) (markedPhysicalStateToRaw P hP (pads+1) Z s).2.1).1 =
      ((markedRawActiveSplit pads) (markedPhysicalStateToRaw P hP (pads+1) Z t).2.1).1
  · rw [ite_eq_left hc,ite_eq_left hc.symm]
    have hj := markedRawJoint_geometric_adjoint_of_copied hd hZ ψ η d₀ Y Q 1 (fun _ => 1)
      (markedPhysicalStateToRaw P hP (pads+1) Z t) (markedPhysicalStateToRaw P hP (pads+1) Z s) hc.symm
    simp only [star_one] at hj
    rw [hj]
    simp only [star_mul,Complex.star_def,Complex.conj_ofReal]
    ring
  · rw [ite_eq_right hc,ite_eq_right (Ne.symm hc)]
    simp only [mul_zero,star_zero]

theorem markedPhysicalEdgeMatrix_geometric_adjoint
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime)
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j))) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ) :
    (markedPhysicalEdgeMatrix P hP V pads Z hZ ψ η d₀ Y Q q)ᴴ =
      markedPhysicalEdgeMatrix P hP V pads Z hZ (markedRawEdgeAdjointCutoff ψ)
        (fun u => star (η u)) d₀ Y Q q := by
  ext s t
  change star (_/(markedPhysicalMass V (pads+1):ℂ))=_
  rw [markedPhysicalEdgeMatrix,markedPhysicalEdgeCoefficient_geometric_adjoint P hP hdisj]
  simp only [star_div₀,Complex.star_def,Complex.conj_ofReal]

theorem markedPhysicalRestrictedMatrix_geometric_adjoint
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime)
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j))) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (G : MarkedPhysicalState P (pads+1) Z → Prop) :
    (markedPhysicalRestrictedMatrix P hP V pads Z hZ ψ η d₀ Y Q q G)ᴴ =
      markedPhysicalRestrictedMatrix P hP V pads Z hZ (markedRawEdgeAdjointCutoff ψ)
        (fun u => star (η u)) d₀ Y Q q G := by
  simp only [markedPhysicalRestrictedMatrix,Matrix.conjTranspose_mul,
    (markedPhysicalGoodMatrix_isHermitian G).eq,
    (markedPhysicalSlotMatrix_isHermitian P (pads+1) Z).eq,
    markedPhysicalEdgeMatrix_geometric_adjoint P hP hdisj,Matrix.mul_assoc]

end
end ArtinMatthews

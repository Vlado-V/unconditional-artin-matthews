module

public import ArtinMatthews.MarkedPhysicalPathResidueSum
public import ArtinMatthews.MarkedPhysicalGeometricPathTube
public import ArtinMatthews.MarkedPrimitiveCoordinateTube


set_option backward.privateInPublic true
@[expose] public section

/-! Every nonzero original even-moment term lies in a fixed finite
primitive coordinate tube, derived from its actual copy expansion. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section
attribute [local instance] markedPhysicalMomentFintype markedPhysicalMomentDecidableEq

def markedPhysicalMomentTubeRadius (n : ℕ) (K H : ℝ) : ℕ :=
  ⌈16+512*(n:ℝ)*K*H⌉₊

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ)
  (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)

theorem markedPhysicalMomentPathTerm_ne_zero_guards
    (G : MarkedPhysicalState P (pads+1) Z → Prop) (R : ℕ)
    (p : MarkedPhysicalMomentPath P (pads+1) Z R)
    (h : markedPhysicalMomentPathTerm P hP V pads Z hZ ψ η d₀ Y Q q G R p≠0) :
    (p 0).1.1=(p (Fin.last (2*R))).1.1 ∧ (∀ v,G (p v)) := by
  unfold markedPhysicalMomentPathTerm at h
  split_ifs at h with hc
  · exact hc
  · exact False.elim (h rfl)

theorem markedPhysicalMomentPathTerm_ne_zero_copy
    (G : MarkedPhysicalState P (pads+1) Z → Prop) (R : ℕ)
    (p : MarkedPhysicalMomentPath P (pads+1) Z R)
    (h : markedPhysicalMomentPathTerm P hP V pads Z hZ ψ η d₀ Y Q q G R p≠0) :
    ∃ copies : Fin (2*R) → (J → Equiv.Perm (Fin (pads+1))) × (J → Equiv.Perm (Fin (pads+1))),
      ∀ k : Fin (2*R),markedPhysicalMomentGeometricCopy P hP V pads Z hZ ψ η d₀ Y Q q
        k.val (p k.castSucc) (p k.succ) (copies k)≠0 := by
  have hc := markedPhysicalMomentPathTerm_ne_zero_guards P hP V pads Z hZ ψ η d₀ Y Q q G R p h
  rw [markedPhysicalMomentPathTerm,ite_eq_left hc] at h
  obtain ⟨copies,_,hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨copies,fun k => (Finset.prod_ne_zero_iff.mp hn) k (Finset.mem_univ k)⟩

theorem markedPhysicalMomentPathTerm_coordinate_tube
    (G : MarkedPhysicalState P (pads+1) Z → Prop) (R : ℕ)
    (p : MarkedPhysicalMomentPath P (pads+1) Z R)
    (h : markedPhysicalMomentPathTerm P hP V pads Z hZ ψ η d₀ Y Q q G R p≠0)
    (K : ℝ) (hd₀ : 0<d₀) (hY : 0<Y) (hK : 0≤K)
    (hψ : Function.support ψ ⊆ Set.Icc (-K) K)
    {S : ℕ} [NeZero S] {U W : ℝ} (hU : 1<U) (hW : 1<W)
    (hbox : Z⊆markedPhysicalPrimitiveBox U (16*U) W (2*W))
    (r : MarkedPhysicalCanonicalRoot S U (16*U) W (2*W))
    (hroot : (p 0).1.1.1=markedPhysicalCanonicalRootPosition r) (v : Fin (2*R+1)) :
    markedPhysicalRootCoordinates (markedPhysicalCanonicalRootPosition r)
      (markedPhysicalCanonicalCompletion r) (p v).1.1.1 ∈
        markedPrimitiveCoordinateTube (markedPhysicalMomentTubeRadius (2*R) K (d₀*Y)) := by
  obtain ⟨copies,hcopies⟩ := markedPhysicalMomentPathTerm_ne_zero_copy
    P hP V pads Z hZ ψ η d₀ Y Q q G R p h
  have hdet : markedMinorIntegerDet (p 0).1.1.1 (markedPhysicalCanonicalCompletion r)=1 := by
    rw [hroot]
    exact markedPhysicalCanonicalCompletion_det hU hW r
  have hr : ((markedPhysicalCanonicalCompletion r).1:ℝ)/(p 0).1.1.1.1∈Set.Icc (0:ℝ) 1 := by
    rw [hroot]
    exact markedPhysicalCanonicalRatio_mem hU r
  have ht := markedPhysicalMomentGeometricPath_tube P hP V pads Z hZ ψ η d₀ Y Q q K
    hd₀ hY hK hψ (2*R) p copies hcopies (markedPhysicalCanonicalCompletion r) hdet
    U (zero_lt_one.trans hU)
    (fun z hz => markedPhysicalPrimitiveBox_first_bounds (hbox hz)) hr v
  rw [hroot] at ht
  have hp := (markedPhysicalRootCoordinates_primitive_iff _ _ _
    (markedPhysicalCanonicalCompletion_det hU hW r)).mpr (hZ _ (p v).1.1.2)
  apply markedPrimitiveCoordinateTube_of_real_bound _ _ hp
  · exact ht.1.trans (Nat.le_ceil _)
  · exact ht.2.trans (by
      have hh := Nat.le_ceil (16+512*((2*R:ℕ):ℝ)*K*(d₀*Y))
      dsimp only [markedPhysicalMomentTubeRadius]
      linarith)

end
end ArtinMatthews

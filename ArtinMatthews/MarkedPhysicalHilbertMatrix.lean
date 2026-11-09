module

public import ArtinMatthews.MarkedPhysicalSlopeBandwidth
public import ArtinMatthews.MarkedPhysicalSlotMatrix
public import ArtinMatthews.MarkedPositionLocalizedMoment


set_option backward.privateInPublic true
@[expose] public section

/-! Actual physical matrices for the constant original atom mass. The
coefficient already contains this mass, so the Hilbert operator divides
by it exactly once. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Classical ComplexOrder
noncomputable section

theorem markedPhysicalMass_pos {J : Type*} [Fintype J]
    (V : J → ℝ) (M : ℕ) (hV : ∀ j, 0<V j) : 0 < markedPhysicalMass V M :=
  Finset.prod_pos (fun j _ => pow_pos (inv_pos.mpr (hV j)) M)

def markedPhysicalHilbertVector {ι : Type*} (σ : ℝ) (f : ι → ℂ) : ι → ℂ :=
  fun s => (Real.sqrt σ : ℂ)*f s

def markedPhysicalEdgeMatrix {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ) :
    Matrix (MarkedPhysicalState P (pads+1) Z) (MarkedPhysicalState P (pads+1) Z) ℂ :=
  fun s t => markedPhysicalEdgeCoefficient P hP V pads Z hZ ψ η d₀ Y Q q s t /
    (markedPhysicalMass V (pads+1) : ℂ)

theorem markedPhysicalEdgeMatrix_pairing {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (V : J → ℝ) (hV : ∀ j,0<V j)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (f g : MarkedPhysicalState P (pads+1) Z → ℂ) :
    markedMatrixPairing (markedPhysicalEdgeMatrix P hP V pads Z hZ ψ η d₀ Y Q q)
      (markedPhysicalHilbertVector (markedPhysicalMass V (pads+1)) f)
      (markedPhysicalHilbertVector (markedPhysicalMass V (pads+1)) g) =
        markedPhysicalEdgePairing P hP V pads Z hZ ψ η d₀ Y Q q f g := by
  rw [markedMatrixPairing_expansion]
  unfold markedPhysicalEdgePairing
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  let σ := markedPhysicalMass V (pads+1)
  have hσ : 0<σ := markedPhysicalMass_pos V (pads+1) hV
  have hσc : (σ:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hσ.ne'
  have hs : (Real.sqrt σ : ℂ)^2=(σ:ℂ) := by exact_mod_cast Real.sq_sqrt hσ.le
  change (_/(σ:ℂ))*star ((Real.sqrt σ:ℂ)*f s)*((Real.sqrt σ:ℂ)*g t)=_
  rw [star_mul]
  have hr : star (Real.sqrt σ:ℂ)=(Real.sqrt σ:ℂ) := by simp only [Complex.star_def,Complex.conj_ofReal]
  rw [hr]
  calc
    _ = markedPhysicalEdgeCoefficient P hP V pads Z hZ ψ η d₀ Y Q q s t *
        ((Real.sqrt σ:ℂ)^2/(σ:ℂ))*star (f s)*g t := by ring
    _ = _ := by rw [hs,div_self hσc,mul_one]

def markedPhysicalGoodMatrix {ι : Type*} [DecidableEq ι] (G : ι → Prop) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun s => if G s then 1 else 0)

theorem markedPhysicalGoodMatrix_isHermitian {ι : Type*} [DecidableEq ι] (G : ι → Prop) :
    (markedPhysicalGoodMatrix G).IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro s
  by_cases hs : G s <;> simp [hs]

theorem markedPhysicalGoodMatrix_action {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : ι → Prop) (f : ι → ℂ) :
    markedPhysicalGoodMatrix G *ᵥ f=markedPhysicalGoodVector G f := by
  funext s
  simp only [markedPhysicalGoodMatrix,Matrix.mulVec_diagonal,markedPhysicalGoodVector]
  by_cases hs : G s <;> simp [hs]

def markedPhysicalRestrictedMatrix {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (G : MarkedPhysicalState P (pads+1) Z → Prop) :
    Matrix (MarkedPhysicalState P (pads+1) Z) (MarkedPhysicalState P (pads+1) Z) ℂ :=
  markedPhysicalGoodMatrix G * markedPhysicalSlotMatrix P (pads+1) Z *
    markedPhysicalEdgeMatrix P hP V pads Z hZ ψ η d₀ Y Q q *
      markedPhysicalSlotMatrix P (pads+1) Z * markedPhysicalGoodMatrix G

theorem markedPhysicalEdgeMatrix_cell_shift {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q K U : ℝ)
    (hd₀ : 0<d₀) (hY : 0<Y) (hK : 0≤K) (hU : 0<U)
    (hψ : Function.support ψ ⊆ Set.Icc (-K) K) (hfirst : ∀ z∈Z,U≤(z.1:ℝ))
    (s t : MarkedPhysicalState P (pads+1) Z)
    (h : markedPhysicalEdgeMatrix P hP V pads Z hZ ψ η d₀ Y Q q s t≠0) :
    markedPhysicalSlopeCell ((d₀*Y)/U^2) t.1.1.1-
      markedPhysicalSlopeCell ((d₀*Y)/U^2) s.1.1.1 ∈
        Finset.Icc (-(⌈2*K+1⌉₊:ℤ)) (⌈2*K+1⌉₊:ℤ) := by
  apply markedPhysicalEdgeCoefficient_cell_shift P hP V pads Z hZ ψ η d₀ Y Q q K U
    hd₀ hY hK hU hψ hfirst s t
  intro hz
  exact h (by simp only [markedPhysicalEdgeMatrix,hz,zero_div])

theorem markedPhysicalRestrictedMatrix_cell_shift {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q K U : ℝ)
    (G : MarkedPhysicalState P (pads+1) Z → Prop)
    (hd₀ : 0<d₀) (hY : 0<Y) (hK : 0≤K) (hU : 0<U)
    (hψ : Function.support ψ ⊆ Set.Icc (-K) K) (hfirst : ∀ z∈Z,U≤(z.1:ℝ)) :
    ∀ s t, markedPhysicalRestrictedMatrix P hP V pads Z hZ ψ η d₀ Y Q q G s t≠0 →
      markedPhysicalSlopeCell ((d₀*Y)/U^2) t.1.1.1-
        markedPhysicalSlopeCell ((d₀*Y)/U^2) s.1.1.1 ∈
          Finset.Icc (-(⌈2*K+1⌉₊:ℤ)) (⌈2*K+1⌉₊:ℤ) := by
  let p := fun s : MarkedPhysicalState P (pads+1) Z => s.1.1
  let c := fun z : Z => markedPhysicalSlopeCell ((d₀*Y)/U^2) z.1
  let R : ℤ := ⌈2*K+1⌉₊
  let T := markedPhysicalEdgeMatrix P hP V pads Z hZ ψ η d₀ Y Q q
  let S := markedPhysicalSlotMatrix P (pads+1) Z
  let D := markedPhysicalGoodMatrix G
  have hT : ∀ s t,T s t≠0 → c (p t)-c (p s)∈Finset.Icc (-R) R :=
    markedPhysicalEdgeMatrix_cell_shift P hP V pads Z hZ ψ η d₀ Y Q q K U
      hd₀ hY hK hU hψ hfirst
  have hS : ∀ s t,S s t≠0 → p s=p t := markedPhysicalSlotMatrix_preserves_position P (pads+1) Z
  have hD : ∀ s t,D s t≠0 → p s=p t :=
    markedMatrix_diagonal_preserves_position _ p
  have h1 := markedMatrix_bandwidth_mul_right T S p c R hT hS
  have h2 := markedMatrix_bandwidth_mul_right (T*S) D p c R h1 hD
  have h3 := markedMatrix_bandwidth_mul_left ((T*S)*D) S p c R h2 hS
  have h4 := markedMatrix_bandwidth_mul_left (S*((T*S)*D)) D p c R h3 hD
  simpa only [markedPhysicalRestrictedMatrix,T,S,D,Matrix.mul_assoc] using h4

end
end ArtinMatthews

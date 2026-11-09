module

public import ArtinMatthews.MarkedPhysicalMomentIndexSum
public import ArtinMatthews.MarkedPhysicalCoordinateIndexFactor


set_option backward.privateInPublic true
@[expose] public section

/-! Exact global assembly of the original physical even moment into
root-independent complex coefficients and literal guarded root weights. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section
attribute [local instance] markedPhysicalMomentFintype markedPhysicalMomentDecidableEq

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ)
  (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)

def markedPhysicalMomentRootDampingSum
    (G : MarkedPhysicalState P (pads+1) Z → Prop) (R : ℕ) (K U W : ℝ)
    (S : MarkedPhysicalLabelPath P (pads+1) (2*R) → ℕ) (hS : ∀ a,S a≠0) : ℂ :=
  ∑ i : MarkedPhysicalCoordinateIndex P (pads+1) (2*R) (markedPhysicalMomentTubeRadius (2*R) K (d₀*Y)),
    markedPhysicalCoordinateIndexCoefficient P hP V pads ψ η d₀ Y Q i*
      (letI : NeZero (S i.1) := ⟨hS i.1⟩
       ∑ r : MarkedPhysicalCanonicalRoot (S i.1) U (16*U) W (2*W),
         markedPhysicalCoordinateIndexDamping P pads Z q G i r)

theorem markedPhysicalMomentIndexSum_eq_root_damping
    (G : MarkedPhysicalState P (pads+1) Z → Prop) (hV : ∀ j,0<V j)
    (R : ℕ) (K U W : ℝ) (hU : 1<U) (hW : 1<W)
    (S : MarkedPhysicalLabelPath P (pads+1) (2*R) → ℕ) (hS : ∀ a,S a≠0) :
    markedPhysicalMomentIndexSum P hP V pads Z hZ ψ η d₀ Y Q q G R K U W S hS=
      markedPhysicalMomentRootDampingSum P hP V pads Z ψ η d₀ Y Q q G R K U W S hS := by
  unfold markedPhysicalMomentIndexSum markedPhysicalMomentRootDampingSum
  apply Finset.sum_congr rfl
  intro i _
  let : NeZero (S i.1) := ⟨hS i.1⟩
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  exact markedPhysicalCoordinateIndexTerm_factor P hP V pads Z hZ ψ η d₀ Y Q q G hV i hU hW r

theorem markedPhysicalPositionMoment_root_damping
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j)))
    (G : MarkedPhysicalState P (pads+1) Z → Prop) (hV : ∀ j,0<V j) (R : ℕ) (hR : 0<R)
    (K U W : ℝ) (hd₀ : 0<d₀) (hY : 0<Y) (hK : 0≤K)
    (hψ : Function.support ψ ⊆ Set.Icc (-K) K) (hU : 1<U) (hW : 1<W)
    (hbox : Z⊆markedPhysicalPrimitiveBox U (16*U) W (2*W))
    (S : MarkedPhysicalLabelPath P (pads+1) (2*R) → ℕ) (hS : ∀ a,S a≠0) :
    markedPhysicalPositionMoment P (pads+1) Z V
      (markedPhysicalRestrictedMatrix P hP V pads Z hZ ψ η d₀ Y Q q G) R =
      markedPhysicalMass V (pads+1)*
        (markedPhysicalMomentRootDampingSum P hP V pads Z ψ η d₀ Y Q q G R K U W S hS).re := by
  rw [markedPhysicalPositionMoment_index_sum P hP V pads Z hZ ψ η d₀ Y Q q
    hdisj G (fun j => (hV j).le) R hR K U W hd₀ hY hK hψ hU hW hbox S hS,
    markedPhysicalMomentIndexSum_eq_root_damping P hP V pads Z hZ ψ η d₀ Y Q q G hV R K U W hU hW S hS]

end
end ArtinMatthews

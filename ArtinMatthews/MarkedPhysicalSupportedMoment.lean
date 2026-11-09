module

public import ArtinMatthews.MarkedPhysicalGeometricActivePath


set_option backward.privateInPublic true
@[expose] public section

/-! Every surviving physical moment summand carries its genuine active
path. Restriction to this finite supported subtype discards only literal
zero terms and introduces no multiplicity or injectivity premise. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Classical
noncomputable section
attribute [local instance] markedPhysicalMomentFintype markedPhysicalMomentDecidableEq

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ)
  (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)

local notation "State" => MarkedPhysicalState P (pads+1) Z
local notation "Slots" => J → Equiv.Perm (Fin (pads+1))

abbrev MarkedPhysicalSupportedCopies (n : ℕ) (p : Fin (n+1) → State) :=
  {copies : Fin n → Slots × Slots // ∀ v : Fin n,
    markedPhysicalMomentGeometricCopy P hP V pads Z hZ ψ η d₀ Y Q q
      v.val (p v.castSucc) (p v.succ) (copies v)≠0}

def markedPhysicalSupportedCopiesActivePath (n : ℕ) (p : Fin (n+1) → State)
    (c : MarkedPhysicalSupportedCopies P hP V pads Z hZ ψ η d₀ Y Q q n p) :
    MarkedMemoryActivePathData (fun j => markedRawPrimeBand (P j)) pads Z n :=
  markedPhysicalSupportedActivePath P hP V pads Z hZ ψ η d₀ Y Q q n p c.1 c.2

theorem markedPhysicalMomentCopy_sum_supported (n : ℕ) (p : Fin (n+1) → State) :
    (∑ copies : Fin n → Slots × Slots, ∏ v : Fin n,
      markedPhysicalMomentGeometricCopy P hP V pads Z hZ ψ η d₀ Y Q q
        v.val (p v.castSucc) (p v.succ) (copies v)) =
    ∑ c : MarkedPhysicalSupportedCopies P hP V pads Z hZ ψ η d₀ Y Q q n p, ∏ v : Fin n,
      markedPhysicalMomentGeometricCopy P hP V pads Z hZ ψ η d₀ Y Q q
        v.val (p v.castSucc) (p v.succ) (c.1 v) := by
  let allowed := fun copies : Fin n → Slots × Slots => ∀ v : Fin n,
    markedPhysicalMomentGeometricCopy P hP V pads Z hZ ψ η d₀ Y Q q
      v.val (p v.castSucc) (p v.succ) (copies v)≠0
  let f := fun copies : Fin n → Slots × Slots => ∏ v : Fin n,
    markedPhysicalMomentGeometricCopy P hP V pads Z hZ ψ η d₀ Y Q q
      v.val (p v.castSucc) (p v.succ) (copies v)
  have hz : (∑ c : {copies // ¬allowed copies},f c.1)=0 := by
    apply Finset.sum_eq_zero
    intro c _
    by_contra hn
    apply c.2
    exact fun v => (Finset.prod_ne_zero_iff.mp hn) v (Finset.mem_univ v)
  have he := Fintype.sum_subtype_add_sum_subtype allowed f
  rw [hz,add_zero] at he
  exact he.symm

theorem markedPhysicalPositionMoment_supported_paths
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j)))
    (G : State → Prop) (hV : ∀ j,0≤V j) (R : ℕ) (hR : 0<R) :
    markedPhysicalPositionMoment P (pads+1) Z V
      (markedPhysicalRestrictedMatrix P hP V pads Z hZ ψ η d₀ Y Q q G) R =
      markedPhysicalMass V (pads+1) *
        (∑ p : MarkedPhysicalMomentPath P (pads+1) Z R,
          if (p 0).1.1=(p (Fin.last (2*R))).1.1 ∧ (∀ v,G (p v)) then
            ∑ c : MarkedPhysicalSupportedCopies P hP V pads Z hZ ψ η d₀ Y Q q (2*R) p,
              ∏ v : Fin (2*R),markedPhysicalMomentGeometricCopy P hP V pads Z hZ ψ η d₀ Y Q q
                v.val (p v.castSucc) (p v.succ) (c.1 v)
          else 0).re := by
  rw [markedPhysicalPositionMoment_geometric_paths P hP V pads Z hZ ψ η d₀ Y Q q hdisj G hV R hR]
  congr 2
  apply Finset.sum_congr rfl
  intro p _
  split_ifs
  · exact markedPhysicalMomentCopy_sum_supported P hP V pads Z hZ ψ η d₀ Y Q q (2*R) p
  · rfl

end
end ArtinMatthews

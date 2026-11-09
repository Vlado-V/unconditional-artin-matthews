module

public import ArtinMatthews.MarkedPhysicalMomentCopySupport


set_option backward.privateInPublic true
@[expose] public section

/-! The actual physical moment as a guarded path observable. Good tests
at every visit remain in the outer guard; oriented kernels and both slot
copies remain literal inside it. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Classical ComplexOrder
noncomputable section
attribute [local instance] markedPhysicalMomentFintype markedPhysicalMomentDecidableEq

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ)
  (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
  (G : MarkedPhysicalState P (pads+1) Z → Prop)

local notation "State" => MarkedPhysicalState P (pads+1) Z
local notation "Slots" => J → Equiv.Perm (Fin (pads+1))
local notation "A" => markedPhysicalRestrictedMatrix P hP V pads Z hZ ψ η d₀ Y Q q G
local notation "T" => markedPhysicalEdgeMatrix P hP V pads Z hZ ψ η d₀ Y Q q

def markedPhysicalMomentBareEdgeCopy (j : ℕ) (s t : State) (c : Slots × Slots) : ℂ :=
  ((Fintype.card Slots:ℂ)⁻¹)^2 *
    (if j%2=0 then
      T (markedPhysicalSlotEquiv P (pads+1) Z c.1 s) (markedPhysicalSlotEquiv P (pads+1) Z c.2 t)
    else star (T (markedPhysicalSlotEquiv P (pads+1) Z c.1 t) (markedPhysicalSlotEquiv P (pads+1) Z c.2 s)))

theorem markedPhysicalMomentEdgeCopy_of_good (j : ℕ) (s t : State) (c : Slots × Slots)
    (hs : G s) (ht : G t) :
    markedPhysicalMomentEdgeCopy P hP V pads Z hZ ψ η d₀ Y Q q G j s t c =
      markedPhysicalMomentBareEdgeCopy P hP V pads Z hZ ψ η d₀ Y Q q j s t c := by
  simp only [markedPhysicalMomentEdgeCopy,markedPhysicalMomentBareEdgeCopy,
    ite_eq_left hs,ite_eq_left ht,one_mul]

theorem markedPhysicalPositionMoment_guarded_copies (hV : ∀ j,0≤V j) (R : ℕ) (hR : 0<R) :
    markedPhysicalPositionMoment P (pads+1) Z V A R =
      markedPhysicalMass V (pads+1) *
        (∑ p : MarkedPhysicalMomentPath P (pads+1) Z R,
          if (p 0).1.1=(p (Fin.last (2*R))).1.1 ∧ (∀ v,G (p v)) then
            ∑ copies : Fin (2*R) → Slots × Slots, ∏ v : Fin (2*R),
              markedPhysicalMomentBareEdgeCopy P hP V pads Z hZ ψ η d₀ Y Q q
                v.val (p v.castSucc) (p v.succ) (copies v)
          else 0).re := by
  rw [markedPhysicalPositionMoment_copies P hP V pads Z hZ ψ η d₀ Y Q q G hV R]
  congr 2
  apply Finset.sum_congr rfl
  intro p _
  by_cases hc : (p 0).1.1=(p (Fin.last (2*R))).1.1
  · simp only [hc,true_and,ite_true]
    by_cases hg : ∀ v,G (p v)
    · rw [ite_eq_left hg]
      apply Finset.sum_congr rfl
      intro copies _
      apply Finset.prod_congr rfl
      intro v _
      exact markedPhysicalMomentEdgeCopy_of_good P hP V pads Z hZ ψ η d₀ Y Q q G
        _ _ _ _ (hg _) (hg _)
    · rw [ite_eq_right hg]
      apply Finset.sum_eq_zero
      intro copies _
      by_contra hn
      exact hg (markedPhysicalMomentCopies_all_good P hP V pads Z hZ ψ η d₀ Y Q q G
        (2*R) (by omega) 0 p copies (by simpa only [zero_add] using hn))
  · simp only [hc,false_and,ite_false]

end
end ArtinMatthews

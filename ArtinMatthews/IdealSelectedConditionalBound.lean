module

public import ArtinMatthews.IdealSelectedConditionalIdentity
public import ArtinMatthews.IdealConditionalBilinear
public import ArtinMatthews.IdealKernelTranspose


set_option backward.privateInPublic true
@[expose] public section

/-! A comparison uniform in the shared labels gives its full-label
bilinear bound with the two original harmonic energies. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealSelectedFill_restriction {G : Type*} {P : G → Finset ℕ} {M : ℕ}
    (S : Finset (G × Fin M)) (a : MarkedPhysicalMarking P M)
    (x : IdealSelectedLabels (idealFullSelectedBands P S)) :
    idealFullSelectedLabels S (idealSelectedFill S a x)=x := by
  funext v
  simp [idealFullSelectedLabels,idealSelectedFill,idealFlattenLabels,finiteProductFill,v.property]

theorem idealSelectedConditional_pairing_bound {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (hV : ∀ g,0 < bandReciprocalMass (P g))
    (S T : Finset (G × Fin M)) (hST : Disjoint S T)
    (K : MarkedPhysicalMarking P M → IdealSelectedLabels (idealResidualBands P S) →
      IdealSelectedLabels (idealResidualBands P T) → ℂ)
    (hK : ∀ a x y,K (idealSelectedFill (S ∪ T) a ((idealSelectedUnionEquiv P S T hST).symm (x,y))) x y=K a x y)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcmp : ∀ a (u : IdealSelectedLabels (idealResidualBands P S) → ℂ)
      (v : IdealSelectedLabels (idealResidualBands P T) → ℂ),
      ‖∑ x,(idealSelectedMass (idealResidualBands P S) x:ℂ)*u x*
        ∑ y,(idealSelectedMass (idealResidualBands P T) y:ℂ)*v y*K a x y‖ ≤
      ε*Real.sqrt (idealFrameEnergy (idealSelectedMass (idealResidualBands P S)) u)*
        Real.sqrt (idealFrameEnergy (idealSelectedMass (idealResidualBands P T)) v))
    (f g : MarkedPhysicalMarking P M → ℂ)
    (hf : ∀ a b,f (idealMix S a b)=f a) (hg : ∀ a b,g (idealMix T a b)=g a) :
    ‖idealLabelExpectation P M (fun a => star (f a)*g a*
      K a (idealFullSelectedLabels S a) (idealFullSelectedLabels T a))‖ ≤
      ε*Real.sqrt (idealLabelEnergy P M f)*Real.sqrt (idealLabelEnergy P M g) := by
  let W := fun a : MarkedPhysicalMarking P M =>
    ∑ x : IdealSelectedLabels (idealResidualBands P S),
      (idealSelectedMass (idealResidualBands P S) x:ℂ)*g (idealSelectedFill S a x)*
        ∑ y : IdealSelectedLabels (idealResidualBands P T),
          (idealSelectedMass (idealResidualBands P T) y:ℂ)*star (f (idealSelectedFill T a y))*K a x y
  have he : idealLabelExpectation P M (fun a => star (f a)*g a*
      K a (idealFullSelectedLabels S a) (idealFullSelectedLabels T a))=idealLabelExpectation P M W := by
    rw [idealSelectedConditional_reindex P hV S T hST]
    apply congrArg (idealLabelExpectation P M)
    funext a
    dsimp only [W]
    simp only [mul_sum]
    apply sum_congr rfl
    intro x _
    apply sum_congr rfl
    intro y _
    let z := idealSelectedFill (S ∪ T) a ((idealSelectedUnionEquiv P S T hST).symm (x,y))
    have hzS : idealFullSelectedLabels S z=x := by
      rw [show z=idealSelectedFill S (idealSelectedFill T a y) x from idealSelectedFill_union_left S T hST a x y]
      exact idealSelectedFill_restriction S _ x
    have hzT : idealFullSelectedLabels T z=y := by
      rw [show z=idealSelectedFill T (idealSelectedFill S a x) y from idealSelectedFill_union_right S T hST a x y]
      exact idealSelectedFill_restriction T _ y
    have hfz : f z=f (idealSelectedFill T a y) := by
      rw [show z=idealSelectedFill S (idealSelectedFill T a y) x from idealSelectedFill_union_left S T hST a x y]
      exact idealSelectedFill_invariant S f hf _ x
    have hgz : g z=g (idealSelectedFill S a x) := by
      rw [show z=idealSelectedFill T (idealSelectedFill S a x) y from idealSelectedFill_union_right S T hST a x y]
      exact idealSelectedFill_invariant T g hg _ y
    change (idealSelectedMass (idealResidualBands P S) x:ℂ)*
      (idealSelectedMass (idealResidualBands P T) y:ℂ)*
        (star (f z)*g z*K z (idealFullSelectedLabels S z) (idealFullSelectedLabels T z))= _
    rw [hfz,hgz,hzS,hzT,hK]
    ring
  rw [he]
  apply idealSelectedConditional_norm P hV T S f g W hε
  intro a
  have hh := hcmp a (fun x => g (idealSelectedFill S a x)) (fun y => star (f (idealSelectedFill T a y)))
  rw [idealFrameEnergy_star] at hh
  calc
    ‖W a‖ ≤ ε*Real.sqrt (idealFrameEnergy (idealSelectedMass (idealResidualBands P S))
        (fun x => g (idealSelectedFill S a x)))*
      Real.sqrt (idealFrameEnergy (idealSelectedMass (idealResidualBands P T))
        (fun y => f (idealSelectedFill T a y))) := hh
    _ = _ := by
      change ε*Real.sqrt (idealFrameEnergy (idealSelectedMass (idealResidualBands P S))
          (fun x => g (idealSelectedFill S a x)))*
        Real.sqrt (idealFrameEnergy (idealSelectedMass (idealResidualBands P T))
          (fun y => f (idealSelectedFill T a y)))=
        ε*Real.sqrt (idealFrameEnergy (idealSelectedMass (idealResidualBands P T))
          (fun y => f (idealSelectedFill T a y)))*
        Real.sqrt (idealFrameEnergy (idealSelectedMass (idealResidualBands P S))
          (fun x => g (idealSelectedFill S a x)))
      ring

end
end ArtinMatthews

module

public import ArtinMatthews.IdealProductRestriction
public import ArtinMatthews.IdealKernelCauchy


set_option backward.privateInPublic true
@[expose] public section

/-! Replacing selected coordinates integrates against their original
harmonic product law and preserves the full law after outer averaging. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def idealSelectedFill {G : Type*} {P : G → Finset ℕ} {M : ℕ}
    (S : Finset (G × Fin M)) (a : MarkedPhysicalMarking P M)
    (x : IdealSelectedLabels (idealFullSelectedBands P S)) : MarkedPhysicalMarking P M :=
  idealFlattenLabels.symm (finiteProductFill S (idealFlattenLabels a) x)

theorem idealSelectedFill_mix {G : Type*} {P : G → Finset ℕ} {M : ℕ}
    (S : Finset (G × Fin M)) (a b : MarkedPhysicalMarking P M) :
    idealSelectedFill S a (idealFullSelectedLabels S b)=idealMix S a b := by
  funext g i
  dsimp only [idealSelectedFill,idealFlattenLabels,Equiv.coe_fn_symm_mk,
    finiteProductFill,idealFullSelectedLabels,idealMix]
  split_ifs <;> rfl

theorem idealFullSelected_marginal_scalar {G A : Type*} [Fintype G] [DecidableEq G]
    [CommRing A] [Algebra ℝ A] (P : G → Finset ℕ) {M : ℕ}
    (hV : ∀ g,0 < bandReciprocalMass (P g)) (S : Finset (G × Fin M))
    (F : IdealSelectedLabels (idealFullSelectedBands P S) → A) :
    idealLabelExpectation P M (fun a => F (idealFullSelectedLabels S a))=
      ∑ x : IdealSelectedLabels (idealFullSelectedBands P S),
        algebraMap ℝ A (idealSelectedMass (idealFullSelectedBands P S) x)*F x := by
  let w : ∀ v : G × Fin M,↥(P v.1) → A :=
    fun v p => algebraMap ℝ A (markedHarmonicAtom (P v.1) p)
  have hw (v : G × Fin M) : (∑ p,w v p)=1 := by
    dsimp only [w]
    rw [← map_sum,markedHarmonicAtom_sum _ (hV v.1),map_one]
  have hm (a : MarkedPhysicalMarking P M) :
      finiteProductMarginalMass w (idealFlattenLabels a)=algebraMap ℝ A (idealLabelMass P M a) := by
    unfold finiteProductMarginalMass w
    rw [← map_prod]
    exact congrArg (algebraMap ℝ A) (idealFlattenLabels_mass P a)
  calc
    _ = ∑ x : ∀ v : G × Fin M,↥(P v.1),
        finiteProductMarginalMass w x*F (finiteProductRestriction S x) := by
      rw [← (idealFlattenLabels (P:=P) (M:=M)).sum_comp
        (fun x => finiteProductMarginalMass w x*F (finiteProductRestriction S x))]
      unfold idealLabelExpectation
      apply sum_congr rfl
      intro a _
      rw [hm]
      rfl
    _ = ∑ x : IdealSelectedLabels (idealFullSelectedBands P S),
        finiteProductMarginalMass (fun v : ↥S => w v) x*F x := finiteProductMarginal w hw S F
    _ = _ := by
      apply sum_congr rfl
      intro x _
      unfold finiteProductMarginalMass idealSelectedMass w idealFullSelectedBands
      rw [map_prod]

theorem idealSelectedFill_expectation {G A : Type*} [Fintype G] [DecidableEq G]
    [CommRing A] [Algebra ℝ A] (P : G → Finset ℕ) {M : ℕ}
    (hV : ∀ g,0 < bandReciprocalMass (P g)) (S : Finset (G × Fin M))
    (a : MarkedPhysicalMarking P M) (F : MarkedPhysicalMarking P M → A) :
    (∑ x : IdealSelectedLabels (idealFullSelectedBands P S),
      algebraMap ℝ A (idealSelectedMass (idealFullSelectedBands P S) x)*F (idealSelectedFill S a x))=
      idealLabelExpectation P M (fun b => F (idealMix S a b)) := by
  rw [← idealFullSelected_marginal_scalar P hV S (fun x => F (idealSelectedFill S a x))]
  simp_rw [idealSelectedFill_mix]

theorem idealSelectedFill_full_expectation {G A : Type*} [Fintype G] [DecidableEq G]
    [CommRing A] [Algebra ℝ A] (P : G → Finset ℕ) {M : ℕ}
    (hV : ∀ g,0 < bandReciprocalMass (P g)) (S : Finset (G × Fin M))
    (F : MarkedPhysicalMarking P M → A) :
    idealLabelExpectation P M (fun a =>
      ∑ x : IdealSelectedLabels (idealFullSelectedBands P S),
        algebraMap ℝ A (idealSelectedMass (idealFullSelectedBands P S) x)*F (idealSelectedFill S a x))=
      idealLabelExpectation P M F := by
  simp_rw [idealSelectedFill_expectation P hV]
  exact idealLabelExpectation_mix P M hV S F

theorem idealSelectedFill_energy {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (hV : ∀ g,0 < bandReciprocalMass (P g))
    (S : Finset (G × Fin M)) (f : MarkedPhysicalMarking P M → ℂ) :
    (∑ a,idealLabelMass P M a*
      idealFrameEnergy (idealSelectedMass (idealFullSelectedBands P S))
        (fun x => f (idealSelectedFill S a x)))=idealLabelEnergy P M f := by
  exact idealSelectedFill_full_expectation P hV S (fun a => ‖f a‖^2)

end
end ArtinMatthews

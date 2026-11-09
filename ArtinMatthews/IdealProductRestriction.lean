module

public import ArtinMatthews.FiniteProductMarginal
public import ArtinMatthews.IdealProductAverage
public import ArtinMatthews.IdealSelectedLabels


set_option backward.privateInPublic true
@[expose] public section

/-! Arbitrary tests on selected source coordinates have exactly the
selected harmonic product law after averaging the full label vector. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def idealFlattenLabels {J : Type*} {P : J → Finset ℕ} {M : ℕ} :
    MarkedPhysicalMarking P M ≃ (∀ v : J × Fin M,↥(P v.1)) where
  toFun a v := a v.1 v.2
  invFun a j i := a (j,i)
  left_inv a := rfl
  right_inv a := by funext v; cases v; rfl

theorem idealFlattenLabels_mass {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (a : MarkedPhysicalMarking P M) :
    finiteProductMarginalMass (fun v : J × Fin M => markedHarmonicAtom (P v.1))
      (idealFlattenLabels a)=idealLabelMass P M a := by
  unfold finiteProductMarginalMass idealLabelMass
  rw [Fintype.prod_prod_type]
  rfl

def idealFullSelectedBands {J : Type*} {M : ℕ} (P : J → Finset ℕ)
    (S : Finset (J × Fin M)) : ↥S → Finset ℕ := fun v => P v.val.1

def idealFullSelectedLabels {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (S : Finset (J × Fin M)) (a : MarkedPhysicalMarking P M) :
    IdealSelectedLabels (idealFullSelectedBands P S) := fun v => a v.val.1 v.val.2

theorem idealFullSelected_marginal {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (S : Finset (J × Fin M)) (F : IdealSelectedLabels (idealFullSelectedBands P S) → ℂ) :
    idealLabelExpectation P M (fun a => F (idealFullSelectedLabels S a))=
      ∑ y : IdealSelectedLabels (idealFullSelectedBands P S),
        (idealSelectedMass (idealFullSelectedBands P S) y:ℂ)*F y := by
  let w : ∀ v : J × Fin M,↥(P v.1) → ℂ :=
    fun v p => (markedHarmonicAtom (P v.1) p:ℂ)
  have hw (v : J × Fin M) : (∑ p,w v p)=1 := by
    dsimp only [w]
    rw [← Complex.ofReal_sum,markedHarmonicAtom_sum _ (hV v.1),Complex.ofReal_one]
  have hm (a : MarkedPhysicalMarking P M) :
      finiteProductMarginalMass w (idealFlattenLabels a)=(idealLabelMass P M a:ℂ) := by
    unfold finiteProductMarginalMass w
    rw [← Complex.ofReal_prod]
    exact congrArg (fun r : ℝ => (r:ℂ)) (idealFlattenLabels_mass P a)
  calc
    _ = ∑ x : ∀ v : J × Fin M,↥(P v.1),
        finiteProductMarginalMass w x*F (finiteProductRestriction S x) := by
      rw [← (idealFlattenLabels (P:=P) (M:=M)).sum_comp
        (fun x => finiteProductMarginalMass w x*F (finiteProductRestriction S x))]
      unfold idealLabelExpectation
      apply sum_congr rfl
      intro a _
      rw [hm]
      rfl
    _ = ∑ y : IdealSelectedLabels (idealFullSelectedBands P S),
        finiteProductMarginalMass (fun v : ↥S => w v) y*F y := finiteProductMarginal w hw S F
    _ = _ := by
      apply sum_congr rfl
      intro y _
      unfold finiteProductMarginalMass idealSelectedMass w idealFullSelectedBands
      rw [Complex.ofReal_prod]

end
end ArtinMatthews

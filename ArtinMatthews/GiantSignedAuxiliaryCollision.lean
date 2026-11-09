module

public import ArtinMatthews.GiantSignedProductCoordinate
public import ArtinMatthews.GiantSignedIdealAuxiliary


set_option backward.privateInPublic true
@[expose] public section

/-! Collision probabilities use the original auxiliary draws and keep
all ordered source and target active labels. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantSignedAuxiliary_coordinate_mass
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (C : J → Finset (Fin k))
    (g : J) (i : C g) (p : P g) :
    (∑ aux : GiantTwoSidedPatternAuxiliary P C,
      idealAuxiliaryMass (fun j => markedHarmonicAtom (P j)) aux *
        (if aux g i = p then 1 else 0 : ℝ)) = markedHarmonicAtom (P g) p := by
  classical
  let w (j : J) (a : C j → P j) := ∏ l, markedHarmonicAtom (P j) (a l)
  have hw (j : J) : ∑ a : C j → P j, w j a = 1 := by
    dsimp only [w]
    rw [← Fintype.prod_sum]
    simp only [markedHarmonicAtom_sum (P j) (hV j), Finset.prod_const_one]
  have ho := giantSignedProduct_coordinate w hw g
    (fun a : C g → P g => if a i = p then (1 : ℝ) else 0)
  have hi := giantSignedProduct_coordinate (fun _ : C g => markedHarmonicAtom (P g))
    (fun _ => markedHarmonicAtom_sum (P g) (hV g)) i
    (fun q : P g => if q = p then (1 : ℝ) else 0)
  calc
    _ = ∑ a : C g → P g, w g a * (if a i = p then 1 else 0 : ℝ) := ho
    _ = ∑ q : P g, markedHarmonicAtom (P g) q * (if q = p then 1 else 0 : ℝ) := hi
    _ = _ := by simp [mul_ite]

def giantSignedAuxCollisionEvent {J : Type*} {P : J → Finset ℕ} {k M : ℕ}
    (C : J → Finset (Fin k)) (a b : MarkedPhysicalMarking P M)
    (e : (Σ g : J, C g) × (Bool × Fin M)) (aux : GiantTwoSidedPatternAuxiliary P C) : Prop :=
  aux e.1.1 e.1.2 = if e.2.1 then b e.1.1 e.2.2 else a e.1.1 e.2.2

theorem giantSignedAuxCollision_probability_le
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k M : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (C : J → Finset (Fin k))
    (a b : MarkedPhysicalMarking P M) (α : ℝ)
    (hAtom : ∀ j p, markedHarmonicAtom (P j) p ≤ α) :
    (∑ aux : GiantTwoSidedPatternAuxiliary P C,
      idealAuxiliaryMass (fun j => markedHarmonicAtom (P j)) aux *
        (if ∃ e : (Σ g : J, C g) × (Bool × Fin M), giantSignedAuxCollisionEvent C a b e aux
          then 1 else 0 : ℝ)) ≤
      (Fintype.card ((Σ g : J, C g) × (Bool × Fin M)) : ℝ) * α := by
  classical
  apply (giantSignedFinite_probability_union
    (idealAuxiliaryMass (fun j => markedHarmonicAtom (P j)))
    (giantSignedIdealAuxiliaryMass_nonneg hV C) (giantSignedAuxCollisionEvent C a b)).trans
  calc
    _ ≤ ∑ _e : (Σ g : J, C g) × (Bool × Fin M), α := by
      apply Finset.sum_le_sum
      intro e _
      let p : P e.1.1 := if e.2.1 then b e.1.1 e.2.2 else a e.1.1 e.2.2
      have hm : (∑ aux : GiantTwoSidedPatternAuxiliary P C,
          idealAuxiliaryMass (fun j => markedHarmonicAtom (P j)) aux *
            (if giantSignedAuxCollisionEvent C a b e aux then 1 else 0 : ℝ)) =
          markedHarmonicAtom (P e.1.1) p := by
        calc
          _ = ∑ aux : GiantTwoSidedPatternAuxiliary P C,
              idealAuxiliaryMass (fun j => markedHarmonicAtom (P j)) aux *
                (if aux e.1.1 e.1.2 = p then 1 else 0 : ℝ) := by
            apply Finset.sum_congr rfl
            intro aux _
            apply congrArg (fun x : ℝ =>
              idealAuxiliaryMass (fun j => markedHarmonicAtom (P j)) aux * x)
            by_cases h : giantSignedAuxCollisionEvent C a b e aux
            · have heq : aux e.1.1 e.1.2 = p := h
              rw [ite_eq_left h, ite_eq_left heq]
            · have hne : ¬aux e.1.1 e.1.2 = p := h
              rw [ite_eq_right h, ite_eq_right hne]
          _ = _ := giantSignedAuxiliary_coordinate_mass hV C e.1.1 e.1.2 p
      rw [hm]
      exact hAtom _ _
    _ = _ := by simp

theorem giantSignedAuxCollision_index_card
    {J : Type*} [Fintype J] {k : ℕ} (C : J → Finset (Fin k)) (M : ℕ) :
    Fintype.card ((Σ g : J, C g) × (Bool × Fin M)) =
      (∑ g, (C g).card) * (2 * M) := by
  simp

end
end ArtinMatthews

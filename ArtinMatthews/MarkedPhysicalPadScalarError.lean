module

public import ArtinMatthews.MarkedPhysicalHarmonicScalar
public import ArtinMatthews.MarkedPhysicalCoprimeScalarDetector


set_option backward.privateInPublic true
@[expose] public section

/-! Exact copied-pad collision correction for the original scalar
detector. The bound charges each fixed pair of unshared labels by
its own harmonic collision mass before taking absolute values. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime)
  (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
  (pads : ℕ) (S T : Finset ℕ) (η : ℝ → ℂ) (Y : ℝ)
  (detector : ℤ → ℤ → ℤ → ℂ) (α β : ℕ → ℂ)

include hP hdis

theorem markedPhysicalCoprimeScalarDetector_sub_survival :
    markedPhysicalCoprimeScalarDetectorSum P S T η Y detector α β-
      markedPhysicalPadSurvivalScalarSum P pads S T η Y detector α β =
      (markedMajorLabelMass P:ℂ)^2*
        ∑ b : (j : J) → ↥(P j),∑ a : (j : J) → ↥(P j),
          if (markedPrimeBandProduct P b).Coprime (markedPrimeBandProduct P a) then
            (markedPhysicalPadCollisionMass P pads b a:ℂ)*
              markedPhysicalScalarDetectorBlock S T η Y detector α β
                (markedPrimeBandProduct P b) (markedPrimeBandProduct P a)
          else 0 := by
  rw [markedPhysicalCoprimeScalarDetectorSum,markedPhysicalCoprimeLabelPairs_sum P hP hdis,
    markedPhysicalPadSurvivalScalarSum,← mul_sub,← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : (markedPrimeBandProduct P b).Coprime (markedPrimeBandProduct P a)
  · simp only [ite_eq_left h,Complex.ofReal_sub,Complex.ofReal_one]
    ring
  · simp only [ite_eq_right h,sub_zero]

theorem markedPhysicalCoprimeScalarDetector_sub_survival_norm_le
    (hV : ∀ j,0 < bandReciprocalMass (P j)) (E : ℝ) (hE : 0 ≤ E)
    (hcollision : ∀ b a,markedPhysicalPadCollisionMass P pads b a ≤ E) :
    ‖markedPhysicalCoprimeScalarDetectorSum P S T η Y detector α β-
      markedPhysicalPadSurvivalScalarSum P pads S T η Y detector α β‖ ≤
      E*markedPhysicalCoprimeScalarDetectorAbsMass P S T η Y detector α β := by
  let C := markedMajorLabelMass P
  let cop (b a : (j : J) → ↥(P j)) :=
    (markedPrimeBandProduct P b).Coprime (markedPrimeBandProduct P a)
  let F (b a : (j : J) → ↥(P j)) := markedPhysicalScalarDetectorBlock S T η Y detector α β
    (markedPrimeBandProduct P b) (markedPrimeBandProduct P a)
  let A (b a : (j : J) → ↥(P j)) := markedPhysicalScalarDetectorAbsBlock S T η Y detector α β
    (markedPrimeBandProduct P b) (markedPrimeBandProduct P a)
  let W := markedPhysicalPadCollisionMass P pads
  rw [markedPhysicalCoprimeScalarDetector_sub_survival P hP hdis,
    markedPhysicalCoprimeScalarDetectorAbsMass,markedPhysicalCoprimeLabelPairs_sum P hP hdis]
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  change C^2*‖∑ b,∑ a,if cop b a then (W b a:ℂ)*F b a else 0‖ ≤
    E*(C^2*∑ b,∑ a,if cop b a then A b a else 0)
  have hsum :
      (∑ b,∑ a,‖if cop b a then (W b a:ℂ)*F b a else 0‖) ≤
        E*(∑ b,∑ a,if cop b a then A b a else 0) := by
    simp only [Finset.mul_sum,mul_ite,mul_zero]
    apply Finset.sum_le_sum
    intro b _
    apply Finset.sum_le_sum
    intro a _
    by_cases hc : cop b a
    · rw [ite_eq_left hc,ite_eq_left hc,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (markedPhysicalPadCollisionMass_nonneg P pads hV b a)]
      exact mul_le_mul (hcollision b a)
        (markedPhysicalScalarDetectorBlock_norm_le S T η Y detector α β _ _) (norm_nonneg _) hE
    · simp only [ite_eq_right hc,norm_zero,le_refl]
  calc
    _ ≤ C^2*(∑ b,∑ a,‖if cop b a then (W b a:ℂ)*F b a else 0‖) :=
      mul_le_mul_of_nonneg_left
        ((norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)) (sq_nonneg _)
    _ ≤ C^2*(E*(∑ b,∑ a,if cop b a then A b a else 0)) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = _ := by ring

end
end ArtinMatthews

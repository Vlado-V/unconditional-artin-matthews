module

public import ArtinMatthews.MarkedMajorMellinIsolation
public import ArtinMatthews.MarkedMajorMellinIsolationL2


set_option backward.privateInPublic true
@[expose] public section

/-! The actual normalized Mellin transform has uniform quadratic L¹ cost and
hence quartic cost when inserted into an L² energy estimate. -/
namespace ArtinMatthews
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem markedMellinIsolation_coefficient_uniform_L2_bound
    (η : ℝ → ℂ) (hη : ContDiff ℝ ∞ η) {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support η ⊆ Icc a b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (θ T : ℝ) (A : ℝ → ℝ → ℂ) (B E : ℝ),
      Continuous (fun p : ℝ × ℝ => A p.1 p.2) →
      (∀ ξ t : ℝ, ‖A ξ t‖ ≤ B) → 0 ≤ E →
      (∀ ξ : ℝ, (∫ t in Icc (-T) T, ‖A ξ t‖^2) ≤ E) →
      IntegrableOn
        (fun t => ‖∫ ξ : ℝ, markedMellinIsolationCoefficient η hη ha hsupp θ ξ*A ξ t‖^2)
        (Icc (-T) T) ∧
      (∫ t in Icc (-T) T,
        ‖∫ ξ : ℝ, markedMellinIsolationCoefficient η hη ha hsupp θ ξ*A ξ t‖^2) ≤
        C*(1+|θ|)^4*E := by
  obtain ⟨C,hC,hbound⟩ := markedMellinIsolation_coefficient_L1_bound η hη ha hsupp
  refine ⟨C^2,by positivity,?_⟩
  intro θ T A B E hA hb hE henergy
  obtain ⟨hint,hineq⟩ := markedMellinIsolation_weighted_L2_interval
    (markedMellinIsolationCoefficient η hη ha hsupp θ) A
    (markedMellinIsolationCoefficient η hη ha hsupp θ).integrable hA hb T henergy
  refine ⟨hint,hineq.trans ?_⟩
  calc
    (∫ ξ : ℝ, ‖markedMellinIsolationCoefficient η hη ha hsupp θ ξ‖)^2*E ≤
        (C*(1+|θ|)^2)^2*E := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (integral_nonneg (fun _ => norm_nonneg _)) (hbound θ) 2) hE
    _ = C^2*(1+|θ|)^4*E := by ring

end
end ArtinMatthews

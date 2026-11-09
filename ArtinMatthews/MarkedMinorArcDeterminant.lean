module

public import ArtinMatthews.MarkedMinorArcGram


set_option backward.privateInPublic true
@[expose] public section

/-! The actual determinant exponential matrix factors into the two
bilinear exponential transforms used in PD (mem:minor-decay). -/
namespace ArtinMatthews
open scoped BigOperators

/-- The actual finite determinant transform on an integer rectangle. -/
noncomputable def markedMinorDeterminantTransform (L T : ℤ) (M N : ℕ)
    (θ : ℝ) (c : ℤ × ℤ → ℂ) (h₁ h₂ : ℤ) : ℂ :=
  ∑ l₁ ∈ Finset.Ico L (L+(M : ℤ)), ∑ l₂ ∈ Finset.Ico T (T+(N : ℤ)),
    c (l₁,l₂) * OAI.Problem337.RealPhase.phase
      (θ*((h₁ : ℝ)*l₂-(h₂ : ℝ)*l₁))

/-- Exact tensor factorization of the actual determinant matrix. -/
theorem markedMinorDeterminantTransform_factor (L T : ℤ) (M N : ℕ)
    (θ : ℝ) (c : ℤ × ℤ → ℂ) (h₁ h₂ : ℤ) :
    markedMinorDeterminantTransform L T M N θ c h₁ h₂ =
      ∑ l₂ ∈ Finset.Ico T (T+(N : ℤ)),
        (∑ l₁ ∈ Finset.Ico L (L+(M : ℤ)), c (l₁,l₂) *
          OAI.Problem337.RealPhase.phase ((-θ)*(h₂ : ℝ)*l₁)) *
            OAI.Problem337.RealPhase.phase (θ*(h₁ : ℝ)*l₂) := by
  unfold markedMinorDeterminantTransform
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l₂ _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l₁ _
  rw [mul_assoc,← OAI.Problem337.RealPhase.phase_add]
  congr 1
  congr 1
  ring

/-- A true L² bound for the determinant matrix, using the proved bilinear
Gram estimate in each tensor coordinate. No spectral estimate is assumed. -/
theorem marked_minor_determinant_energy_le (L T : ℤ) (M N : ℕ)
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ-(a : ℝ)/q| ≤ 1/(q : ℝ)^2) (c : ℤ × ℤ → ℂ) :
    (∑ h₁ ∈ Finset.Ico L (L+(M : ℤ)), ∑ h₂ ∈ Finset.Ico T (T+(N : ℤ)),
      ‖markedMinorDeterminantTransform L T M N θ c h₁ h₂‖^2) ≤
      markedMinorGramBudget M N q * markedMinorGramBudget N M q *
        (∑ l₁ ∈ Finset.Ico L (L+(M : ℤ)), ∑ l₂ ∈ Finset.Ico T (T+(N : ℤ)), ‖c (l₁,l₂)‖^2) := by
  let I := Finset.Ico L (L+(M : ℤ))
  let J := Finset.Ico T (T+(N : ℤ))
  let F := fun h₂ l₂ : ℤ => ∑ l₁ ∈ I, c (l₁,l₂) *
    OAI.Problem337.RealPhase.phase ((-θ)*(h₂ : ℝ)*l₁)
  have hneg : |(-θ)-((-a : ℤ) : ℝ)/q| ≤ 1/(q : ℝ)^2 := by
    simpa only [Int.cast_neg,neg_div,neg_sub_neg,abs_sub_comm] using happrox
  have hfirst (h₂ : ℤ) :
      (∑ h₁ ∈ I, ‖∑ l₂ ∈ J, F h₂ l₂ *
        OAI.Problem337.RealPhase.phase (θ*(h₁ : ℝ)*l₂)‖^2) ≤
        markedMinorGramBudget M N q * ∑ l₂ ∈ J, ‖F h₂ l₂‖^2 :=
    marked_minor_bilinear_energy_le L T M N θ a q hq hcop happrox (F h₂)
  have hsecond (l₂ : ℤ) : (∑ h₂ ∈ J, ‖F h₂ l₂‖^2) ≤
      markedMinorGramBudget N M q * ∑ l₁ ∈ I, ‖c (l₁,l₂)‖^2 :=
    marked_minor_bilinear_energy_le T L N M (-θ) (-a) q hq hcop.neg_left hneg
      (fun l₁ => c (l₁,l₂))
  calc
    _ = ∑ h₂ ∈ J, ∑ h₁ ∈ I, ‖∑ l₂ ∈ J, F h₂ l₂ *
        OAI.Problem337.RealPhase.phase (θ*(h₁ : ℝ)*l₂)‖^2 := by
      rw [Finset.sum_comm]
      simp only [markedMinorDeterminantTransform_factor,I,J,F]
    _ ≤ ∑ h₂ ∈ J, markedMinorGramBudget M N q * ∑ l₂ ∈ J, ‖F h₂ l₂‖^2 :=
      Finset.sum_le_sum (fun h₂ _ => hfirst h₂)
    _ = markedMinorGramBudget M N q * (∑ l₂ ∈ J, ∑ h₂ ∈ J, ‖F h₂ l₂‖^2) := by
      rw [← Finset.mul_sum,Finset.sum_comm]
    _ ≤ markedMinorGramBudget M N q *
        (markedMinorGramBudget N M q * ∑ l₂ ∈ J, ∑ l₁ ∈ I, ‖c (l₁,l₂)‖^2) := by
      apply mul_le_mul_of_nonneg_left _ (markedMinorGramBudget_nonneg M N q hq)
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun l₂ _ => hsecond l₂)
    _ = _ := by rw [Finset.sum_comm]; ring

end ArtinMatthews

module

public import ArtinMatthews.IntegerQuadraticHaar


set_option backward.privateInPublic true
@[expose] public section

/-! Exact phase of a finite quadratic sum, with its genuine sqrt(card)
Gauss normalization. -/

namespace ArtinMatthews.QuadraticWeil

open ArtinMatthews.QuadraticGauss
open OAI.SevenEighths OAI.SevenEighths.FiniteFourier
open OAI.RepresentationTheory.Weil.Local
open scoped Classical
noncomputable section

variable (F : Type) [Field F] [Fintype F]

theorem finite_quadratic_phase (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) :
    FunctionsMetaplectic.Construction.phase (∑ x : F, ψ (x ^ 2)) = residueIndex F ψ := by
  rw [square_sum_eq_gauss hF ψ hψ]
  have hn := primitive_gaussSum_norm (residueCharacter F)
    (primitiveOnIdeals_of_field _ (residueCharacter_nontrivial hF)) ψ
    (AddChar.IsPrimitive.of_ne_one hψ)
  rw [FunctionsMetaplectic.Construction.phase, hn]
  rfl

end

end ArtinMatthews.QuadraticWeil

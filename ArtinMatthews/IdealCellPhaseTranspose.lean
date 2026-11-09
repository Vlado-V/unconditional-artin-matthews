module

public import ArtinMatthews.IdealCellPhaseComparison
public import ArtinMatthews.IdealKernelPairTranspose


set_option backward.privateInPublic true
@[expose] public section

/-! Exact transpose of the two actual character-cell averages moves
them onto the two arbitrary full-tuple tests. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

theorem idealFullCellPhaseAverage_eq_pairAverage (P : A → Finset ℕ) (R : B → Finset ℕ)
    (Q : ℕ) (h ξ ζ α : ℝ) (x : IdealSelectedLabels P) (y : IdealSelectedLabels R) :
    idealFullCellPhaseAverage P R Q h ξ ζ α x y =
      idealKernelPairAverage (idealSelectedMass P) (idealSelectedMass R)
        (idealCharacterCellKernel P Q h ξ) (idealCharacterCellKernel R Q h ξ)
        (fun d e => idealProductPhase ζ α (idealSelectedProduct d) (idealSelectedProduct e)) x y := by
  unfold idealFullCellPhaseAverage idealKernelPairAverage
  apply sum_congr rfl
  intro d _
  apply sum_congr rfl
  intro e _
  rw [Complex.ofReal_mul]
  ring

theorem idealFullCellPhaseAverage_pairing (P : A → Finset ℕ) (R : B → Finset ℕ)
    (Q : ℕ) (h ξ ζ α : ℝ) (f : IdealSelectedLabels P → ℂ) (g : IdealSelectedLabels R → ℂ) :
    (∑ x, (idealSelectedMass P x : ℂ)*f x*
      ∑ y, (idealSelectedMass R y : ℂ)*g y*idealFullCellPhaseAverage P R Q h ξ ζ α x y) =
      ∑ d, (idealSelectedMass P d : ℂ)*idealCharacterCellTranspose P Q h ξ f d*
        ∑ e, (idealSelectedMass R e : ℂ)*idealCharacterCellTranspose R Q h ξ g e*
          idealProductPhase ζ α (idealSelectedProduct d) (idealSelectedProduct e) := by
  let phase (d : IdealSelectedLabels P) (e : IdealSelectedLabels R) :=
    idealProductPhase ζ α (idealSelectedProduct d) (idealSelectedProduct e)
  let K := idealKernelPairAverage (idealSelectedMass P) (idealSelectedMass R)
    (idealCharacterCellKernel P Q h ξ) (idealCharacterCellKernel R Q h ξ) phase
  calc
    _ = ∑ x, ∑ y, ((idealSelectedMass P x*idealSelectedMass R y : ℝ) : ℂ)*f x*g y*K x y := by
      simp only [idealFullCellPhaseAverage_eq_pairAverage, mul_sum]
      apply sum_congr rfl
      intro x _
      apply sum_congr rfl
      intro y _
      dsimp only [K, phase]
      rw [Complex.ofReal_mul]
      ring
    _ = ∑ d, ∑ e, ((idealSelectedMass P d*idealSelectedMass R e : ℝ) : ℂ)*phase d e*
        idealWeightedKernelTranspose (idealSelectedMass P) (idealCharacterCellKernel P Q h ξ) f d*
        idealWeightedKernelTranspose (idealSelectedMass R) (idealCharacterCellKernel R Q h ξ) g e :=
      idealKernelPairAverage_pairing _ _ _ _ phase f g
    _ = _ := by
      simp only [mul_sum, idealCharacterCellTranspose]
      apply sum_congr rfl
      intro d _
      apply sum_congr rfl
      intro e _
      dsimp only [phase]
      rw [Complex.ofReal_mul]
      ring

end
end ArtinMatthews

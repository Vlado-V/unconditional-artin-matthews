module

public import ArtinMatthews.IdealCharacterCellReproduction
public import ArtinMatthews.RationalPhasePrimitiveCharacters


set_option backward.privateInPublic true
@[expose] public section

/-! Exact reduced-rational phase averaging through the literal cell
kernels, with the actual primitive-conductor coefficients. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def idealRationalCellAverage (P : A → Finset ℕ) (R : B → Finset ℕ)
    (Q r : ℕ) (h ξ : ℝ) (u : ℤ) (x : IdealSelectedLabels P) (y : IdealSelectedLabels R) : ℂ :=
  ∑ d : IdealSelectedLabels P, ∑ e : IdealSelectedLabels R,
    (idealSelectedMass P d : ℂ) * idealCharacterCellKernel P Q h ξ d x *
      (idealSelectedMass R e : ℂ) * idealCharacterCellKernel R Q h ξ e y *
        (Real.fourierChar ((u : ℝ) * (idealSelectedProduct d : ℝ) *
          (idealSelectedProduct e : ℝ) / r) : ℂ)

theorem idealRationalCellAverage_eq (P : A → Finset ℕ) (R : B → Finset ℕ)
    {Q r : ℕ} [NeZero r] (hQr : r ≤ Q) (h ξ : ℝ) (u : ℤ)
    (hP : ∀ d : IdealSelectedLabels P, (idealSelectedProduct d).Coprime r)
    (hR : ∀ e : IdealSelectedLabels R, (idealSelectedProduct e).Coprime r)
    (x : IdealSelectedLabels P) (y : IdealSelectedLabels R) :
    idealRationalCellAverage P R Q r h ξ u x y =
      ∑ ψ : IdealPrimitiveCharacters Q,
        rationalPhasePrimitiveCoefficient hQr u ψ *
          idealCharacterCellApply P Q h ξ
            (fun d => idealPrimitiveCharacterValue ψ (idealSelectedProduct d)) x *
          idealCharacterCellApply R Q h ξ
            (fun e => idealPrimitiveCharacterValue ψ (idealSelectedProduct e)) y := by
  have hphase (d : IdealSelectedLabels P) (e : IdealSelectedLabels R) :=
    rationalPhase_bilinear_primitive_sum hQr u (idealSelectedProduct d) (idealSelectedProduct e)
      (hP d) (hR e)
  unfold idealRationalCellAverage
  simp_rw [hphase]
  simp only [mul_sum]
  calc
    _ = ∑ d : IdealSelectedLabels P, ∑ ψ : IdealPrimitiveCharacters Q,
        ∑ e : IdealSelectedLabels R,
          (idealSelectedMass P d : ℂ) * idealCharacterCellKernel P Q h ξ d x *
            (idealSelectedMass R e : ℂ) * idealCharacterCellKernel R Q h ξ e y *
              (rationalPhasePrimitiveCoefficient hQr u ψ *
                idealPrimitiveCharacterValue ψ (idealSelectedProduct d) *
                  idealPrimitiveCharacterValue ψ (idealSelectedProduct e)) := by
      apply sum_congr rfl
      intro d _
      rw [sum_comm]
    _ = ∑ ψ : IdealPrimitiveCharacters Q, ∑ d : IdealSelectedLabels P,
        ∑ e : IdealSelectedLabels R,
          (idealSelectedMass P d : ℂ) * idealCharacterCellKernel P Q h ξ d x *
            (idealSelectedMass R e : ℂ) * idealCharacterCellKernel R Q h ξ e y *
              (rationalPhasePrimitiveCoefficient hQr u ψ *
                idealPrimitiveCharacterValue ψ (idealSelectedProduct d) *
                  idealPrimitiveCharacterValue ψ (idealSelectedProduct e)) := by rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro ψ _
      simp only [idealCharacterCellApply, mul_sum, sum_mul]
      conv_rhs => rw [sum_comm]
      apply sum_congr rfl
      intro d _
      apply sum_congr rfl
      intro e _
      ring

end
end ArtinMatthews

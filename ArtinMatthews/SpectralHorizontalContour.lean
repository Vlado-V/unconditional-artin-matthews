module

public import ArtinMatthews.SourceContourHeightWeight


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Complex
noncomputable section

theorem spectral_horizontal_integral_eq_of_heightWeight (f : ℂ → ℂ) {B C : ℝ}
    (hB : 0 ≤ B)
    (hhol : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ B → DifferentiableAt ℂ f z)
    (hbound : ∀ t y : ℝ, 0 ≤ y → y ≤ B →
      ‖f ((t : ℂ) + (y : ℂ) * I)‖ ≤ C * SourcePhysical.sourceContourHeightWeight t) :
    (∫ t : ℝ, f (t : ℂ)) = ∫ t : ℝ, f ((t : ℂ) + (B : ℂ) * I) := by
  let F : ℂ → ℂ := fun z => f (I * z)
  have hrotate (x y : ℝ) : I * ((x : ℂ) + (y : ℂ) * I) =
      ((-y : ℝ) : ℂ) + (x : ℂ) * I := by
    push_cast
    ring_nf
    simp only [Complex.I_sq, neg_mul, one_mul]
    ring
  have hd : DifferentiableOn ℂ F {z : ℂ | 0 ≤ z.re ∧ z.re ≤ B} := by
    intro z hz
    have hh := hhol (I * z)
      (by simpa [Complex.mul_im] using hz.1)
      (by simpa [Complex.mul_im] using hz.2)
    exact (hh.comp z ((hasDerivAt_id z).const_mul I).differentiableAt).differentiableWithinAt
  have hb (x : ℝ) (hx : x ∈ Icc 0 B) (y : ℝ) :
      ‖F ((x : ℂ) + (y : ℂ) * I)‖ ≤ C * SourcePhysical.sourceContourHeightWeight y := by
    dsimp only [F]
    rw [hrotate]
    simpa only [SourcePhysical.sourceContourHeightWeight_neg] using hbound (-y) x hx.1 hx.2
  have heq := SourcePhysical.source_vertical_integral_eq_of_heightWeight F hB hd hb
  have hl : (fun y : ℝ => F ((0 : ℝ) + y * I)) = (fun y : ℝ => f ((-y : ℝ) : ℂ)) := by
    funext y
    dsimp only [F]
    rw [hrotate]
    simp
  have hr : (fun y : ℝ => F ((B : ℂ) + y * I)) =
      (fun y : ℝ => f (((-y : ℝ) : ℂ) + (B : ℂ) * I)) := by
    funext y
    dsimp only [F]
    exact congrArg f (hrotate B y)
  rw [hl, hr] at heq
  calc
    _ = ∫ y : ℝ, f ((-y : ℝ) : ℂ) :=
      (integral_neg_eq_self (fun y : ℝ => f (y : ℂ)) volume).symm
    _ = ∫ y : ℝ, f (((-y : ℝ) : ℂ) + (B : ℂ) * I) := heq
    _ = _ := integral_neg_eq_self (fun y : ℝ => f ((y : ℂ) + (B : ℂ) * I)) volume

end
end ArtinMatthews

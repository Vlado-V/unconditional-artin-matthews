module

public import ArtinMatthews.SpectralGamma0EllipticCoordinates


set_option backward.privateInPublic true
@[expose] public section

/-! A genuinely bounded inverse-height-square multiplier, agreeing with the
Euclidean forcing coefficient on every chart above the chosen positive height. -/

noncomputable section
open Set

namespace ArtinMatthews

def spectralEllipticInverseHeight (a : ℝ) (x : Fin 2 → ℝ) : ℝ :=
  1 / (max a (x 1))^2

theorem spectralEllipticInverseHeight_continuous {a : ℝ} (ha : 0 < a) :
    Continuous (spectralEllipticInverseHeight a) :=
  continuous_const.div ((continuous_const.max (continuous_apply 1)).pow 2)
    (fun x => ne_of_gt (sq_pos_of_pos (ha.trans_le (le_max_left a (x 1)))))

theorem spectralEllipticInverseHeight_nonneg (a : ℝ) (x : Fin 2 → ℝ) :
    0 ≤ spectralEllipticInverseHeight a x := by
  unfold spectralEllipticInverseHeight
  positivity

theorem spectralEllipticInverseHeight_bound {a : ℝ} (ha : 0 < a) (x : Fin 2 → ℝ) :
    |spectralEllipticInverseHeight a x| ≤ 1/a^2 := by
  rw [abs_of_nonneg (spectralEllipticInverseHeight_nonneg a x)]
  exact one_div_le_one_div_of_le (sq_pos_of_pos ha)
    ((sq_le_sq₀ ha.le (ha.le.trans (le_max_left a (x 1)))).mpr (le_max_left a (x 1)))

theorem spectralEllipticInverseHeight_eq {a : ℝ} {x : Fin 2 → ℝ} (hx : a ≤ x 1) :
    spectralEllipticInverseHeight a x = 1/(x 1)^2 := by
  simp only [spectralEllipticInverseHeight,max_eq_right hx]

end ArtinMatthews

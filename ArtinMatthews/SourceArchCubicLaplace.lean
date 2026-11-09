module

public import ArtinMatthews.SourceArchJacquetLaplace
public import ArtinMatthews.SourceThetaBesselSchlafli


set_option backward.privateInPublic true
@[expose] public section

/-! The exact scaling from the two-dimensional Gaussian Laplace
integral to the cubic Bessel integral. -/
namespace ArtinMatthews.SourceArchJacquet

open MeasureTheory Set OAI.CubicEisenstein
noncomputable section

theorem sourceArchCubicLaplace_change {r : ℝ} (hr : 0 < r) :
    r ^ (4 / 3 : ℝ) * (∫ t in Ioi 0, t ^ (-(2 / 3 : ℝ)) *
      Real.exp (-(r ^ 2 * t) - (4 * Real.pi ^ 2) / t)) =
    r ^ (2 / 3 : ℝ) * ∫ t in Ioi 0, cubicBesselDensity (4 * Real.pi * r) t := by
  have hsqpow (a : ℝ) : (r ^ 2) ^ a = r ^ (2 * a) := by
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
    norm_num
  have hd : (∫ t in Ioi 0, cubicBesselDensity (4 * Real.pi * r) (r ^ 2 * t)) =
      ∫ t in Ioi 0, r ^ (-(4 / 3 : ℝ)) *
        (t ^ (-(2 / 3 : ℝ)) * Real.exp (-(r ^ 2 * t) - (4 * Real.pi ^ 2) / t)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    unfold cubicBesselDensity
    rw [Real.mul_rpow (sq_nonneg r) ht.le]
    rw [hsqpow, show (2 : ℝ) * (-2 / 3) = -(4 / 3) by norm_num]
    have hphase : (4 * Real.pi * r) ^ 2 / (4 * (r ^ 2 * t)) =
        (4 * Real.pi ^ 2) / t := by
      field_simp [hr.ne', ne_of_gt (show 0 < t from ht)]
    rw [hphase]
    norm_num
    ring
  have hchange := integral_comp_mul_left_Ioi (cubicBesselDensity (4 * Real.pi * r)) 0
    (sq_pos_of_pos hr)
  rw [hd, integral_const_mul, mul_zero, smul_eq_mul] at hchange
  have hinv : (r ^ 2)⁻¹ = r ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_neg_one, hsqpow]
    norm_num
  rw [hinv] at hchange
  have h := congrArg (fun a : ℝ => r ^ (8 / 3 : ℝ) * a) hchange
  simpa only [← mul_assoc, ← Real.rpow_add hr, show (8 / 3 : ℝ) + -(4 / 3) = 4 / 3 by norm_num,
    show (8 / 3 : ℝ) + -2 = 2 / 3 by norm_num] using h

def sourceArchJacquetConstant : ℝ :=
  4 * Real.pi * (2 * Real.pi) ^ (1 / 3 : ℝ) / Real.Gamma (4 / 3)

theorem sourceArchJacquetConstant_pos : 0 < sourceArchJacquetConstant := by
  unfold sourceArchJacquetConstant
  exact div_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos)
    (Real.rpow_pos_of_pos (mul_pos (by norm_num) Real.pi_pos) _))
    (Real.Gamma_pos_of_pos (by norm_num))

theorem sourceArchJacquetConstant_ne_zero : sourceArchJacquetConstant ≠ 0 :=
  sourceArchJacquetConstant_pos.ne'

theorem sourceArchCubicLaplace_bessel {r : ℝ} (hr : 0 < r) :
    ((r ^ (4 / 3 : ℝ) * (2 * Real.pi) *
        ∫ t in Ioi 0, t ^ (-(2 / 3 : ℝ)) *
          Real.exp (-(r ^ 2 * t) - (4 * Real.pi ^ 2) / t) : ℝ) : ℂ) =
    (Real.Gamma (4 / 3) * sourceArchJacquetConstant * r : ℝ) *
      schlafliBesselK (1 / 3 : ℂ) (4 * Real.pi * r) := by
  have hc : 0 < 2 * Real.pi := by positivity
  have hx : 0 < 4 * Real.pi * r := by positivity
  rw [schlafliBesselK_cubic_real _ hx, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  rw [show r ^ (4 / 3 : ℝ) * (2 * Real.pi) *
      (∫ t in Ioi 0, t ^ (-(2 / 3 : ℝ)) *
        Real.exp (-(r ^ 2 * t) - (4 * Real.pi ^ 2) / t)) =
      (2 * Real.pi) * (r ^ (4 / 3 : ℝ) *
        ∫ t in Ioi 0, t ^ (-(2 / 3 : ℝ)) *
          Real.exp (-(r ^ 2 * t) - (4 * Real.pi ^ 2) / t)) by ring]
  rw [sourceArchCubicLaplace_change hr,
    show 4 * Real.pi * r / 2 = (2 * Real.pi) * r by ring,
    Real.mul_rpow hc.le hr.le]
  have hcancel : (2 * Real.pi) ^ (1 / 3 : ℝ) * (2 * Real.pi) ^ (-(1 / 3 : ℝ)) = 1 := by
    rw [← Real.rpow_add hc]
    norm_num
  have hrpower : r * r ^ (-(1 / 3 : ℝ)) = r ^ (2 / 3 : ℝ) := by
    calc
      _ = r ^ (1 : ℝ) * r ^ (-(1 / 3 : ℝ)) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hr]; norm_num
  have hg : Real.Gamma (4 / 3) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  calc
    _ = (2 * Real.pi) * (r * r ^ (-(1 / 3 : ℝ))) *
        ((2 * Real.pi) ^ (1 / 3 : ℝ) * (2 * Real.pi) ^ (-(1 / 3 : ℝ))) *
        ∫ t in Ioi 0, cubicBesselDensity (4 * Real.pi * r) t := by
      rw [hcancel, hrpower, mul_one]
      ring
    _ = _ := by
      unfold sourceArchJacquetConstant
      field_simp [hg]
      ring

end
end ArtinMatthews.SourceArchJacquet

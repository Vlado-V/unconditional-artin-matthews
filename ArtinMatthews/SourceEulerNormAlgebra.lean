module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Ring


set_option backward.privateInPublic true
@[expose] public section

/-! Exact real-power algebra for the honest coarse global Gauss bound. -/
namespace ArtinMatthews.SourceEulerAssembly

theorem sourceEuler_sqrt_power (q x : ℝ) (hq : 0 < q) :
    Real.sqrt q * q * q ^ (-(1 / 2 : ℝ) - x) = q ^ (1 - x) := by
  calc
    _ = (q ^ (1 / 2 : ℝ) * q ^ (1 : ℝ)) * q ^ (-(1 / 2 : ℝ) - x) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_one]
    _ = q ^ ((1 / 2 : ℝ) + 1 + (-(1 / 2 : ℝ) - x)) := by
      rw [← Real.rpow_add hq, ← Real.rpow_add hq]
    _ = q ^ (1 - x) := by congr 1; ring

theorem sourceEuler_cube_power (q x : ℝ) (hq : 0 < q) :
    q ^ (3 : ℕ) * q ^ (-1 - 3 * x) = q ^ (2 - 3 * x) := by
  rw [← Real.rpow_natCast q 3, ← Real.rpow_add hq]
  congr 1
  norm_num
  ring

theorem sourceEuler_linear_power (q x : ℝ) (hq : 0 < q) :
    q * q ^ (-x) = q ^ (1 - x) := by
  calc
    _ = q ^ (1 : ℝ) * q ^ (-x) := by rw [Real.rpow_one]
    _ = q ^ (1 + -x) := (Real.rpow_add hq _ _).symm
    _ = q ^ (1 - x) := by rw [sub_eq_add_neg]

theorem sourceEulerCoarseMajorant_algebra (qc qn qs qr x w z : ℝ)
    (hc : 0 < qc) (hn : 0 < qn) (hs : 0 < qs) :
    Real.sqrt qc * (qs * (qc * qn ^ (3 : ℕ))) * qc ^ (-(1 / 2 : ℝ) - x) *
        qn ^ (-1 - 3 * x) * qs ^ (-w) * qr ^ (-6 * z) =
      qc ^ (1 - x) * (qn ^ (2 - 3 * x) * (qs ^ (1 - w) * qr ^ (-6 * z))) := by
  calc
    _ = (Real.sqrt qc * qc * qc ^ (-(1 / 2 : ℝ) - x)) *
      ((qn ^ (3 : ℕ) * qn ^ (-1 - 3 * x)) *
        ((qs * qs ^ (-w)) * qr ^ (-6 * z))) := by ring
    _ = _ := by rw [sourceEuler_sqrt_power qc x hc,
      sourceEuler_cube_power qn x hn, sourceEuler_linear_power qs w hs]

end ArtinMatthews.SourceEulerAssembly

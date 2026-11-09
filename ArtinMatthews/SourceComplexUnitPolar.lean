module

public import ArtinMatthews.SourceCircleHaar
public import Mathlib.Topology.Algebra.Group.Units


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open MeasureTheory Set
open scoped ENNReal Real
noncomputable section

def sourceComplexUnitLogNorm (z : ℂˣ) : ℝ := 2 * Real.log ‖(z : ℂ)‖

def sourceComplexUnitAngle (z : ℂˣ) : Circle :=
  ⟨(z : ℂ) / (‖(z : ℂ)‖ : ℂ), by
    rw [show ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ∈ Submonoid.unitSphere ℂ ↔
      ‖(z : ℂ) / (‖(z : ℂ)‖ : ℂ)‖ = 1 from mem_sphere_zero_iff_norm,
      norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr z.ne_zero)]⟩

def sourceComplexRadialUnit (t : ℝ) : ℂˣ :=
  Units.mk0 (Real.exp (t / 2) : ℂ) (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))

theorem sourceComplexRadialUnit_add (s t : ℝ) :
    sourceComplexRadialUnit (s + t) = sourceComplexRadialUnit s * sourceComplexRadialUnit t := by
  apply Units.ext
  change (Real.exp ((s + t) / 2) : ℂ) = (Real.exp (s / 2) : ℂ) * (Real.exp (t / 2) : ℂ)
  rw [add_div, Real.exp_add, Complex.ofReal_mul]

theorem sourceComplexRadialUnit_mul_angle_norm (θ : Circle) (t : ℝ) :
    ‖((sourceComplexRadialUnit t * Circle.toUnits θ : ℂˣ) : ℂ)‖ = Real.exp (t / 2) := by
  change ‖(Real.exp (t / 2) : ℂ) * (θ : ℂ)‖ = _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Circle.norm_coe, mul_one]

theorem sourceComplexRadialUnit_mul_angle_logNorm (θ : Circle) (t : ℝ) :
    sourceComplexUnitLogNorm (sourceComplexRadialUnit t * Circle.toUnits θ) = t := by
  rw [sourceComplexUnitLogNorm, sourceComplexRadialUnit_mul_angle_norm, Real.log_exp]
  ring

theorem sourceComplexRadialUnit_mul_angle_angle (θ : Circle) (t : ℝ) :
    sourceComplexUnitAngle (sourceComplexRadialUnit t * Circle.toUnits θ) = θ := by
  apply Subtype.ext
  change ((Real.exp (t / 2) : ℂ) * (θ : ℂ)) /
    (‖((sourceComplexRadialUnit t * Circle.toUnits θ : ℂˣ) : ℂ)‖ : ℂ) = (θ : ℂ)
  rw [sourceComplexRadialUnit_mul_angle_norm, mul_comm, mul_div_cancel_right₀]
  exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)

theorem sourceComplexUnit_angle_reconstruct (z : ℂˣ) :
    sourceComplexRadialUnit (sourceComplexUnitLogNorm z) * Circle.toUnits (sourceComplexUnitAngle z) = z := by
  apply Units.ext
  change (Real.exp ((2 * Real.log ‖(z : ℂ)‖) / 2) : ℂ) *
    ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) = (z : ℂ)
  rw [show (2 * Real.log ‖(z : ℂ)‖) / 2 = Real.log ‖(z : ℂ)‖ by ring,
    Real.exp_log (norm_pos_iff.mpr z.ne_zero)]
  rw [mul_comm, div_mul_cancel₀]
  exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr z.ne_zero)

/-- Exact local product coordinates: unnormalized angle and log squared norm. -/
def sourceComplexUnitPolarMulEquiv : Circle × Multiplicative ℝ ≃* ℂˣ where
  toFun p := sourceComplexRadialUnit p.2.toAdd * Circle.toUnits p.1
  invFun z := (sourceComplexUnitAngle z, Multiplicative.ofAdd (sourceComplexUnitLogNorm z))
  left_inv p := Prod.ext (sourceComplexRadialUnit_mul_angle_angle p.1 p.2.toAdd)
    (congrArg Multiplicative.ofAdd (sourceComplexRadialUnit_mul_angle_logNorm p.1 p.2.toAdd))
  right_inv := sourceComplexUnit_angle_reconstruct
  map_mul' p q := by
    change sourceComplexRadialUnit (p.2.toAdd + q.2.toAdd) * Circle.toUnits (p.1 * q.1) = _
    rw [sourceComplexRadialUnit_add, map_mul]
    ac_rfl

end
end ArtinMatthews.SourcePhysical

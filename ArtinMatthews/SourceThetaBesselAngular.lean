module

public import ArtinMatthews.SourceThetaBesselDerivatives
public import ArtinMatthews.SourceComplexUnitPolarHomeomorph
public import Mathlib.Topology.Algebra.GroupWithZero


set_option backward.privateInPublic true
@[expose] public section

/-! The concrete angular types used in source03. Their radial
derivatives retain the genuine cubic Bessel profile. -/
namespace ArtinMatthews.SourceReflection

open ArtinMatthews.SourcePhysical
open scoped ContDiff
noncomputable section

def sourceThetaBesselAngularLogDerivative (c : ℝ) (m : ℤ) (n : ℕ) (θ : Circle) (x : ℝ) : ℂ :=
  (θ : ℂ) ^ m * sourceThetaBesselLogDerivative c n x

theorem sourceThetaBesselAngularLogDerivative_hasDerivAt {c : ℝ} (hc : 0 < c)
    (m : ℤ) (n : ℕ) (θ : Circle) (x : ℝ) :
    HasDerivAt (sourceThetaBesselAngularLogDerivative c m n θ)
      (sourceThetaBesselAngularLogDerivative c m (n + 1) θ x) x :=
  (sourceThetaBesselLogDerivative_hasDerivAt hc n x).const_mul _

theorem sourceThetaBesselAngularLogDerivative_measurable {c : ℝ} (hc : 0 < c) (m : ℤ) (n : ℕ) :
    Measurable (Function.uncurry (sourceThetaBesselAngularLogDerivative c m n)) := by
  have hD : Continuous (sourceThetaBesselLogDerivative c n) :=
    continuous_iff_continuousAt.mpr fun x => (sourceThetaBesselLogDerivative_hasDerivAt hc n x).continuousAt
  apply Continuous.measurable
  have hθ : Continuous (fun θ : Circle => (θ : ℂ) ^ m) :=
    (continuous_subtype_val : Continuous (fun θ : Circle => (θ : ℂ))).zpow₀ m
      (fun θ => Or.inl (Circle.coe_ne_zero θ))
  exact (hθ.comp continuous_fst).mul (hD.comp continuous_snd)

theorem sourceThetaBesselAngularLogDerivative_twoEnded {c : ℝ} (hc : 0 < c) (m : ℤ) (n : ℕ)
    {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ x, ‖sourceThetaBesselAngularLogDerivative c m n θ x‖ ≤
      C * min (Real.exp ((5 / 6 : ℝ) * x)) (Real.exp (-A * x)) := by
  obtain ⟨C, hC, hb⟩ := sourceThetaBesselLogDerivative_twoEnded hc n hA
  refine ⟨C, hC, fun θ x => ?_⟩
  simpa only [sourceThetaBesselAngularLogDerivative, norm_mul, norm_zpow, Circle.norm_coe, one_zpow,
    one_mul] using hb x

theorem sourceThetaBesselAngularLogDerivative_twoEnded_of_le {c : ℝ} (hc : 0 < c) (m : ℤ) (n : ℕ)
    {δ A : ℝ} (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 5 / 6) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ x, ‖sourceThetaBesselAngularLogDerivative c m n θ x‖ ≤
      C * min (Real.exp (δ * x)) (Real.exp (-A * x)) := by
  obtain ⟨C, hC, hb⟩ := sourceThetaBesselAngularLogDerivative_twoEnded hc m n hA
  refine ⟨C, hC, fun θ x => (hb θ x).trans (mul_le_mul_of_nonneg_left ?_ hC)⟩
  apply le_min
  · rcases le_total x 0 with hx | hx
    · exact (min_le_left _ _).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hδ₁ hx))
    · exact (min_le_right _ _).trans (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (by linarith) hx))
  · exact min_le_right _ _

/-- The literal normalized complex-place local factor in the source. -/
def sourceThetaBesselComplexFactor (c : ℝ) (m : ℤ) (z : ℂˣ) : ℂ :=
  (sourceComplexUnitAngle z : ℂ) ^ m * sourceThetaBesselProfile c (‖(z : ℂ)‖ ^ 2)

theorem sourceThetaBesselComplexFactor_eq_log {c : ℝ} (hc : 0 < c) (m : ℤ) (z : ℂˣ) :
    sourceThetaBesselComplexFactor c m z =
      sourceThetaBesselAngularLogDerivative c m 0 (sourceComplexUnitAngle z) (sourceComplexUnitLogNorm z) := by
  have hz : Real.exp (sourceComplexUnitLogNorm z) = ‖(z : ℂ)‖ ^ 2 := by
    rw [sourceComplexUnitLogNorm, show (2 : ℝ) = ((2 : ℕ) : ℝ) from rfl,
      Real.exp_nat_mul, Real.exp_log (norm_pos_iff.mpr z.ne_zero)]
  rw [sourceThetaBesselAngularLogDerivative, sourceThetaBesselLogDerivative_zero hc, hz,
    sourceThetaBesselComplexFactor]

end
end ArtinMatthews.SourceReflection

module

public import ArtinMatthews.SourceThetaSchlafliMoments
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

/-! The log derivative of each genuine Schläfli moment is a two-term
recurrence. Its differentiated integrand has a local Gamma majorant. -/
namespace ArtinMatthews.SourceReflection

open MeasureTheory Set Filter
open scoped Topology
noncomputable section

private theorem thetaSchlafli_phase_hasDerivAt (scale x z : ℝ) :
    HasDerivAt (fun t => sourceThetaSchlafliPhase scale t z) (sourceThetaSchlafliPhase scale x z) x :=
  ((Real.hasDerivAt_exp x).const_mul scale).div_const z

theorem sourceThetaSchlafliMomentIntegrand_hasDerivAt (scale : ℝ) (k : ℕ) (x z : ℝ) :
    HasDerivAt (fun t => sourceThetaSchlafliMomentIntegrand scale k t z)
      (((5 / 6 : ℝ) + k) * sourceThetaSchlafliMomentIntegrand scale k x z -
        sourceThetaSchlafliMomentIntegrand scale (k + 1) x z) x := by
  let y (t : ℝ) := sourceThetaSchlafliPhase scale t z
  have hy : HasDerivAt y (y x) x := thetaSchlafli_phase_hasDerivAt scale x z
  have hp : HasDerivAt (fun t => y t ^ k) ((k : ℝ) * y x ^ k) x := by
    have he : (k : ℝ) * y x ^ (k - 1) * y x = (k : ℝ) * y x ^ k := by
      cases k with
      | zero => simp
      | succ j => simp [pow_succ, mul_assoc]
    exact he ▸ hy.pow k
  have hs : HasDerivAt (fun t => -z - y t) (-(y x)) x := by
    simpa only [Pi.sub_apply] using! hy.const_sub (-z)
  have hExp := (Real.hasDerivAt_exp (-z - y x)).comp x hs
  have hEnv := (Real.hasDerivAt_exp ((5 / 6 : ℝ) * x)).comp x
    ((hasDerivAt_id x).const_mul (5 / 6 : ℝ))
  have h := hEnv.mul ((hasDerivAt_const x (z ^ (-(2 / 3 : ℝ)))).mul (hp.mul hExp))
  convert! h using 1
  dsimp only [sourceThetaSchlafliMomentIntegrand, y, Function.comp_def, Pi.mul_apply]
  rw [pow_succ]
  ring

theorem sourceThetaSchlafliMoment_hasDerivAt {scale : ℝ} (hscale : 0 < scale) (k : ℕ) (x : ℝ) :
    HasDerivAt (sourceThetaSchlafliMoment scale k)
      (((5 / 6 : ℝ) + k) * sourceThetaSchlafliMoment scale k x -
        sourceThetaSchlafliMoment scale (k + 1) x) x := by
  let F := sourceThetaSchlafliMomentIntegrand scale k
  let G := sourceThetaSchlafliMomentIntegrand scale (k + 1)
  let c := (5 / 6 : ℝ) + k
  let F' (t z : ℝ) := c * F t z - G t z
  let D := (c * (k.factorial : ℝ) + ((k + 1).factorial : ℝ)) * Real.exp ((5 / 6 : ℝ) * (x + 1))
  let B (z : ℝ) := D * sourceThetaSchlafliGammaDensity 0 z
  let μ₀ := (volume : Measure ℝ).restrict (Ioi 0)
  have hF (t : ℝ) : Integrable (F t) μ₀ := sourceThetaSchlafliMomentIntegrand_integrable hscale k t
  have hG (t : ℝ) : Integrable (G t) μ₀ := sourceThetaSchlafliMomentIntegrand_integrable hscale (k + 1) t
  have hFm (t : ℝ) : Measurable (F t) := sourceThetaSchlafliMomentIntegrand_measurable scale k t
  have hGm (t : ℝ) : Measurable (G t) := sourceThetaSchlafliMomentIntegrand_measurable scale (k + 1) t
  have hF'm : Measurable (F' x) := ((hFm x).const_mul c).sub (hGm x)
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hB : Integrable B μ₀ := (sourceThetaSchlafliGammaDensity_integrable 0).const_mul D
  have hdom : ∀ᵐ z ∂μ₀, ∀ t ∈ Metric.ball x 1, ‖F' t z‖ ≤ B z := by
    filter_upwards [ae_restrict_mem (μ := volume) (s := Ioi (0 : ℝ)) measurableSet_Ioi] with z hz
    intro t ht
    have htz : 0 < z := hz
    have hdist : |t - x| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using ht
    have htx : t ≤ x + 1 := by linarith [(abs_lt.mp hdist).2]
    have hExp : Real.exp ((5 / 6 : ℝ) * t) ≤ Real.exp ((5 / 6 : ℝ) * (x + 1)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htx (by norm_num))
    have hDens : 0 ≤ sourceThetaSchlafliGammaDensity 0 z :=
      mul_nonneg (Real.rpow_nonneg htz.le _) (Real.exp_pos _).le
    have hK (j : ℕ) : sourceThetaSchlafliMomentIntegrand scale j t z ≤
        ((j.factorial : ℝ) * Real.exp ((5 / 6 : ℝ) * (x + 1))) * sourceThetaSchlafliGammaDensity 0 z := by
      have h := sourceThetaSchlafliMomentIntegrand_le hscale htz j 0 t
      have h₁ : sourceThetaSchlafliMomentIntegrand scale j t z ≤
          ((j.factorial : ℝ) * Real.exp ((5 / 6 : ℝ) * t)) * sourceThetaSchlafliGammaDensity 0 z := by
        simpa using h
      exact h₁.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hExp (Nat.cast_nonneg _)) hDens)
    have hF₀ : 0 ≤ F t z := (sourceThetaSchlafliMomentIntegrand_pos hscale htz k t).le
    have hG₀ : 0 ≤ G t z := (sourceThetaSchlafliMomentIntegrand_pos hscale htz (k + 1) t).le
    change ‖c * F t z - G t z‖ ≤ B z
    rw [Real.norm_eq_abs]
    calc
      _ ≤ |c * F t z| + |G t z| := abs_sub _ _
      _ = c * F t z + G t z := by rw [abs_of_nonneg (mul_nonneg hc hF₀), abs_of_nonneg hG₀]
      _ ≤ c * (((k.factorial : ℝ) * Real.exp ((5 / 6 : ℝ) * (x + 1))) *
          sourceThetaSchlafliGammaDensity 0 z) +
          (((k + 1).factorial : ℝ) * Real.exp ((5 / 6 : ℝ) * (x + 1))) *
            sourceThetaSchlafliGammaDensity 0 z :=
        add_le_add (mul_le_mul_of_nonneg_left (hK k) hc) (hK (k + 1))
      _ = B z := by dsimp only [B, D]; ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ₀) (F := F) (F' := F') (bound := B)
    (Metric.ball_mem_nhds x zero_lt_one) (Eventually.of_forall fun t => (hFm t).aestronglyMeasurable)
    (hF x) hF'm.aestronglyMeasurable hdom hB (Eventually.of_forall fun z t _ =>
      sourceThetaSchlafliMomentIntegrand_hasDerivAt scale k t z)
  have heq : (∫ z, F' x z ∂μ₀) = c * sourceThetaSchlafliMoment scale k x -
      sourceThetaSchlafliMoment scale (k + 1) x := by
    dsimp only [F']
    rw [integral_sub ((hF x).const_mul c) (hG x), integral_const_mul]
    rfl
  exact heq ▸ h.2

end
end ArtinMatthews.SourceReflection

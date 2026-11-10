module

public import ArtinMatthews.SourceSheetProfile
public import ArtinMatthews.SourceComplexMellinSchwartz
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open MeasureTheory Set Filter
open ArtinMatthews.VaryingKummerAnalytic
open scoped SchwartzMap ENNReal Topology
noncomputable section

variable {Y : Type*}

theorem sourceSheetComplexCoordinate_hasDerivAt (N : Y → ℝ) (t : ℝ) (θ : Circle) (y : Y) :
    HasDerivAt (fun u : ℝ => sourceSheetComplexCoordinate N u θ y)
      ((1 / 2 : ℝ) • sourceSheetComplexCoordinate N t θ y) t := by
  have harg := ((hasDerivAt_id t).sub_const (Real.log (N y))).div_const 2
  have h := ((Real.hasDerivAt_exp ((t - Real.log (N y)) / 2)).comp t harg).smul_const (θ : ℂ)
  have he (u : ℝ) : sourceSheetComplexCoordinate N u θ y =
      Real.exp ((u - Real.log (N y)) / 2) • (θ : ℂ) := by
    rw [sourceSheetComplexCoordinate, Complex.real_smul]
  simp only [he, smul_smul]
  simpa only [id_eq, Function.comp_def, mul_comm (1 / 2 : ℝ)] using h

variable [MeasurableSpace Y]

omit [MeasurableSpace Y] in
theorem sourceSheetProfileIntegrand_hasDerivAt (N : Y → ℝ)
    (g : 𝓢(ℂ, ℂ)) (G : Y → ℂ) (t : ℝ) (p : Circle × Y) :
    HasDerivAt (fun u => sourceSheetProfileIntegrand N g G u p)
      ((1 / 2 : ℝ) • sourceSheetProfileIntegrand N (sourceComplexEulerSchwartz g) G t p) t := by
  let z := sourceSheetComplexCoordinate N t p.1 p.2
  have h := (g.differentiable z).hasFDerivAt.comp_hasDerivAt t
    (sourceSheetComplexCoordinate_hasDerivAt N t p.1 p.2)
  simpa only [sourceSheetProfileIntegrand, Function.comp_apply,
    sourceComplexEulerSchwartz_apply, map_smul, smul_mul_assoc, z] using h.mul_const (G p.2)

/-- The actual sheet is differentiable; the derivative is the sheet for the Euler
derivative of its one chosen complex factor, with the exact one-half. -/
theorem sourceSheetLogProfile_hasDerivAt (ν : Measure Y) [SFinite ν]
    (N : Y → ℝ) (hN : ∀ y, 0 < N y) (hNm : Measurable N)
    (g : 𝓢(ℂ, ℂ)) (G : Y → ℂ) (hG : Measurable G) (σ : ℝ) (hσ : 0 < σ)
    (hInt : Integrable (fun y => ‖G y‖ * (N y) ^ σ) ν) (t : ℝ) :
    HasDerivAt (sourceSheetLogProfile ν N g G)
      ((1 / 2 : ℝ) • sourceSheetLogProfile ν N (sourceComplexEulerSchwartz g) G t) t := by
  let E := sourceComplexEulerSchwartz g
  obtain ⟨C,hC,hb⟩ := sourceSheetProfileIntegrand_norm_le N hN E G σ hσ
  let B : Circle × Y → ℝ := fun p => ((1 / 2 : ℝ) * (C * Real.exp (-σ * (t - 1)))) *
    (‖G p.2‖ * (N p.2) ^ σ)
  have hB : Integrable B (sourceCircleHaar.prod ν) := (hInt.comp_snd sourceCircleHaar).const_mul _
  have hI := (sourceSheetLogProfile_integrable_and_bound ν N hN hNm g G hG σ hσ hInt).1 t
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := sourceCircleHaar.prod ν) (F := sourceSheetProfileIntegrand N g G)
    (F' := fun u p => (1 / 2 : ℝ) • sourceSheetProfileIntegrand N E G u p)
    (bound := B) (Ioi_mem_nhds (show t - 1 < t by linarith))
    (Eventually.of_forall fun u =>
      (sourceSheetProfileIntegrand_measurable N hNm g G hG u).aestronglyMeasurable)
    hI ((sourceSheetProfileIntegrand_measurable N hNm E G hG t).const_smul
      (1 / 2 : ℝ)).aestronglyMeasurable
    (Eventually.of_forall fun p u hu => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
      have he : Real.exp (-σ * u) ≤ Real.exp (-σ * (t - 1)) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonpos_left (le_of_lt hu) (by linarith)
      calc
        _ ≤ (1 / 2 : ℝ) * ((C * Real.exp (-σ * u)) * (‖G p.2‖ * N p.2 ^ σ)) :=
          mul_le_mul_of_nonneg_left (hb u p) (by norm_num)
        _ ≤ B p := by
          dsimp [B]
          rw [← mul_assoc]
          gcongr
          exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hN p.2).le _))
    hB (Eventually.of_forall fun p u _ => sourceSheetProfileIntegrand_hasDerivAt N g G u p)
  unfold sourceSheetLogProfile
  rw [← integral_smul]
  exact h.2

end
end ArtinMatthews.SourcePhysical

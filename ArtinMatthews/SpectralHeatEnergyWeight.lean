module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecificLimits.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! The exact energy weight contributed by a pair of Gaussian native
tests, including complementary and residual energies. -/

noncomputable section
open Filter
open scoped Topology
namespace ArtinMatthews

def spectralHeatEnergyWeight (R eig : ℝ) : ℂ :=
  Complex.exp (2*(1/4-(eig : ℂ))/(R : ℂ)^2)

theorem spectralHeatEnergyWeight_real (R eig : ℝ) :
    spectralHeatEnergyWeight R eig = (Real.exp (2*(1/4-eig)/R^2) : ℂ) := by
  rw [spectralHeatEnergyWeight,Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem spectralHeatEnergyWeight_star (R eig : ℝ) :
    star (spectralHeatEnergyWeight R eig) = spectralHeatEnergyWeight R eig := by
  rw [spectralHeatEnergyWeight_real]
  exact Complex.conj_ofReal _

theorem spectralHeatEnergyWeight_product (R eig : ℝ) :
    Complex.exp ((1/4-(eig : ℂ))/(R : ℂ)^2)*
      star (Complex.exp ((1/4-(eig : ℂ))/(R : ℂ)^2)) = spectralHeatEnergyWeight R eig := by
  have hs : star (Complex.exp ((1/4-(eig : ℂ))/(R : ℂ)^2)) =
      Complex.exp ((1/4-(eig : ℂ))/(R : ℂ)^2) := by
    have hr : (1/4-(eig : ℂ))/(R : ℂ)^2 = (((1/4-eig)/R^2 : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hr,← Complex.ofReal_exp]
    exact Complex.conj_ofReal _
  rw [hs,← Complex.exp_add,spectralHeatEnergyWeight]
  congr 1
  ring

theorem spectralHeatEnergyWeight_principal (R t : ℝ) :
    spectralHeatEnergyWeight R (1/4+t^2) = Complex.exp (-2*((t : ℂ)/(R : ℂ))^2) := by
  unfold spectralHeatEnergyWeight
  congr 1
  push_cast
  rw [div_pow]
  ring

theorem spectralHeatEnergyWeight_norm_le {R eig : ℝ} (hR : 1 ≤ R) (heig : 0 ≤ eig) :
    ‖spectralHeatEnergyWeight R eig‖ ≤ Real.exp (1/2 : ℝ) := by
  rw [spectralHeatEnergyWeight_real,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hR2 : 1 ≤ R^2 := one_le_pow₀ hR
  apply (div_le_iff₀ (sq_pos_of_pos hR0)).mpr
  nlinarith

theorem spectralHeatEnergyWeight_principal_norm_le (R eig : ℝ) (heig : 1/4 ≤ eig) :
    ‖spectralHeatEnergyWeight R eig‖ ≤ 1 := by
  rw [spectralHeatEnergyWeight_real,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg R)

theorem spectralHeatEnergyWeight_tendsto (eig : ℝ) :
    Tendsto (fun R : ℝ => spectralHeatEnergyWeight R eig) atTop (𝓝 1) := by
  have hi : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have he : Tendsto (fun R : ℝ => 2*(1/4-eig)*(R⁻¹)^2) atTop (𝓝 0) := by
    convert tendsto_const_nhds.mul (hi.pow 2) using 1
    norm_num
  have hc := (Complex.continuous_ofReal.tendsto (Real.exp 0)).comp
    ((Real.continuous_exp.tendsto 0).comp he)
  have hvalue (R : ℝ) : spectralHeatEnergyWeight R eig = (Real.exp (2*(1/4-eig)*(R⁻¹)^2) : ℂ) := by
    rw [spectralHeatEnergyWeight_real,div_eq_mul_inv,inv_pow]
  simpa only [Function.comp_def,hvalue,Real.exp_zero,Complex.ofReal_one] using hc

end ArtinMatthews

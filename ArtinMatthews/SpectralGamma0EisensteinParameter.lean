module

public import ArtinMatthews.SpectralGamma0EisensteinSeries
public import Mathlib.Analysis.Complex.LocallyUniformLimit


set_option backward.privateInPublic true
@[expose] public section

/-! Holomorphic spectral-parameter dependence of the actual Eisenstein series. -/
noncomputable section
open Set Filter
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0EisensteinSummand_parameter_strip_bound (N : ℕ) (v : Gamma0EisensteinRows N)
    (z : UpperHalfPlane) (a b : ℝ) (s : ℂ) (ha : a ≤ s.re) (hb : s.re ≤ b) :
    ‖gamma0EisensteinSummand N s v z‖ ≤
      ‖gamma0EisensteinSummand N (a : ℂ) v z‖ + ‖gamma0EisensteinSummand N (b : ℂ) v z‖ := by
  simp only [gamma0EisensteinSummand_norm,Complex.ofReal_re]
  have hp := gamma0EisensteinHeight_pos N v z
  by_cases h : 1 ≤ gamma0EisensteinHeight N v z
  · exact (Real.rpow_le_rpow_of_exponent_le h hb).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hp.le a))
  · exact (Real.rpow_le_rpow_of_exponent_ge hp (le_of_not_ge h) ha).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hp.le b))

theorem gamma0Eisenstein_differentiableOn_parameter_strip (N : ℕ) (z : UpperHalfPlane)
    (a b : ℝ) (ha : 1 < a) (hab : a < b) :
    DifferentiableOn ℂ (fun s => gamma0Eisenstein N s z) {s : ℂ | a < s.re ∧ s.re < b} := by
  have hsa := gamma0EisensteinSummand_summable_norm N (a : ℂ) (by simpa using ha) z
  have hsb := gamma0EisensteinSummand_summable_norm N (b : ℂ) (by simpa using ha.trans hab) z
  have hsum : DifferentiableOn ℂ
      (fun s : ℂ => ∑' v : Gamma0EisensteinRows N, gamma0EisensteinSummand N s v z)
      {s : ℂ | a < s.re ∧ s.re < b} := by
    apply Complex.differentiableOn_tsum_of_summable_norm (hsa.add hsb)
      (fun v => (gamma0EisensteinSummand_differentiable_s N v z).differentiableOn)
    · exact (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    · intro v s hs
      exact gamma0EisensteinSummand_parameter_strip_bound N v z a b s hs.1.le hs.2.le
  exact hsum.const_mul (1/2 : ℂ)

theorem gamma0Eisenstein_differentiableAt_parameter (N : ℕ) (z : UpperHalfPlane)
    (s : ℂ) (hs : 1 < s.re) : DifferentiableAt ℂ (fun w => gamma0Eisenstein N w z) s := by
  let a : ℝ := (1+s.re)/2
  let b : ℝ := s.re+1
  have ha : 1 < a := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a,b]; linarith
  have hmem : s ∈ {w : ℂ | a < w.re ∧ w.re < b} := by
    constructor <;> dsimp [a,b] <;> linarith
  exact (gamma0Eisenstein_differentiableOn_parameter_strip N z a b ha hab s hmem).differentiableAt
    (((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds hmem)

theorem gamma0Eisenstein_analytic_parameter (N : ℕ) (z : UpperHalfPlane) :
    AnalyticOnNhd ℂ (fun s => gamma0Eisenstein N s z) {s : ℂ | 1 < s.re} := by
  apply DifferentiableOn.analyticOnNhd
  · intro s hs
    exact (gamma0Eisenstein_differentiableAt_parameter N z s hs).differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_re

end ArtinMatthews

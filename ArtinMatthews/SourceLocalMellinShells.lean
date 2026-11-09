module

public import ArtinMatthews.SourceLocalMultiplicativeShell
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.Real


set_option backward.privateInPublic true
@[expose] public section

/-! Actual shell Mellin integrals. No normalization of the unit shell
to probability measure is made. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain MeasureTheory Set
open scoped NumberField
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (P : HeightOneSpectrum (𝓞 K))

local notation "k" => P.adicCompletion K
local notation "q" => (Ideal.absNorm P.asIdeal : ℝ)
local notation "μ" => sourceLocalMulMeasure K P

def sourceLocalMellinWeight (z : ℂ) (u : kˣ) : ℂ := (‖(u : k)‖ : ℂ) ^ z

def sourceLocalMellinShellMass : ℝ :=
  (sourceLocalSelfDual K P).real (sourceLocalBall K P 0) * (1 - q⁻¹)

theorem sourceLocalMellinQ_gt_one : 1 < q := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm P

theorem sourceLocalMellinRatio_norm_lt_one (z : ℂ) (hz : 0 < z.re) :
    ‖(q : ℂ) ^ (-z)‖ < 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (sourceLocalNorm_pos K P), Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg (sourceLocalMellinQ_gt_one K P) (neg_lt_zero.mpr hz)

theorem sourceLocalMellinWeight_shell_geometric (n : ℤ) (m : ℕ) (z : ℂ) {u : kˣ}
    (hu : u ∈ sourceLocalMulShell K P (n - (m : ℤ))) :
    sourceLocalMellinWeight K P z u =
      (q : ℂ) ^ ((n : ℂ) * z) * ((q : ℂ) ^ (-z)) ^ m := by
  have hq := sourceLocalNorm_pos K P
  rw [sourceLocalMellinWeight, sourceLocalMulShell_norm K P _ hu,
    ← Real.rpow_intCast, ← Complex.cpow_mul_ofReal_nonneg hq.le]
  have h : (((n - (m : ℤ) : ℤ) : ℝ) : ℂ) * z =
      (n : ℂ) * z + (m : ℂ) * (-z) := by push_cast; ring
  rw [h, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hq.ne'), Complex.cpow_nat_mul]

theorem sourceLocalMellinWeight_integrable_shell (n : ℤ) (z : ℂ) :
    IntegrableOn (sourceLocalMellinWeight K P z) (sourceLocalMulShell K P n) μ := by
  let : (sourceLocalMulMeasure K P).IsHaarMeasure := sourceLocalMulMeasure_isHaar K P
  refine (integrableOn_const (C := ((q ^ n : ℝ) : ℂ) ^ z)
    (sourceLocalMulShell_isCompact K P n).measure_ne_top).congr_fun ?_
      (sourceLocalMulShell_measurable K P n)
  intro u hu
  rw [sourceLocalMellinWeight, sourceLocalMulShell_norm K P n hu]

theorem sourceLocalMellinWeight_integral_shell (n : ℤ) (m : ℕ) (z : ℂ) :
    (∫ u in sourceLocalMulShell K P (n - (m : ℤ)), sourceLocalMellinWeight K P z u ∂μ) =
      (sourceLocalMellinShellMass K P : ℂ) * (q : ℂ) ^ ((n : ℂ) * z) *
        ((q : ℂ) ^ (-z)) ^ m := by
  rw [setIntegral_congr_fun (sourceLocalMulShell_measurable K P _)
    (fun _ hu => sourceLocalMellinWeight_shell_geometric K P n m z hu),
    setIntegral_const, sourceLocalMulShell_mass, Complex.real_smul, sourceLocalMellinShellMass]
  ring

theorem sourceLocalMellinWeight_norm_integral_shell (n : ℤ) (m : ℕ) (z : ℂ) :
    (∫ u in sourceLocalMulShell K P (n - (m : ℤ)), ‖sourceLocalMellinWeight K P z u‖ ∂μ) =
      sourceLocalMellinShellMass K P * ‖(q : ℂ) ^ ((n : ℂ) * z)‖ *
        ‖(q : ℂ) ^ (-z)‖ ^ m := by
  have h (u : kˣ) (hu : u ∈ sourceLocalMulShell K P (n - (m : ℤ))) :
      ‖sourceLocalMellinWeight K P z u‖ =
        ‖(q : ℂ) ^ ((n : ℂ) * z)‖ * ‖(q : ℂ) ^ (-z)‖ ^ m := by
    rw [sourceLocalMellinWeight_shell_geometric K P n m z hu, norm_mul, norm_pow]
  rw [setIntegral_congr_fun (sourceLocalMulShell_measurable K P _) h,
    setIntegral_const, sourceLocalMulShell_mass, smul_eq_mul, sourceLocalMellinShellMass]
  ring

end
end ArtinMatthews.SourcePhysical

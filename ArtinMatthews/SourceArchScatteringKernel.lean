module

public import ArtinMatthews.SourceArchSphericalSection
public import ArtinMatthews.SourceArchSelfDualMeasure
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket


set_option backward.privateInPublic true
@[expose] public section

/-! The literal unoscillated spherical Jacquet kernel, with its
absolute convergence on the right half-plane. -/
namespace ArtinMatthews.SourceArchJacquet

open MeasureTheory
open ArtinMatthews.VaryingKummerAnalytic
open scoped MatrixGroups
noncomputable section

def sourceArchScatteringKernel (s : ℂ) (x : ℂ) : ℂ :=
  ((1 + ‖x‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * s + 1))

theorem sourceArchScatteringKernel_continuous (s : ℂ) :
    Continuous (sourceArchScatteringKernel s) := by
  unfold sourceArchScatteringKernel
  apply Continuous.cpow (by fun_prop) continuous_const
  intro x
  exact Complex.ofReal_mem_slitPlane.mpr (by positivity)

theorem sourceArchScatteringKernel_norm (s : ℂ) (x : ℂ) :
    ‖sourceArchScatteringKernel s x‖ =
      (1 + ‖x‖ ^ 2) ^ (-(2 * s.re + 1)) := by
  unfold sourceArchScatteringKernel
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  congr 1
  simp

theorem sourceArchScatteringKernel_integrable {s : ℂ} (hs : 0 < s.re) :
    Integrable (sourceArchScatteringKernel s) sourceComplexTraceMeasure := by
  have hd : (Module.finrank ℝ ℂ : ℝ) < 4 * s.re + 2 := by
    rw [Complex.finrank_real_complex]
    norm_num
    linarith
  have hi := integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure ℂ)) hd
  have hn : Integrable (fun x : ℂ => ‖sourceArchScatteringKernel s x‖) := by
    apply hi.congr
    exact Filter.Eventually.of_forall fun x => by
      dsimp only
      rw [sourceArchScatteringKernel_norm]
      congr 1
      ring
  have hc : Integrable (sourceArchScatteringKernel s) :=
    (integrable_norm_iff (sourceArchScatteringKernel_continuous s).aestronglyMeasurable).mp hn
  exact hc.smul_measure (by norm_num)

theorem sourceArchSphericalSection_scatteringKernel (s : ℂ) (x : ℂ) :
    sourceArchSphericalSection s (sourcePGL2Weyl * sourcePGL2Upper x) =
      sourceArchScatteringKernel s x := by
  have hdiagGL : sourceGL2Diagonal (1 : ℂˣ) = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [sourceGL2Diagonal]
  have hdiag : sourcePGL2Diagonal (1 : ℂˣ) = 1 := by
    change Matrix.ProjGenLinGroup.mk (sourceGL2Diagonal (1 : ℂˣ)) = 1
    rw [hdiagGL, map_one]
  have h := sourceArchSphericalSection_bigCell s x (1 : ℂˣ)
  simp only [hdiag, mul_one, Units.val_one, norm_one, one_pow] at h
  rw [h, sourceArchScatteringKernel, Complex.ofReal_div, Complex.ofReal_one, one_div,
    Complex.inv_cpow_ofReal_nonneg (by positivity), ← Complex.cpow_neg]

def sourceArchScattering (s : ℂ) : ℂ :=
  ∫ x : ℂ, sourceArchSphericalSection s (sourcePGL2Weyl * sourcePGL2Upper x)
    ∂sourceComplexTraceMeasure

theorem sourceArchScattering_integrable {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun x : ℂ => sourceArchSphericalSection s
      (sourcePGL2Weyl * sourcePGL2Upper x)) sourceComplexTraceMeasure := by
  simp_rw [sourceArchSphericalSection_scatteringKernel]
  exact sourceArchScatteringKernel_integrable hs

end
end ArtinMatthews.SourceArchJacquet

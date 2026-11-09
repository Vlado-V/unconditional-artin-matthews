module

public import ArtinMatthews.SpectralGamma0EisensteinConvergence
public import ArtinMatthews.SpectralGamma0EisensteinPositive
public import Mathlib.Analysis.Fourier.AddCircle


set_option backward.privateInPublic true
@[expose] public section

/-! Honest period-one Fourier inputs for the convergent Eisenstein family at infinity. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups
namespace ArtinMatthews

def gamma0EisensteinSlice (N : ℕ) (s : ℂ) (y : ℝ) (hy : 0 < y) (x : ℝ) : ℂ :=
  gamma0Eisenstein N s ⟨⟨x,y⟩,hy⟩

theorem gamma0EisensteinSlice_continuous (N : ℕ) (s : ℂ) (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) : Continuous (gamma0EisensteinSlice N s y hy) := by
  have hm : Continuous (fun x : ℝ => Complex.mk x y) := by
    convert Complex.continuous_ofReal.add (continuous_const : Continuous (fun _ : ℝ => (y:ℂ)*Complex.I)) using 1
    funext x
    apply Complex.ext <;> simp
  have hc : Continuous (fun x : ℝ => (⟨⟨x,y⟩,hy⟩ : UpperHalfPlane)) :=
    hm.upperHalfPlaneMk (fun _ => hy)
  exact (gamma0Eisenstein_continuous N s hs).comp hc

theorem gamma0EisensteinSlice_periodic (N : ℕ) (s : ℂ) (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) : Function.Periodic (gamma0EisensteinSlice N s y hy) 1 := by
  intro x
  have he : ModularGroup.T • (⟨⟨x,y⟩,hy⟩ : UpperHalfPlane) = ⟨⟨x+1,y⟩,hy⟩ := by
    apply UpperHalfPlane.ext
    apply Complex.ext
    · exact ModularGroup.re_T_smul _
    · exact ModularGroup.im_T_smul _
  unfold gamma0EisensteinSlice
  rw [← he]
  exact gamma0Eisenstein_translation_invariant N s hs _

def gamma0EisensteinFourierCoefficient (N : ℕ) (s : ℂ) (y : ℝ) (hy : 0 < y) (n : ℤ) : ℂ :=
  fourierCoeffOn (by norm_num : (0:ℝ)<1) (gamma0EisensteinSlice N s y hy) n

theorem gamma0EisensteinSlice_memLp (N : ℕ) (s : ℂ) (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) :
    MemLp (gamma0EisensteinSlice N s y hy) 2 (volume.restrict (Ioc (0:ℝ) 1)) := by
  have hc := gamma0EisensteinSlice_continuous N s hs y hy
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  exact (hc.norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self

theorem gamma0EisensteinFourier_parseval (N : ℕ) (s : ℂ) (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) :
    HasSum (fun n : ℤ => ‖gamma0EisensteinFourierCoefficient N s y hy n‖^2)
      (∫ x in (0:ℝ)..1, ‖gamma0EisensteinSlice N s y hy x‖^2) := by
  unfold gamma0EisensteinFourierCoefficient
  have h := hasSum_sq_fourierCoeffOn (by norm_num : (0:ℝ)<1)
    (gamma0EisensteinSlice_memLp N s hs y hy)
  simpa only [sub_zero,inv_one,one_smul] using h

theorem gamma0EisensteinFourier_zero (N : ℕ) (s : ℂ) (y : ℝ) (hy : 0 < y) :
    gamma0EisensteinFourierCoefficient N s y hy 0 =
      ∫ x in (0:ℝ)..1, gamma0EisensteinSlice N s y hy x := by
  unfold gamma0EisensteinFourierCoefficient
  rw [fourierCoeffOn_eq_integral]
  simp

theorem gamma0EisensteinFourier_zero_lower_bound (N : ℕ) (s : ℝ) (hs : 1 < s)
    (y : ℝ) (hy : 0 < y) :
    y^s ≤ (gamma0EisensteinFourierCoefficient N (s : ℂ) y hy 0).re := by
  have hc := gamma0EisensteinSlice_continuous N (s : ℂ) (by simpa using hs) y hy
  have hf : IntegrableOn (gamma0EisensteinSlice N (s : ℂ) y hy) (Ioc (0:ℝ) 1) :=
    hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  rw [gamma0EisensteinFourier_zero,intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  have hre : (∫ x in Ioc (0:ℝ) 1, gamma0EisensteinSlice N (s : ℂ) y hy x).re =
      ∫ x in Ioc (0:ℝ) 1, (gamma0EisensteinSlice N (s : ℂ) y hy x).re :=
    (integral_re hf).symm
  rw [hre]
  have hconst : IntegrableOn (fun _x : ℝ => y^s) (Ioc (0:ℝ) 1) :=
    continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hb := integral_mono_ae hconst hf.re (Eventually.of_forall (fun x =>
    gamma0Eisenstein_real_lower_bound N s hs (⟨⟨x,y⟩,hy⟩ : UpperHalfPlane)))
  simpa using hb

end ArtinMatthews

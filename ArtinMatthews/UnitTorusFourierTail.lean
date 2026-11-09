module

public import ArtinMatthews.UnitTorusPoincare
public import Mathlib.Data.Fintype.Pi


set_option backward.privateInPublic true
@[expose] public section

/-! Finite Fourier truncations and their quantitative weak-H1 tails. -/
namespace ArtinMatthews
open MeasureTheory UnitAddTorus
open scoped BigOperators ComplexConjugate ENNReal
noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable (ι : Type*) [Fintype ι]

theorem unitTorus_fourier_parseval_norm (f : UnitTorusL2 ι) :
    HasSum (fun n : ι → ℤ => ‖mFourierCoeff f n‖ ^ 2) (‖f‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map,
    mFourierBasis_repr] using
    lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (mFourierBasis.repr f)

def unitTorusFourierTruncation (S : Finset (ι → ℤ)) (f : UnitTorusL2 ι) : UnitTorusL2 ι :=
  ∑ n ∈ S, mFourierCoeff f n • mFourierBasis n

theorem unitTorus_fourier_coefficient_norm (f : UnitTorusL2 ι) (n : ι → ℤ) :
    ‖mFourierCoeff f n‖ ≤ ‖f‖ := by
  rw [← unitTorusCoefficient_apply]
  change ‖inner ℂ (mFourierBasis n) f‖ ≤ ‖f‖
  simpa only [mFourierBasis.orthonormal.norm_eq_one, one_mul] using
    norm_inner_le_norm (mFourierBasis n) f

theorem unitTorus_fourier_truncation_coefficient (S : Finset (ι → ℤ))
    (f : UnitTorusL2 ι) (n : ι → ℤ) :
    mFourierCoeff (unitTorusFourierTruncation ι S f) n =
      if n ∈ S then mFourierCoeff f n else 0 := by
  classical
  rw [← unitTorusCoefficient_apply]
  simp only [unitTorusFourierTruncation, map_sum, map_smul,
    unitTorusCoefficient_apply, ← mFourierBasis_repr, mFourierBasis.repr_self,
    lp.single_apply, Pi.single_apply, smul_eq_mul]
  simp

theorem unitTorus_fourier_tail_coefficient (S : Finset (ι → ℤ))
    (f : UnitTorusL2 ι) (n : ι → ℤ) :
    mFourierCoeff (f - unitTorusFourierTruncation ι S f) n =
      if n ∈ S then 0 else mFourierCoeff f n := by
  classical
  rw [← unitTorusCoefficient_apply, map_sub, unitTorusCoefficient_apply,
    unitTorusCoefficient_apply, unitTorus_fourier_truncation_coefficient]
  split_ifs <;> simp

variable [DecidableEq ι]

def unitTorusFrequencyBox (N : ℕ) : Finset (ι → ℤ) :=
  Fintype.piFinset (fun _ : ι => Finset.Icc (-(N : ℤ)) N)

theorem unitTorusFrequencyBox_mem (N : ℕ) (n : ι → ℤ) :
    n ∈ unitTorusFrequencyBox ι N ↔ ∀ j, -(N : ℤ) ≤ n j ∧ n j ≤ N := by
  simp only [unitTorusFrequencyBox, Fintype.mem_piFinset, Finset.mem_Icc]

theorem unitTorusFrequencyBox_outside (N : ℕ) (n : ι → ℤ)
    (hn : n ∉ unitTorusFrequencyBox ι N) : ∃ j, (N : ℝ) < ‖(n j : ℂ)‖ := by
  rw [unitTorusFrequencyBox_mem] at hn
  push Not at hn
  obtain ⟨j, hj⟩ := hn
  refine ⟨j, ?_⟩
  have ha : (N : ℤ) < |n j| := by
    by_contra h
    have hh := abs_le.mp (le_of_not_gt h)
    omega
  rw [Complex.norm_intCast, ← Int.cast_abs]
  exact_mod_cast ha

theorem unitTorus_weakGradient_fourier_tail_sq (N : ℕ) (f : UnitTorusL2 ι)
    (g : ι → UnitTorusL2 ι) (hgrad : UnitTorusWeakGradient ι f g) :
    (N : ℝ) ^ 2 * ‖f - unitTorusFourierTruncation ι (unitTorusFrequencyBox ι N) f‖ ^ 2 ≤
      ∑ j, ‖g j‖ ^ 2 := by
  have hf := unitTorus_fourier_parseval_norm ι
    (f - unitTorusFourierTruncation ι (unitTorusFrequencyBox ι N) f)
  have hg : HasSum (fun n : ι → ℤ => ∑ j, ‖mFourierCoeff (g j) n‖ ^ 2)
      (∑ j, ‖g j‖ ^ 2) :=
    hasSum_sum fun j _ => unitTorus_fourier_parseval_norm ι (g j)
  apply hasSum_le _ (hf.mul_left ((N : ℝ) ^ 2)) hg
  intro n
  rw [unitTorus_fourier_tail_coefficient]
  by_cases hn : n ∈ unitTorusFrequencyBox ι N
  · simp only [ite_eq_left hn, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [ite_eq_right hn]
  obtain ⟨j, hj⟩ := unitTorusFrequencyBox_outside ι N n hn
  have hphase : ‖2 * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hp : 1 ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
  have hnorm : (N : ℝ) * ‖mFourierCoeff f n‖ ≤ ‖mFourierCoeff (g j) n‖ := by
    rw [hgrad j n, norm_mul, norm_mul, hphase]
    calc
      (N : ℝ) * ‖mFourierCoeff f n‖ ≤ ‖(n j : ℂ)‖ * ‖mFourierCoeff f n‖ := by gcongr
      _ ≤ (2 * Real.pi) * ‖(n j : ℂ)‖ * ‖mFourierCoeff f n‖ := by
        exact mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_left (norm_nonneg _) hp) (norm_nonneg _)
  calc
    (N : ℝ) ^ 2 * ‖mFourierCoeff f n‖ ^ 2 =
        ((N : ℝ) * ‖mFourierCoeff f n‖) ^ 2 := by ring
    _ ≤ ‖mFourierCoeff (g j) n‖ ^ 2 := pow_le_pow_left₀ (by positivity) hnorm 2
    _ ≤ ∑ j, ‖mFourierCoeff (g j) n‖ ^ 2 :=
      Finset.single_le_sum (f := fun j => ‖mFourierCoeff (g j) n‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ j)

theorem unitTorus_weakGradient_fourier_tail (N : ℕ) (f : UnitTorusL2 ι)
    (g : ι → UnitTorusL2 ι) (hgrad : UnitTorusWeakGradient ι f g) :
    (N : ℝ) * ‖f - unitTorusFourierTruncation ι (unitTorusFrequencyBox ι N) f‖ ≤
      Real.sqrt (∑ j, ‖g j‖ ^ 2) := by
  have h := unitTorus_weakGradient_fourier_tail_sq ι N f g hgrad
  have hnonneg : 0 ≤ ∑ j, ‖g j‖ ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg ‖g j‖)
  have hs := Real.sq_sqrt hnonneg
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N)
    (norm_nonneg (f - unitTorusFourierTruncation ι (unitTorusFrequencyBox ι N) f)),
    Real.sqrt_nonneg (∑ j, ‖g j‖ ^ 2)]

end
end ArtinMatthews

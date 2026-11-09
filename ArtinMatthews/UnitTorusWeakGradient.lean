module

public import Mathlib.Analysis.Fourier.AddCircleMulti


set_option backward.privateInPublic true
@[expose] public section

/-! The normalized multitorus Fourier gradient and its zero-mean energy inequality. -/
namespace ArtinMatthews
open MeasureTheory UnitAddTorus
open scoped BigOperators ComplexConjugate ENNReal
noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable (ι : Type*) [Fintype ι]

abbrev unitTorusHaar : Measure (UnitAddTorus ι) :=
  Measure.pi (fun _ : ι => AddCircle.haarAddCircle)

instance unitTorusHaar_probability : IsProbabilityMeasure (unitTorusHaar ι) := by
  unfold unitTorusHaar
  infer_instance

abbrev UnitTorusL2 := Lp ℂ 2 (unitTorusHaar ι)

def unitTorusCoefficient (n : ι → ℤ) : UnitTorusL2 ι →L[ℂ] ℂ :=
  innerSL ℂ (mFourierBasis n)

theorem unitTorusCoefficient_apply (n : ι → ℤ) (f : UnitTorusL2 ι) :
    unitTorusCoefficient ι n f = mFourierCoeff f n := by
  exact (HilbertBasis.repr_apply_apply mFourierBasis f n).symm.trans (mFourierBasis_repr f n)

def UnitTorusWeakGradient (f : UnitTorusL2 ι) (g : ι → UnitTorusL2 ι) : Prop :=
  ∀ j n, mFourierCoeff (g j) n =
    (2 * (Real.pi : ℂ) * Complex.I * (n j : ℂ)) * mFourierCoeff f n

theorem unitTorus_fourier_zero (f : UnitTorusL2 ι) :
    mFourierCoeff f (0 : ι → ℤ) = ∫ x, f x ∂unitTorusHaar ι := by
  simp only [mFourierCoeff, neg_zero, mFourier_zero, ContinuousMap.one_apply, one_smul]
  rfl

theorem unitTorusWeakGradient_poincare (f : UnitTorusL2 ι) (g : ι → UnitTorusL2 ι)
    (hgrad : UnitTorusWeakGradient ι f g)
    (hmean : (∫ x, f x ∂unitTorusHaar ι) = 0) :
    (2 * Real.pi) ^ 2 * (∫ x, ‖f x‖ ^ 2 ∂unitTorusHaar ι) ≤
      ∑ j, ∫ x, ‖g j x‖ ^ 2 ∂unitTorusHaar ι := by
  have hf : HasSum (fun n : ι → ℤ => ‖mFourierCoeff f n‖ ^ 2)
      (∫ x, ‖f x‖ ^ 2 ∂unitTorusHaar ι) := hasSum_sq_mFourierCoeff f
  have hg : HasSum (fun n : ι → ℤ => ∑ j, ‖mFourierCoeff (g j) n‖ ^ 2)
      (∑ j, ∫ x, ‖g j x‖ ^ 2 ∂unitTorusHaar ι) := by
    exact hasSum_sum fun j _ => hasSum_sq_mFourierCoeff (g j)
  apply hasSum_le _ (hf.mul_left ((2 * Real.pi) ^ 2)) hg
  intro n
  by_cases hn : n = 0
  · subst n
    rw [unitTorus_fourier_zero ι f, hmean, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hn
  have hj0 : n j ≠ 0 := by simpa only [Pi.zero_apply] using hj
  have hjNorm : 1 ≤ ‖(n j : ℂ)‖ := by
    have hnat : 1 ≤ (n j).natAbs := Nat.succ_le_iff.mpr (Int.natAbs_pos.mpr hj0)
    rw [Complex.norm_intCast, ← Int.cast_abs, Int.abs_eq_natAbs]
    exact_mod_cast hnat
  have hphase : ‖2 * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hnorm : (2 * Real.pi) * ‖mFourierCoeff f n‖ ≤ ‖mFourierCoeff (g j) n‖ := by
    rw [hgrad j n, norm_mul, norm_mul, hphase]
    nlinarith [mul_nonneg (by positivity : 0 ≤ 2 * Real.pi)
      (mul_nonneg (sub_nonneg.mpr hjNorm) (norm_nonneg (mFourierCoeff f n)))]
  calc
    (2 * Real.pi) ^ 2 * ‖mFourierCoeff f n‖ ^ 2 =
        ((2 * Real.pi) * ‖mFourierCoeff f n‖) ^ 2 := by ring
    _ ≤ ‖mFourierCoeff (g j) n‖ ^ 2 := pow_le_pow_left₀ (by positivity) hnorm 2
    _ ≤ ∑ j, ‖mFourierCoeff (g j) n‖ ^ 2 :=
      Finset.single_le_sum (f := fun j => ‖mFourierCoeff (g j) n‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ j)

theorem unitTorusWeakGradient_isClosed :
    IsClosed {fg : UnitTorusL2 ι × (ι → UnitTorusL2 ι) |
      UnitTorusWeakGradient ι fg.1 fg.2} := by
  have hset : {fg : UnitTorusL2 ι × (ι → UnitTorusL2 ι) |
      UnitTorusWeakGradient ι fg.1 fg.2} =
      ⋂ j : ι, ⋂ n : ι → ℤ, {fg | unitTorusCoefficient ι n (fg.2 j) =
        (2 * (Real.pi : ℂ) * Complex.I * (n j : ℂ)) * unitTorusCoefficient ι n fg.1} := by
    ext fg
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, unitTorusCoefficient_apply, UnitTorusWeakGradient]
  rw [hset]
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro n
  apply isClosed_eq
  · exact (unitTorusCoefficient ι n).continuous.comp ((continuous_apply j).comp continuous_snd)
  · exact continuous_const.mul ((unitTorusCoefficient ι n).continuous.comp continuous_fst)

theorem unitTorusWeakGradient_tendsto {κ : Type*} {l : Filter κ}
    [Filter.NeBot l] {f : κ → UnitTorusL2 ι} {g : κ → ι → UnitTorusL2 ι}
    {f₀ : UnitTorusL2 ι} {g₀ : ι → UnitTorusL2 ι}
    (hgrad : ∀ᶠ k in l, UnitTorusWeakGradient ι (f k) (g k))
    (hf : Filter.Tendsto f l (nhds f₀)) (hg : Filter.Tendsto g l (nhds g₀)) :
    UnitTorusWeakGradient ι f₀ g₀ := by
  exact (unitTorusWeakGradient_isClosed ι).mem_of_tendsto (hf.prodMk_nhds hg) hgrad

end
end ArtinMatthews

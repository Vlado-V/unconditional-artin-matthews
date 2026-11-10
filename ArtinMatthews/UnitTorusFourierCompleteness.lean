module

public import ArtinMatthews.UnitTorusWeakGradient


set_option backward.privateInPublic true
@[expose] public section

/-! A normalized torus function with no nonzero Fourier modes is almost
everywhere constant. The result uses the full integer Fourier basis. -/
namespace ArtinMatthews
open MeasureTheory UnitAddTorus
open scoped ENNReal
noncomputable section

local instance unitTorusCompletenessMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance unitTorusCompletenessProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable (ι : Type*) [Fintype ι]

theorem unitTorus_eq_const_ae_of_nonzero_fourierCoeff_eq_zero
    (F : UnitAddTorus ι → ℂ) (hF : MemLp F 2 (unitTorusHaar ι))
    (hzero : ∀ n : ι → ℤ, n ≠ 0 → mFourierCoeff F n = 0) :
    F =ᵐ[unitTorusHaar ι] fun _ => mFourierCoeff F 0 := by
  classical
  let f : UnitTorusL2 ι := hF.toLp F
  have hcoe : (f : UnitAddTorus ι → ℂ) =ᵐ[unitTorusHaar ι] F := hF.coeFn_toLp
  have hcoeff (n : ι → ℤ) : mFourierCoeff f n = mFourierCoeff F n := by
    unfold mFourierCoeff
    apply integral_congr_ae
    filter_upwards [hcoe] with t ht
    rw [ht]
  have heq : f = mFourierCoeff F 0 • mFourierBasis (0 : ι → ℤ) := by
    apply mFourierBasis.repr.injective
    apply lp.ext
    funext n
    have hleft : mFourierBasis.repr f n = mFourierCoeff F n :=
      (mFourierBasis_repr f n).trans (hcoeff n)
    rw [hleft, map_smul, mFourierBasis.repr_self]
    by_cases hn : n = 0
    · subst n
      simp [lp.single_apply]
    · simp [lp.single_apply, hn, hzero n hn]
  have hb : (mFourierBasis (0 : ι → ℤ) : UnitTorusL2 ι) =ᵐ[unitTorusHaar ι]
      fun _ => (1 : ℂ) := by
    have h0 : (fun t => mFourierLp 2 (0 : ι → ℤ) t) =ᵐ[unitTorusHaar ι]
        fun t => mFourier (0 : ι → ℤ) t := coeFn_mFourierLp 2 (0 : ι → ℤ)
    filter_upwards [h0] with t ht
    simpa only [coe_mFourierBasis, mFourier_zero, ContinuousMap.coe_one, Pi.one_apply] using ht
  filter_upwards [hcoe, Lp.coeFn_smul (mFourierCoeff F 0) (mFourierBasis (0 : ι → ℤ)),
    hb] with t ht hs hb'
  calc
    F t = f t := ht.symm
    _ = (mFourierCoeff F 0 • mFourierBasis (0 : ι → ℤ) : UnitTorusL2 ι) t :=
      congrArg (fun u : UnitTorusL2 ι => u t) heq
    _ = mFourierCoeff F 0 := by
      rw [hs]
      change mFourierCoeff F 0 * mFourierBasis (0 : ι → ℤ) t = mFourierCoeff F 0
      rw [hb', mul_one]

theorem unitTorus_add_left_ae_of_nonzero_fourierCoeff_eq_zero
    (F : UnitAddTorus ι → ℂ) (hF : MemLp F 2 (unitTorusHaar ι))
    (hzero : ∀ n : ι → ℤ, n ≠ 0 → mFourierCoeff F n = 0) (a : UnitAddTorus ι) :
    (fun t => F (a + t)) =ᵐ[unitTorusHaar ι] F := by
  have h := unitTorus_eq_const_ae_of_nonzero_fourierCoeff_eq_zero ι F hF hzero
  have hmp : MeasurePreserving (fun t : UnitAddTorus ι => a + t) (unitTorusHaar ι)
      (unitTorusHaar ι) := measurePreserving_pi _ _ fun i =>
    measurePreserving_add_left AddCircle.haarAddCircle (a i)
  have ha : (fun t => F (a + t)) =ᵐ[unitTorusHaar ι] fun _ => mFourierCoeff F 0 :=
    hmp.quasiMeasurePreserving.ae h
  exact ha.trans h.symm

end
end ArtinMatthews

module

public import ArtinMatthews.SpectralBesselI


set_option backward.privateInPublic true
@[expose] public section

/-! Continuity of the actual I series away from its power branch point. -/

noncomputable section

namespace ArtinMatthews

theorem spectralBesselI_continuousAt (ν : ℂ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (spectralBesselI ν) x := by
  unfold spectralBesselI
  apply ContinuousAt.mul
  · apply ContinuousAt.cpow (by fun_prop) continuousAt_const
    have hp : 0 < x/2 := half_pos hx
    simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using
      (Complex.ofReal_mem_slitPlane.mpr hp)
  · exact (Complex.analyticAt_regularizedHGFun_zero (b := {ν+1}) _).continuousAt.comp (by fun_prop)

end ArtinMatthews

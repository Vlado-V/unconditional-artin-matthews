module

public import ArtinMatthews.SpectralCuspRayRepresentative


set_option backward.privateInPublic true
@[expose] public section

/-! Actual weak complex Euler pairs on a positive cusp ray admit classical
representatives, constructed from their locally integrable functions. -/
namespace ArtinMatthews
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
open SpectralCuspRayRegularity

theorem cuspRayWeakEuler_exists_classical {Y : ℝ} (hY : 0≤Y) (eig : ℂ) (c g : ℝ → ℂ)
    (hc : LocallyIntegrableOn c (Ioi Y) volume)
    (hg : LocallyIntegrableOn g (Ioi Y) volume)
    (hfirst : RayWeakDerivative (Y:=Y) c g)
    (hsecond : RayWeakDerivative (Y:=Y) g (fun y => -eig*c y/(y:ℂ)^2)) :
    ∃ C G : ℝ → ℂ, ContinuousOn C (Ioi Y) ∧ ContinuousOn G (Ioi Y) ∧
      c =ᵐ[volume.restrict (Ioi Y)] C ∧ g =ᵐ[volume.restrict (Ioi Y)] G ∧
      (∀ y>Y, HasDerivAt C (G y) y) ∧
      (∀ y>Y, HasDerivAt G (-eig*C y/(y:ℂ)^2) y) := by
  let m : ℝ → ℂ := fun y => -eig/(y:ℂ)^2
  have hm : ContinuousOn m (Ioi Y) := by
    apply continuousOn_const.div (Complex.continuous_ofReal.continuousOn.pow 2)
    intro y hy
    exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (lt_of_le_of_lt hY hy).ne')
  have hmc : LocallyIntegrableOn (fun y => m y • c y) (Ioi Y) volume :=
    hc.continuousOn_smul isOpen_Ioi.isLocallyClosed hm
  have hsecond' : RayWeakDerivative (Y:=Y) g (fun y => m y • c y) := by
    simpa only [m,smul_eq_mul,div_mul_eq_mul_div] using hsecond
  obtain ⟨C,hC,hcC⟩ := ray_weak_continuous_representative hY hc hg hfirst
  obtain ⟨G,hG,hgG⟩ := ray_weak_continuous_representative hY hg hmc hsecond'
  have hmcC : (fun y => m y • c y) =ᵐ[volume.restrict (Ioi Y)] fun y => m y • C y := by
    filter_upwards [hcC] with y hy
    rw [hy]
  refine ⟨C,G,hC,hG,hcC,hgG,rayWeakDerivative_hasDerivAt hY hc hg hfirst hC hG hcC hgG,?_⟩
  intro y hy
  have H := rayWeakDerivative_hasDerivAt hY hg hmc hsecond' hG (hm.smul hC) hgG hmcC y hy
  simpa only [m,smul_eq_mul,Pi.mul_apply,div_mul_eq_mul_div] using H

end
end ArtinMatthews

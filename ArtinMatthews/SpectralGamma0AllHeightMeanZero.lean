module

public import ArtinMatthews.SpectralGamma0CuspHeightRestriction


set_option backward.privateInPublic true
@[expose] public section

/-! The actual closed all-positive-height mean-zero energy subspace.
This definition does not identify its mass span with the complete automorphic
cuspidal L² space; that density/realization theorem remains separate. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups

namespace ArtinMatthews

def gamma0AllHeightMeanZeroEnergy (N : ℕ) [NeZero N] : Submodule ℂ (gamma0EnergySpace N) :=
  ⨅ (r : SL(2, ℤ)) (Y : {Y : ℝ // 0 < Y}),
    ((cuspHyperbolicAverageProjection (N : ℝ) Y.val Y.property).comp
      (gamma0CuspHeightRestriction N r Y.val Y.property)).ker

theorem mem_gamma0AllHeightMeanZeroEnergy_iff (N : ℕ) [NeZero N] (u : gamma0EnergySpace N) :
    u ∈ gamma0AllHeightMeanZeroEnergy N ↔
      ∀ (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y),
        cuspHyperbolicAverageProjection (N : ℝ) Y hY (gamma0CuspHeightRestriction N r Y hY u) = 0 := by
  simp only [gamma0AllHeightMeanZeroEnergy,Submodule.mem_iInf,LinearMap.mem_ker]
  constructor
  · intro h r Y hY
    exact h r ⟨Y,hY⟩
  · intro h r Y
    exact h r Y.val Y.property

theorem gamma0AllHeightMeanZeroEnergy_isClosed (N : ℕ) [NeZero N] :
    IsClosed (gamma0AllHeightMeanZeroEnergy N : Set (gamma0EnergySpace N)) := by
  unfold gamma0AllHeightMeanZeroEnergy
  simp_rw [Submodule.coe_iInf]
  exact isClosed_iInter (fun _ => isClosed_iInter (fun _ => ContinuousLinearMap.isClosed_ker _))

instance gamma0AllHeightMeanZeroEnergy_complete (N : ℕ) [NeZero N] :
    CompleteSpace (gamma0AllHeightMeanZeroEnergy N) :=
  (gamma0AllHeightMeanZeroEnergy_isClosed N).isComplete.completeSpace_coe

/-- The actual all-height condition supplies the height-one mean-zero
condition needed for the already proved uniform cusp tail estimate. -/
theorem gamma0AllHeightMeanZeroEnergy_tail_bound (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (u : gamma0AllHeightMeanZeroEnergy N) {Y : ℝ} (hY : 1 ≤ Y) :
    ‖spectralLpMeasureRestriction (spectralCuspHyperbolicMeasure_mono hY)
      (gamma0CuspEnergyRestriction N r u.val)‖^2 ≤
      ((N : ℝ)^2/Y^2)*(((N : ℝ)+1)*‖u‖^2) := by
  have hz := (mem_gamma0AllHeightMeanZeroEnergy_iff N u.val).mp u.property r 1 zero_lt_one
  rw [gamma0CuspHeightRestriction_one] at hz
  have ht := gamma0CuspEnergy_residual_tail_bound N r u.val hY
  rw [hz,sub_zero] at ht
  exact ht

end ArtinMatthews

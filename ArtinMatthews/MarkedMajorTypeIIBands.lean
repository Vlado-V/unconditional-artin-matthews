module

public import ArtinMatthews.MarkedArrayBandStructure
public import ArtinMatthews.MarkedMajorCharacterBudget


set_option backward.privateInPublic true
@[expose] public section

/-! All actual PD03 closed prime bands supply the major-input structure,
normalizers, logarithmic endpoints and unit support for every arc modulus. -/
namespace ArtinMatthews
open Filter

 theorem markedMajorTypeII_band_data {I : Type*} [Fintype I]
    (e : I → ℝ) (hinj : Function.Injective e)
    (he : ∀ i,(1/10:ℝ) < e i ∧ e i < (1/5:ℝ)) (A : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      Pairwise (fun i j => Disjoint (markedLogPowerBand (e i) (Real.exp L)) (markedLogPowerBand (e j) (Real.exp L))) ∧
      (∀ i p,p ∈ markedLogPowerBand (e i) (Real.exp L) → p.Prime ∧
        L^(1/(10:ℝ)) ≤ Real.log p ∧ Real.log p ≤ 2*L^(1/(5:ℝ))) ∧
      (∀ i,Real.log 2/2 ≤ bandReciprocalMass (markedLogPowerBand (e i) (Real.exp L))) ∧
      (∀ i p,p ∈ markedLogPowerBand (e i) (Real.exp L) → L^A < (p:ℝ)) := by
  have hs := Real.tendsto_exp_atTop.eventually
    (marked_actual_band_structure_eventually e (fun i => by linarith [(he i).1]) hinj
      (fun i => (he i).1.le) (fun i => (he i).2.le))
  filter_upwards [hs,marked_polynomial_le_exp_rpow 2 A (1/10) (by norm_num),
    eventually_gt_atTop (0:ℝ)] with L hL hsmall hpos
  simp only [Real.log_exp] at hL
  refine ⟨hL.1,?_,hL.2.2.1,?_⟩
  · intro i p hp
    have hh := hL.2.1 i p hp
    refine ⟨hh.1,?_,?_⟩
    · have hlog := Real.log_le_log (Real.exp_pos _) hh.2.1
      simpa only [Real.log_exp] using hlog
    · have hlog := Real.log_le_log (Nat.cast_pos.mpr hh.1.pos) hh.2.2
      simpa only [Real.log_exp] using hlog
  · intro i p hp
    have hh := hL.2.1 i p hp
    have hpA := Real.rpow_pos_of_pos hpos A
    exact (show L^A < Real.exp (L^(1/(10:ℝ))) by linarith).trans_le hh.2.1

end ArtinMatthews

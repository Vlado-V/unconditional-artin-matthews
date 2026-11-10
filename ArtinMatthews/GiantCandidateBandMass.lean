module

public import ArtinMatthews.GiantCandidateBandGeometry
public import ArtinMatthews.DivisorWeights
public import ArtinMatthews.MarkedEstimateMertensBandCore
public import ArtinMatthews.MarkedEstimateMertensBands
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! Mertens mass of the exact half-open candidate bands. The only change
from the proved closed interval is the possible upper endpoint. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators Topology
noncomputable section

theorem giantCandidatePrimeInterval_mass_defect (y : ℝ) :
    0 ≤ markedClosedBandMass (Real.exp y) (Real.exp (2*y)) -
        bandReciprocalMass (giantCandidatePrimeInterval y) ∧
      markedClosedBandMass (Real.exp y) (Real.exp (2*y)) -
        bandReciprocalMass (giantCandidatePrimeInterval y) ≤ Real.exp (-(2*y)) := by
  classical
  let D := (Nat.primesLE ⌊Real.exp (2*y)⌋₊).filter
    (fun p : ℕ => Real.exp y ≤ (p:ℝ))
  let I := giantCandidatePrimeInterval y
  let B := D \ I
  have hsub : I ⊆ D := by
    intro p hp
    obtain ⟨hpP,hpL,hpU⟩ := mem_giantCandidatePrimeInterval.mp hp
    exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr
      ⟨(Nat.le_floor_iff (Real.exp_nonneg _)).mpr hpU.le,hpP⟩,hpL⟩
  have hB (p : ℕ) (hp : p ∈ B) : (p:ℝ) = Real.exp (2*y) := by
    obtain ⟨hpD,hpI⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hpP,hpL⟩ := mem_filter.mp hpD
    have hupper := (Nat.le_floor_iff (Real.exp_nonneg _)).mp (Nat.mem_primesLE.mp hpP).1
    have hlower : Real.exp (2*y) ≤ (p:ℝ) := by
      by_contra! h
      exact hpI (mem_giantCandidatePrimeInterval.mpr ⟨(Nat.mem_primesLE.mp hpP).2,hpL,h⟩)
    exact le_antisymm hupper hlower
  have hcard : B.card ≤ 1 := by
    apply card_le_one.mpr
    intro p hp q hq
    exact_mod_cast (hB p hp).trans (hB q hq).symm
  have hdiff :
      markedClosedBandMass (Real.exp y) (Real.exp (2*y)) -
        bandReciprocalMass (giantCandidatePrimeInterval y) = ∑ p∈B, 1/(p:ℝ) := by
    have h := sum_sdiff hsub (f := fun p : ℕ => 1/(p:ℝ))
    change (∑ p∈B,1/(p:ℝ)) + (∑ p∈I,1/(p:ℝ)) = ∑ p∈D,1/(p:ℝ) at h
    change (∑ p∈D,1/(p:ℝ)) - (∑ p∈I,1/(p:ℝ)) = _
    linarith
  rw [hdiff]
  constructor
  · exact sum_nonneg (fun p _ => by positivity)
  · calc
      _ = (B.card:ℝ) * Real.exp (-(2*y)) := by
        have hb : (∑ p∈B,1/(p:ℝ)) = ∑ _p∈B, Real.exp (-(2*y)) := by
          apply sum_congr rfl
          intro p hp
          rw [hB p hp,one_div,Real.exp_neg]
        rw [hb,sum_const,nsmul_eq_mul]
      _ ≤ _ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (show (B.card:ℝ)≤1 by exact_mod_cast hcard) (Real.exp_nonneg _)

theorem giantCandidatePrimeInterval_mass_tendsto :
    Tendsto (fun y : ℝ => bandReciprocalMass (giantCandidatePrimeInterval y))
      atTop (𝓝 (Real.log 2)) := by
  have he : Tendsto (fun y : ℝ => Real.exp (-(2*y))) atTop (𝓝 0) := by
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<2))
  have hd : Tendsto (fun y : ℝ => markedClosedBandMass (Real.exp y) (Real.exp (2*y)) -
      bandReciprocalMass (giantCandidatePrimeInterval y)) atTop (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall (fun y => (giantCandidatePrimeInterval_mass_defect y).1))
      (Filter.Eventually.of_forall (fun y => (giantCandidatePrimeInterval_mass_defect y).2)) he
  have h := marked_exponential_band_mass_tendsto.sub hd
  rw [sub_zero] at h
  apply h.congr'
  filter_upwards [] with y
  simp only [sub_sub_cancel]

theorem giantCandidatePrimeInterval_mass_eventually :
    ∀ᶠ y : ℝ in atTop,
      Real.log 2/2 < bandReciprocalMass (giantCandidatePrimeInterval y) ∧
        bandReciprocalMass (giantCandidatePrimeInterval y) < 1 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hupper : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1)
    linarith
  exact giantCandidatePrimeInterval_mass_tendsto.eventually (Ioo_mem_nhds (by linarith) hupper)

end
end ArtinMatthews

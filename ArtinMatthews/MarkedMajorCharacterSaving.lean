module

public import ArtinMatthews.MarkedMajorCharacterActual
public import ArtinMatthews.MarkedMajorCharacterBudget


set_option backward.privateInPublic true
@[expose] public section

/-! Arbitrary logarithmic saving for the original fixed-rational-arc source.
The six-character decomposition, actual endpoint energies, and all finite
character costs are discharged; only literal arithmetic support remains. -/
namespace ArtinMatthews
open Filter Finset Set
open scoped ContDiff

theorem markedMajor_arcSource_all_log
    (cfg : MarkedMajorLabelEnergyConfig) (σ Kx : ℝ) (hσ : 0 ≤ σ)
    (cutoff : ℝ → ℂ) (hcutoff : ContDiff ℝ ∞ cutoff) (hnorm : ∀ y, ‖cutoff y‖ ≤ 1)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi) (hinterval : lo < 4*hi)
    (hsupp : Function.support cutoff ⊆ Set.Icc lo hi)
    (ψ : SchwartzMap ℝ ℂ) {R : ℝ} (hψ : tsupport ψ ⊆ Set.Icc (-R) R) (P : ℝ) (hP : 0 ≤ P) :
    ∀ᶠ L : ℝ in atTop, ∀ X : ℝ, 1 ≤ X → X ≤ Real.exp (σ*L) → X ≤ Kx*Real.exp L →
      ∀ {J J' : Type} [Fintype J] [DecidableEq J] [Fintype J'] [DecidableEq J']
      (z : MarkedMajorLabelEnergyData J cfg L X) (z' : MarkedMajorLabelEnergyData J' cfg L X),
      z'.Y=z.Y → ∀ (q : ℕ) [NeZero q], (q:ℝ) ≤ L^cfg.a → ∀ (h : ℤ) (θ : ℝ),
      |θ| ≤ cfg.Kθ*L^cfg.A₀ →
      (∀ j p,p ∈ z.allBands j → q < p) → (∀ j p,p ∈ z'.allBands j → q < p) →
      (∀ n ∈ Finset.Icc z.l z.r,z.β n ≠ 0 → ∀ p ∈ Nat.primesLE ⌊Real.exp (L^(6/25:ℝ))⌋₊,¬p∣n) →
      (∀ n ∈ Finset.Icc z'.l z'.r,z'.β n ≠ 0 → ∀ p ∈ Nat.primesLE ⌊Real.exp (L^(6/25:ℝ))⌋₊,¬p∣n) →
      ‖z.arcSource z' cutoff ψ q h θ‖ ≤ (z.Y*X)*L^(-P) := by
  have hsave : 0 ≤ P+6*cfg.a := by linarith [cfg.ha]
  filter_upwards [markedMajorLabelEnergy_source_all_log cfg σ Kx hσ cutoff hcutoff hnorm
    hlo hhi hinterval hsupp ψ hψ (P+6*cfg.a) hsave,
    markedMajor_arc_unit_scale cfg.a cfg.τ cfg.hτ,eventually_gt_atTop (0:ℝ)] with L hsource hscale hL
  intro X hX1 hupper hcomp J J' _ _ _ _ z z' hY q _ hq h θ hθ hband hband' hrough hrough'
  have hX : 0 < X := by linarith
  have he (χ : AddChar (MarkedUnitTuple q) ℂ) := hsource X hX1 hupper hcomp
    (z.characterLeft q χ θ hq hθ) (z'.characterRight q χ θ hq hθ) hY θ hθ
  rw [MarkedMajorLabelEnergyData.arcSource_expansion z z' cutoff ψ q h θ hq hθ hY
    (hq.trans hscale.1) (hscale.2.trans (z.H_lower.trans z.H_le_u))
    (hscale.2.trans (z'.H_lower.trans z'.H_le_u)) hband hband' hrough hrough']
  calc
    _ ≤ ∑ χ : AddChar (MarkedUnitTuple q) ℂ,‖markedFourierCoeff (markedResiduePhase q h) χ‖*
      ‖(z.characterLeft q χ θ hq hθ).source (z'.characterRight q χ θ hq hθ) cutoff ψ θ‖ := by
      exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul])
    _ ≤ ∑ χ : AddChar (MarkedUnitTuple q) ℂ,‖markedFourierCoeff (markedResiduePhase q h) χ‖*
      ((z.Y*X)*L^(-(P+6*cfg.a))) :=
      Finset.sum_le_sum (fun χ _ => mul_le_mul_of_nonneg_left (he χ) (norm_nonneg _))
    _ = (∑ χ : AddChar (MarkedUnitTuple q) ℂ,‖markedFourierCoeff (markedResiduePhase q h) χ‖)*
      ((z.Y*X)*L^(-(P+6*cfg.a))) := (sum_mul ..).symm
    _ ≤ (q:ℝ)^6*((z.Y*X)*L^(-(P+6*cfg.a))) :=
      mul_le_mul_of_nonneg_right (markedResiduePhase_total_norm_le q h)
        (mul_nonneg (mul_pos z.Y_pos hX).le (Real.rpow_nonneg hL.le _))
    _ ≤ _ := markedMajor_character_cost hL hq z.Y_pos.le hX.le

end ArtinMatthews

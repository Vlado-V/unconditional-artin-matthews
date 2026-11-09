module

public import ArtinMatthews.MarkedPhysicalCellRootBudget
public import ArtinMatthews.MarkedPhysicalActualPositionMoment


set_option backward.privateInPublic true
@[expose] public section

/-! The actual .21 source scale controls the cell factor for the
unchanged N=2ceil(sqrt(log x)/2), including scales below one. -/
namespace ArtinMatthews
noncomputable section

theorem markedPhysicalTypeII_cell_root_bound {x H A : ℝ}
    (hlog : 1 ≤ Real.log x) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hscale : H ≤ Real.exp (A*(Real.log x)^(21/100:ℝ))) :
    (256*H+1)^((markedMemoryMomentLength x:ℝ)⁻¹) ≤ 257*Real.exp A := by
  let H₁ := max 1 H
  have hH₁ : 1 ≤ H₁ := le_max_left _ _
  have hpos : 0 < H₁ := zero_lt_one.trans_le hH₁
  have hhi : H₁ ≤ Real.exp (A*(Real.log x)^(21/100:ℝ)) :=
    max_le (Real.one_le_exp (mul_nonneg hA (Real.rpow_nonneg (zero_le_one.trans hlog) _))) hscale
  have hl : Real.log H₁ ≤ A*(Real.log x)^(21/100:ℝ) := (Real.log_le_iff_le_exp hpos).mpr hhi
  have hn : (Real.log x)^(1/2:ℝ) ≤ (markedMemoryMomentLength x:ℝ) :=
    markedPhysicalMomentOrder_lower (Real.log x)
  have hb := markedPhysicalCell_root_budget H₁ A (Real.log x) hH₁ hA hlog hl
    (markedMemoryMomentLength x) hn
  exact (Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ 256*H+1)
    (show 256*H+1 ≤ 256*H₁+1 by have hh := le_max_right (1:ℝ) H; dsimp [H₁]; linarith)
    (inv_nonneg.mpr (Nat.cast_nonneg _))).trans hb

end
end ArtinMatthews

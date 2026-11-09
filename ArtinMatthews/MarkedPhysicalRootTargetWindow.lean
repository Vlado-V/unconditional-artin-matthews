module

public import ArtinMatthews.MarkedPhysicalTargetStrip
public import ArtinMatthews.MarkedMinorArcBanKernel


set_option backward.privateInPublic true
@[expose] public section

/-! One fixed finite target window before root averaging. The window is
independent of the root ratio; its explicit size is retained in the error. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators

def markedPhysicalRootTargetWindow (D : ℤ) (A Y : ℝ) : Finset (ℤ × ℤ) :=
  ((markedBanIntegerWindow 0 (16+|(D : ℝ)| *A*Y)).product
    (markedBanIntegerWindow 0 (|(D : ℝ)| *A*Y))).filter (fun z => D ∣ z.2)

theorem markedPhysicalRootTargetWindow_divisor (D : ℤ) (A Y : ℝ)
    (z : ℤ × ℤ) (hz : z ∈ markedPhysicalRootTargetWindow D A Y) : D ∣ z.2 :=
  (Finset.mem_filter.mp hz).2

theorem markedPhysicalRootTargetWindow_contains (D : ℤ) (A Y : ℝ)
    (z : ℤ × ℤ) {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1)
    (hD : D ∣ z.2) (hz : |markedMinorIntegerTau r z| ≤ 16)
    (hl : |((z.2/D : ℤ) : ℝ)| ≤ A*Y) : z ∈ markedPhysicalRootTargetWindow D A Y := by
  have he : z.2 = D*(z.2/D) := (Int.mul_ediv_cancel' hD).symm
  have hn : |(z.2 : ℝ)| ≤ |(D : ℝ)| *A*Y := by
    rw [he, Int.cast_mul, abs_mul]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hl (abs_nonneg (D : ℝ))
  have hm : |(z.1 : ℝ)| ≤ 16+|(D : ℝ)| *A*Y :=
    (markedPhysicalTargetStrip_first_bound z hr₀ hr₁ hz).trans (add_le_add le_rfl hn)
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨mem_markedBanIntegerWindow.mpr (by simpa only [add_zero] using hm),
      mem_markedBanIntegerWindow.mpr (by simpa only [add_zero] using hn)⟩,hD⟩

theorem markedPhysicalRootTargetWindow_card_le (D : ℤ) {A Y : ℝ}
    (hA : 0 ≤ A) (hY : 0 ≤ Y) :
    ((markedPhysicalRootTargetWindow D A Y).card : ℝ) ≤
      (33+2*|(D : ℝ)| *A*Y)*(1+2*|(D : ℝ)| *A*Y) := by
  have hB : 0 ≤ |(D : ℝ)| *A*Y := by positivity
  have hm := markedBanIntegerWindow_card_le 0 (show 0 ≤ 16+|(D : ℝ)| *A*Y by positivity)
  have hn := markedBanIntegerWindow_card_le 0 hB
  calc
    _ ≤ (((markedBanIntegerWindow 0 (16+|(D : ℝ)| *A*Y)).product
        (markedBanIntegerWindow 0 (|(D : ℝ)| *A*Y))).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_filter_le _ _)
    _ = ((markedBanIntegerWindow 0 (16+|(D : ℝ)| *A*Y)).card : ℝ)*
        ((markedBanIntegerWindow 0 (|(D : ℝ)| *A*Y)).card : ℝ) := by
      rw [Finset.product_eq_sprod, Finset.card_product, Nat.cast_mul]
    _ ≤ (2*(16+|(D : ℝ)| *A*Y)+1)*(2*(|(D : ℝ)| *A*Y)+1) :=
      mul_le_mul hm hn (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

/-- The existing actual raw-minus-major row bound applies to this fixed
window after imposing only the current target strip. -/
theorem markedPhysicalRootTargetWindow_kernel_bound (D b a : ℤ) (r : ℝ)
    (ψ : ℝ → ℂ) {Q Y A W : ℝ} (hQ : 1 ≤ Q) (hY : 1 ≤ Y)
    (hA : 0 ≤ A) (hW : 0 ≤ W) (hψ : ∀ u, ‖ψ u‖ ≤ W)
    (hsupp : ∀ u, ψ u ≠ 0 → |u| ≤ A)
    (test : (ℤ × ℤ) → ℂ) (htest : ∀ z ∈ markedPhysicalRootTargetWindow D A Y, ‖test z‖ ≤ 1) :
    (∑ z ∈ (markedPhysicalRootTargetWindow D A Y).filter
        (fun z => |markedMinorIntegerTau r z| ≤ 16),
      ‖test z*markedBanEdgeKernel ψ Q Y b a (z.2/D)‖) ≤ (33*W*(8*A+5))*Q^3 := by
  have hd : markedMinorIntegerDet ((1,0) : ℤ × ℤ) (0,1) = 1 := by
    norm_num [markedMinorIntegerDet]
  have ht : markedMinorIntegerTau r ((1,0) : ℤ × ℤ) ≠ 0 := by
    norm_num [markedMinorIntegerTau]
  have hh := markedBan_kernel_row_bound_polynomial r (1,0) (0,1) D b a hd ht
    ((markedPhysicalRootTargetWindow D A Y).filter (fun z => |markedMinorIntegerTau r z| ≤ 16))
    (fun z hz => ⟨by
      simpa only [markedMinorIntegerDet, one_mul, zero_mul, sub_zero] using
        markedPhysicalRootTargetWindow_divisor D A Y z (Finset.mem_filter.mp hz).1, by
      simpa only [markedMinorIntegerTau, Int.cast_one, Int.cast_zero, mul_zero, add_zero, div_one]
        using (Finset.mem_filter.mp hz).2⟩) ψ hQ hY hA hW hψ hsupp test
    (fun z hz => htest z (Finset.mem_filter.mp hz).1)
  simpa only [markedBanNormalizedDet, markedMinorIntegerDet, one_mul, zero_mul, sub_zero] using hh

end ArtinMatthews

module

public import ArtinMatthews.MarkedPhysicalRootTargetReindex
public import ArtinMatthews.MarkedPhysicalRootTargetWindow
public import ArtinMatthews.MarkedPhysicalRootStripGeometry


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite physical target support lies in the root-independent
window whenever the one-edge kernel is nonzero. -/

noncomputable section
namespace ArtinMatthews

theorem markedPhysicalPrimitiveBox_first_bounds {A B C D : ℝ} {z : ℤ × ℤ}
    (hz : z ∈ markedPhysicalPrimitiveBox A B C D) : A ≤ (z.1 : ℝ) ∧ (z.1 : ℝ) ≤ B := by
  exact (fixedURoot_mem_closed_interval A B z.1).mp
    (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).1

theorem markedPhysicalCanonicalRatio_mem {S : ℕ} {A B C D : ℝ}
    (hA : 1 < A) (r : MarkedPhysicalCanonicalRoot S A B C D) :
    ((markedPhysicalCanonicalCompletion r).1 : ℝ)/(markedPhysicalCanonicalRootPosition r).1 ∈ Set.Icc 0 1 := by
  change ((r.2.1).2.1 : ℝ)/(r.2.1).1 ∈ Set.Icc 0 1
  exact ((fixedURootMatrixBox_mem_ratio r.1 A B 0 1 C D hA (by norm_num) (by norm_num) r.2.1).mp r.2.2).2

theorem markedPhysicalCanonicalTarget_strip {S : ℕ} [NeZero S] {A B C D U : ℝ}
    (hA : 1 < A) (hC : 1 < C) (hU : 0 < U) (hUA : U ≤ A) (hBU : B ≤ 16*U)
    (r : MarkedPhysicalCanonicalRoot S A B C D) (Z : Finset (ℤ × ℤ))
    (hbox : Z ⊆ markedPhysicalPrimitiveBox A B C D)
    (z : ℤ × ℤ) (hz : z ∈ markedPhysicalCanonicalTargets hA hC r Z) :
    |markedMinorIntegerTau
      (((markedPhysicalCanonicalCompletion r).1 : ℝ)/(markedPhysicalCanonicalRootPosition r).1) z| ≤ 16 := by
  let w := (markedPhysicalCanonicalTargetEquiv hA hC r).symm z
  have hw : w ∈ Z := (markedPhysicalCanonicalTargets_mem hA hC r Z z).mp hz
  have hwb := markedPhysicalPrimitiveBox_first_bounds (hbox hw)
  have hrb := markedPhysicalPrimitiveBox_first_bounds (markedPhysicalCanonicalRootPosition_mem hA hC r)
  have he : markedPhysicalRootCoordinates (markedPhysicalCanonicalRootPosition r)
      (markedPhysicalCanonicalCompletion r) w=z :=
    Equiv.apply_symm_apply (markedPhysicalCanonicalTargetEquiv hA hC r) z
  rw [← he]
  exact markedPhysicalRootCoordinates_box _ _ _ (markedPhysicalCanonicalCompletion_det hA hC r)
    hU (hUA.trans hrb.1) ((zero_lt_one.trans hA).le.trans hwb.1) (hwb.2.trans hBU)

theorem markedPhysicalCanonicalTarget_window {S : ℕ} [NeZero S] {A B C D U : ℝ}
    (hA : 1 < A) (hC : 1 < C) (hU : 0 < U) (hUA : U ≤ A) (hBU : B ≤ 16*U)
    (r : MarkedPhysicalCanonicalRoot S A B C D) (Z : Finset (ℤ × ℤ))
    (hbox : Z ⊆ markedPhysicalPrimitiveBox A B C D)
    (z : ℤ × ℤ) (hz : z ∈ markedPhysicalCanonicalTargets hA hC r Z)
    (d b a : ℤ) (R Q Y : ℝ) (ψ : ℝ → ℂ) (hY : 0 < Y)
    (hsupp : ∀ v,ψ v ≠ 0 → |v| ≤ R) (hd : d ∣ z.2)
    (hk : markedBanEdgeKernel ψ Q Y b a (z.2/d) ≠ 0) :
    z ∈ markedPhysicalRootTargetWindow d R Y := by
  have hψ : ψ ((z.2/d : ℤ) / Y) ≠ 0 := by
    intro hψ
    exact hk (by simp only [markedBanEdgeKernel,hψ,zero_mul])
  have hn := hsupp _ hψ
  rw [abs_div,abs_of_pos hY] at hn
  have hnorm := (div_le_iff₀ hY).mp hn
  have hr := markedPhysicalCanonicalRatio_mem hA r
  exact markedPhysicalRootTargetWindow_contains d R Y z hr.1 hr.2 hd
    (markedPhysicalCanonicalTarget_strip hA hC hU hUA hBU r Z hbox z hz) hnorm

end ArtinMatthews

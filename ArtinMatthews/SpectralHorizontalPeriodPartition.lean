module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! A literal compact smooth partition of one horizontal period. -/
namespace ArtinMatthews
open Set Filter
open scoped Topology ContDiff
noncomputable section

def spectralHorizontalPartition (w x : ℝ) : ℝ :=
  Real.smoothTransition (x / w) - Real.smoothTransition ((x - w) / w)

theorem spectralHorizontalPartition_contDiff (w : ℝ) :
    ContDiff ℝ ∞ (spectralHorizontalPartition w) := by
  unfold spectralHorizontalPartition
  fun_prop

theorem spectralHorizontalPartition_zero_left {w x : ℝ} (hw : 0 < w) (hx : x ≤ 0) :
    spectralHorizontalPartition w x = 0 := by
  unfold spectralHorizontalPartition
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hx hw.le),
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hw.le)]
  ring

theorem spectralHorizontalPartition_zero_right {w x : ℝ} (hw : 0 < w) (hx : 2 * w ≤ x) :
    spectralHorizontalPartition w x = 0 := by
  unfold spectralHorizontalPartition
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ hw).mpr (by linarith)),
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ hw).mpr (by linarith))]
  ring

theorem spectralHorizontalPartition_tsupport {w : ℝ} (hw : 0 < w) :
    tsupport (spectralHorizontalPartition w) ⊆ Icc 0 (2 * w) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hn : spectralHorizontalPartition w x ≠ 0 := hx
  constructor
  · by_contra h
    exact hn (spectralHorizontalPartition_zero_left hw (le_of_not_ge h))
  · by_contra h
    exact hn (spectralHorizontalPartition_zero_right hw (le_of_not_ge h))

theorem spectralHorizontalPartition_hasCompactSupport {w : ℝ} (hw : 0 < w) :
    HasCompactSupport (spectralHorizontalPartition w) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (spectralHorizontalPartition_tsupport hw)

theorem spectralHorizontalPartition_add_shift {w x : ℝ} (hw : 0 < w)
    (hx : x ∈ Icc 0 w) :
    spectralHorizontalPartition w x + spectralHorizontalPartition w (x + w) = 1 := by
  unfold spectralHorizontalPartition
  have hz : Real.smoothTransition ((x - w) / w) = 0 :=
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith [hx.2]) hw.le)
  have ho : Real.smoothTransition ((x + w) / w) = 1 :=
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ hw).mpr (by linarith [hx.1]))
  rw [hz, ho,
    show x + w - w = x by ring]
  ring

theorem spectralHorizontalPartition_deriv_add_shift {w x : ℝ} (hw : 0 < w)
    (hx : x ∈ Ioo 0 w) :
    deriv (spectralHorizontalPartition w) x + deriv (spectralHorizontalPartition w) (x + w) = 0 := by
  have heq : (fun t => spectralHorizontalPartition w t + spectralHorizontalPartition w (t + w))
      =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    exact spectralHorizontalPartition_add_shift hw ⟨ht.1.le, ht.2.le⟩
  have hd := (spectralHorizontalPartition_contDiff w).differentiable (by simp)
  have hs : DifferentiableAt ℝ (fun t => spectralHorizontalPartition w (t + w)) x :=
    (hd (x + w)).comp x (differentiableAt_id.add_const w)
  simpa only [deriv_fun_add (hd x) hs, deriv_comp_add_const, deriv_const] using heq.deriv_eq

theorem spectralHorizontalPartition_deriv2_add_shift {w x : ℝ} (hw : 0 < w)
    (hx : x ∈ Ioo 0 w) :
    deriv (deriv (spectralHorizontalPartition w)) x +
      deriv (deriv (spectralHorizontalPartition w)) (x + w) = 0 := by
  have heq : (fun t => deriv (spectralHorizontalPartition w) t +
      deriv (spectralHorizontalPartition w) (t + w)) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    exact spectralHorizontalPartition_deriv_add_shift hw ht
  have hd := (contDiff_infty_iff_deriv.mp (spectralHorizontalPartition_contDiff w)).2.differentiable
    (by simp)
  have hs : DifferentiableAt ℝ (fun t => deriv (spectralHorizontalPartition w) (t + w)) x :=
    (hd (x + w)).comp x (differentiableAt_id.add_const w)
  simpa only [deriv_fun_add (hd x) hs, deriv_comp_add_const, deriv_const] using heq.deriv_eq

end
end ArtinMatthews

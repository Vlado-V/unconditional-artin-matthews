module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import ArtinMatthews.SpectralPositiveTestPrimitive
public import Mathlib.Analysis.Calculus.ContDiff.Operations
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


set_option backward.privateInPublic true
@[expose] public section

/-! Division by height preserves genuine smooth compact tests whose support
lies in the positive half-line. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace ArtinMatthews

theorem spectralPositiveTest_div_pow_contDiff (ρ : ℝ → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hs : tsupport ρ ⊆ Ioi (0 : ℝ)) (k : ℕ) :
    ContDiff ℝ ∞ (fun y => ρ y / y ^ k) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y = 0
  · subst y
    have hzero : (0 : ℝ) ∉ tsupport ρ := fun h =>
      lt_irrefl (0 : ℝ) (show (0 : ℝ) < 0 from hs h)
    have he : (fun y => ρ y / y ^ k) =ᶠ[𝓝 (0 : ℝ)] 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hzero] with y hy
      simp only [hy, zero_div, Pi.zero_apply]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hρy : ContDiffAt ℝ ∞ ρ y := hρ.contDiffAt
    exact hρy.div (contDiffAt_id.pow k) (pow_ne_zero k hy)

theorem spectralPositiveTest_div_pow_tsupport (ρ : ℝ → ℝ) (k : ℕ) :
    tsupport (fun y => ρ y / y ^ k) ⊆ tsupport ρ := by
  simpa only [div_eq_mul_inv] using
    (tsupport_mul_subset_left (f := ρ) (g := fun y => (y ^ k)⁻¹))

theorem spectralPositiveTest_div_pow_compact (ρ : ℝ → ℝ)
    (hρc : HasCompactSupport ρ) (k : ℕ) :
    HasCompactSupport (fun y => ρ y / y ^ k) :=
  hρc.of_isClosed_subset (isClosed_tsupport _) (spectralPositiveTest_div_pow_tsupport ρ k)

theorem spectralPositiveTest_exists_height (ρ : ℝ → ℝ)
    (hρc : HasCompactSupport ρ) (hs : tsupport ρ ⊆ Ioi (0 : ℝ)) :
    ∃ Y : ℝ, 0 < Y ∧ tsupport ρ ⊆ Ioi Y := by
  obtain ⟨a, b, ha, _, _, hab⟩ := spectralPositiveTest_support_enclosure ρ hρc hs
  exact ⟨a, ha, fun _ hx => (hab hx).1⟩

end ArtinMatthews

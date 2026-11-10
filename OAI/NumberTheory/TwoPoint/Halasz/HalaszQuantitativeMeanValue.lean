module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.TwoPoint.Halasz.HalaszClassicalDefect
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import OAI.NumberTheory.TwoPoint.Halasz.HalaszConstantGrowth
public import OAI.NumberTheory.TwoPoint.Halasz.HalaszSmallDefect


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-! The one quantitative complete-system estimate used by the subsequent
logarithmic phase argument. Both the defect and the constant are explicit. -/
namespace TwoPointCorrelations

theorem halasz_quantitative_mean_value : ∃ R₀ : ℕ, ∀ k : ℕ, 2≤k →
    ∀ N : ℕ, 1≤N →
    (halaszVinogradovCount ((10*k+1)*k) k N:ℝ) ≤
      (R₀+k+32:ℝ)^(256*k^4)*
        (N:ℝ)^(2*(((10*k+1)*k:ℕ):ℝ)-(halaszTotalDegree k:ℝ)+(k:ℝ)^2/2048) := by
  obtain ⟨R₀,hmean⟩ := halasz_classical_selected_moment
  refine ⟨R₀,?_⟩
  intro k hk N hN
  apply (hmean k hk N hN).trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  exact_mod_cast halasz_selected_constant_growth (R₀ := R₀) hk

end TwoPointCorrelations

end OAI

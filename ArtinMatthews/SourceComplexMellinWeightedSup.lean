module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import ArtinMatthews.SourceComplexMellinSchwartzScale
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
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

namespace ArtinMatthews.VaryingKummerAnalytic
open scoped SchwartzMap
noncomputable section

/-- The normalized power of one complex coordinate can be bounded pointwise,
including after bounded logarithmic shifts. This supplies the chosen-place
estimate in the norm-one sheet integral. -/
theorem sourceComplexSchwartz_weighted_dilate_sup (g : 𝓢(ℂ, ℂ)) (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ), -1 ≤ t → ∀ z : ℂ,
      ‖g (Real.exp t • z)‖ * (‖z‖ ^ 2) ^ σ ≤ C := by
  let k := Nat.ceil (2 * σ)
  obtain ⟨C, hC, hdecay⟩ := sourceComplexSchwartz_exp_smul_norm_le g k
  refine ⟨C, hC, ?_⟩
  intro t ht z
  have hp : (‖z‖ ^ 2) ^ σ ≤ (1 + ‖z‖) ^ k := by
    rw [← Real.rpow_natCast_mul (norm_nonneg _) 2 σ, ← Real.rpow_natCast]
    refine (Real.rpow_le_rpow (norm_nonneg _) (le_add_of_nonneg_left zero_le_one) (by positivity)).trans ?_
    exact Real.rpow_le_rpow_of_exponent_le (by simp) (Nat.le_ceil (2 * σ))
  calc
    _ ≤ (C * (1 + ‖z‖) ^ (-(k : ℝ))) * (1 + ‖z‖) ^ k :=
      mul_le_mul (hdecay t ht z) hp (by positivity) (by positivity)
    _ = C := by
      rw [mul_assoc, ← Real.rpow_natCast (1 + ‖z‖) k,
        ← Real.rpow_add (by positivity), neg_add_cancel, Real.rpow_zero, mul_one]

end
end ArtinMatthews.VaryingKummerAnalytic

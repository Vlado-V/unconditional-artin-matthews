module

public import ArtinMatthews.ShiftedDualZeroEnergy
public import ArtinMatthews.ShiftedConvolutionCoefficients
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! The congruence-constrained coefficient at zero has no multiplicity loss.
The modulus condition can only reduce its absolute majorant. -/

noncomputable section
open scoped BigOperators
namespace ArtinMatthews

theorem shiftedConvolutionCoeff_zero_majorant (S T : Finset ℕ) (m3 m4 D : ℕ)
    (a b : ℕ → ℂ) :
    ‖shiftedConvolutionCoeff S T m3 m4 D a b 0‖ ≤
      ∑ k ∈ shiftedDualZeroPairs S T m3 m4, ‖a k.1 * b k.2‖ := by
  classical
  have heq : shiftedConvolutionCoeff S T m3 m4 D a b 0 =
      ∑ k ∈ shiftedDualZeroPairs S T m3 m4,
        if (m3^2 * k.1 : ZMod D) = (m4^2 * k.2 : ZMod D) then a k.1 * b k.2 else 0 := by
    simp only [shiftedConvolutionCoeff, shiftedDualZeroPairs, Finset.sum_filter,
      Finset.sum_product, sub_eq_zero, ← Nat.cast_mul, Nat.cast_inj, ite_and]
  rw [heq]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  split_ifs
  · exact le_rfl
  · simp only [norm_zero]
    exact norm_nonneg _

theorem shiftedConvolutionCoeff_zero_energy (S T : Finset ℕ) (m3 m4 D : ℕ)
    (hm3 : 0 < m3) (hm4 : 0 < m4) (a b : ℕ → ℂ) :
    ‖shiftedConvolutionCoeff S T m3 m4 D a b 0‖^2 ≤
      (∑ k ∈ S, ‖a k‖^2) * (∑ k ∈ T, ‖b k‖^2) :=
  (pow_le_pow_left₀ (norm_nonneg _) (shiftedConvolutionCoeff_zero_majorant S T m3 m4 D a b) 2).trans
    (shiftedDualZero_energy_bound S T m3 m4 hm3 hm4 a b)

end ArtinMatthews

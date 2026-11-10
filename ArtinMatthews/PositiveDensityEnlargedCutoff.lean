module

public import ArtinMatthews.PositiveDensityCandidateCRT
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
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

/-! Choose the integer cutoff after the uniform splitting constant, using
the exact density of the actual enlarged progression. -/

noncomputable section
namespace ArtinMatthews

open scoped BigOperators

theorem giantSieve_enlarged_units_density {S : Finset ℤ} {u r₃ : ℕ}
    (hprog : IsQuadraticProgressionFor S u r₃) (Y : ℕ) :
    ((giantSieveEnlargedUnits hprog Y).card : ℝ) /
        Nat.totient (enlargedModulus (quadraticModulus S) (giantSieveNewPrimes S Y)) =
      (1 / (Nat.totient (quadraticModulus S) : ℝ)) *
        progressionDensityProduct (giantSieveNewPrimes S Y) := by
  let : NeZero (enlargedModulus (quadraticModulus S) (giantSieveNewPrimes S Y)) :=
    ⟨(giantSieveEnlargedModulus_pos S Y).ne'⟩
  exact enlargedProgressionUnits_density (giantSieveNewPrimes_data S Y)
    (ZMod.unitOfCoprime u hprog.2.1)

theorem giantSieve_exists_enlarged_cutoff {S : Finset ℤ} {u r₃ : ℕ}
    (hprog : IsQuadraticProgressionFor S u r₃)
    {B K : ℝ} (hB : 0 ≤ B) (hK : 0 < K) :
    ∃ Y : ℕ, 3 ≤ Y ∧ (∀ a ∈ S, a.natAbs ≤ Y) ∧
      B / (Y : ℝ) < K * (((giantSieveEnlargedUnits hprog Y).card : ℝ) /
        Nat.totient (enlargedModulus (quadraticModulus S) (giantSieveNewPrimes S Y))) := by
  let H := ∑ a ∈ S, a.natAbs
  let Y₀ := max 3 H
  let P := fun T : ℝ => giantSieveNewPrimes S ⌊T⌋₊
  have h₀ : 0 < quadraticModulus S :=
    Nat.mul_pos (by decide) (Finset.prod_pos fun _ hq => (quadraticPrimeSupport_prime hq).1.pos)
  have hφ : (0 : ℝ) < Nat.totient (quadraticModulus S) := by
    exact_mod_cast Nat.totient_pos.mpr h₀
  obtain ⟨T, hT, hT₁, hgap⟩ := exists_cutoff_for_progressionDensityProduct P
    (fun _ => Finset.filter_subset _ _)
    (fun T p hp => (giantSieveNewPrimes_data S ⌊T⌋₊ p hp).2.1)
    (2 * B) ((Y₀ : ℝ) + 1) (div_pos hK hφ)
  let Y := ⌊T⌋₊
  have hY₀ : Y₀ ≤ Y := Nat.le_floor (by linarith)
  have hY₃ : 3 ≤ Y := (le_max_left _ _).trans hY₀
  refine ⟨Y, hY₃, fun a ha => ?_, ?_⟩
  · have haH : a.natAbs ≤ H := Finset.single_le_sum (fun _ _ => Nat.zero_le _) ha
    exact haH.trans ((le_max_right _ _).trans hY₀)
  · have hmin : (3 : ℝ) ≤ Y₀ := by exact_mod_cast (le_max_left 3 H)
    have hYge : T / 2 ≤ (Y : ℝ) := by linarith [Nat.sub_one_lt_floor T]
    have hBT : B / (Y : ℝ) ≤ (2 * B) / T := by
      calc
        _ ≤ B / (T / 2) := div_le_div_of_nonneg_left hB (by positivity) hYge
        _ = _ := by ring
    rw [giantSieve_enlarged_units_density]
    apply lt_of_le_of_lt hBT
    simpa only [P, Y, div_eq_mul_inv, one_mul, mul_assoc] using hgap

end ArtinMatthews

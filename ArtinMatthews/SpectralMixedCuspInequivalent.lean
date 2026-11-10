module

public import ArtinMatthews.SpectralCuspEisensteinWidthFormula
public import ArtinMatthews.SpectralMixedCuspNormalization
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The cusps in the shifted-correlation application are genuinely
inequivalent as soon as the left coprime factor exceeds one. -/

noncomputable section
open Matrix
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0MixedCusps_inequivalent_of_one_lt (r s : ℕ) [NeZero s]
    (hr : 1 < r) :
    ¬ gamma0EisensteinCuspsEquivalent (r*s) (gamma0CuspOneOver s) 1 := by
  intro h
  obtain ⟨M, hC⟩ := (gamma0EisensteinCuspsEquivalent_iff (r*s) (gamma0CuspOneOver s) 1).mp h
  obtain ⟨k, hk⟩ := (gamma0MixedCuspCorrespondence_iff r s M.val).mp M.property
  rw [hC, zero_sub] at hk
  have hs : (s : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne s
  have hD : (r : ℤ) ∣ M.val 1 1 := by
    refine ⟨-k, ?_⟩
    apply mul_left_cancel₀ hs
    linear_combination -hk
  have hdet : M.val 0 0 * M.val 1 1 = 1 := by
    have h := M.val.property
    rwa [Matrix.det_fin_two, hC, mul_zero, sub_zero] at h
  have hd : (r : ℤ) ∣ 1 := hdet ▸ dvd_mul_of_dvd_right hD (M.val 0 0)
  have hd' : r ∣ 1 := by exact_mod_cast hd
  exact (not_le_of_gt hr) (Nat.le_of_dvd zero_lt_one hd')

end ArtinMatthews

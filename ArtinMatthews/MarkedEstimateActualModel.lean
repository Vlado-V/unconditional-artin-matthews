module

public import ArtinMatthews.MarkedEstimateVariance
public import ArtinMatthews.MarkedEstimateMertensBandCore
public import ArtinMatthews.MarkedEstimateMertensBands
public import Mathlib.NumberTheory.Chebyshev
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-!
# Uniform moments for the actual marking bands

This combines the exact closed-band Mertens theorem with the finite
independent-model computations. The resulting constants depend only on
the number of bands, not on their particular fixed positive exponents.
-/

namespace ArtinMatthews

open Filter

/-- Distinct exponents give mutually disjoint marking bands eventually. -/
theorem marked_array_disjoint_eventually {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : Function.Injective a) :
    ∀ᶠ x : ℝ in atTop,
      Pairwise (fun i j => Disjoint (markedLogPowerBand (a i) x) (markedLogPowerBand (a j) x)) := by
  have hpair (i j : ι) : ∀ᶠ x : ℝ in atTop, i ≠ j →
      Disjoint (markedLogPowerBand (a i) x) (markedLogPowerBand (a j) x) := by
    by_cases hij : i = j
    · simp [hij]
    · have hne : a i ≠ a j := fun h => hij (ha h)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · filter_upwards [markedLogPowerBand_disjoint_eventually hlt] with x hx
        exact fun _ => hx
      · filter_upwards [markedLogPowerBand_disjoint_eventually hgt] with x hx
        exact fun _ => hx.symm
  exact eventually_all.mpr (fun i => eventually_all.mpr (hpair i))

/-- The exact uniform independent-model moment bounds (2.3) for all fixed
finite collections of admissible marking exponents. -/
theorem marked_array_moment_bounds_eventually {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    ∀ᶠ x : ℝ in atTop,
      let P := fun i => markedLogPowerBand (a i) x
      let V := fun i => bandReciprocalMass (P i)
      (1 / 2 : ℝ) ^ Fintype.card ι ≤ independentArrayMean P V ∧
      independentArrayMean P V ≤ (1 / (Real.log 2 / 2)) ^ Fintype.card ι ∧
      independentArraySecondMoment P V ≤ ((1 / (Real.log 2 / 2)) ^ 2) ^ Fintype.card ι := by
  have hm : ∀ᶠ x : ℝ in atTop, ∀ i,
      Real.log 2 / 2 < bandReciprocalMass (markedLogPowerBand (a i) x) ∧
      bandReciprocalMass (markedLogPowerBand (a i) x) < 1 :=
    eventually_all.mpr (fun i => marked_log_power_band_mass_eventually (ha i))
  filter_upwards [hm] with x hx
  exact independentArray_moment_bounds (fun i => markedLogPowerBand (a i) x)
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
    (by positivity : 0 < Real.log 2 / 2)
    (fun i => (hx i).1.le) (fun i => (hx i).2.le)

/-- A concrete variance constant depending only on the number of bands. -/
noncomputable def markedArrayVarianceConstant (K : ℕ) : ℝ :=
  (((1 / (Real.log 2 / 2)) ^ 2) ^ K) / (((1 / 2 : ℝ) ^ K) ^ 2)

theorem markedArrayVarianceConstant_pos (K : ℕ) :
    0 < markedArrayVarianceConstant K := by
  unfold markedArrayVarianceConstant
  positivity

/-- Equation (2.8) for the actual disjoint marking bands. The variance
constant is independent of the number of arrays and of all fixed band
exponents; only the threshold for `x` may depend on those choices. -/
theorem marked_arrays_variance_eventually {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (a : J → I → ℝ) (ha : ∀ j i, 0 < a j i)
    (hdistinct : Function.Injective (fun ji : J × I => a ji.1 ji.2))
    (hJ : 0 < Fintype.card J) :
    ∀ᶠ x : ℝ in atTop,
      Pairwise (fun ji ki : J × I =>
        Disjoint (markedLogPowerBand (a ji.1 ji.2) x) (markedLogPowerBand (a ki.1 ki.2) x)) ∧
      independentArraysVariance
        (fun j i => markedLogPowerBand (a j i) x)
        (fun j i => bandReciprocalMass (markedLogPowerBand (a j i) x)) ≤
          markedArrayVarianceConstant (Fintype.card I) / Fintype.card J := by
  have hall := eventually_all.mpr (fun j => marked_array_moment_bounds_eventually (a j) (ha j))
  filter_upwards [hall, marked_array_disjoint_eventually
    (fun ji : J × I => a ji.1 ji.2) hdistinct] with x hx hdisjoint
  refine ⟨hdisjoint, ?_⟩
  exact independentArraysVariance_le_of_moment_bounds _ _ hJ
    (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ Fintype.card I)
    (by positivity : (0 : ℝ) ≤ ((1 / (Real.log 2 / 2)) ^ 2) ^ Fintype.card I)
    (fun j => (hx j).1) (fun j => (hx j).2.2)

end ArtinMatthews

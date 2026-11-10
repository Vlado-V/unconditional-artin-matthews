module

public import ArtinMatthews.CubicSieveJointEuler
public import ArtinMatthews.CubicSamplingSourceTruncation
public import ArtinMatthews.CubicSieveSourceModelDecay
public import ArtinMatthews.MarkedEstimateArrayModel
public import ArtinMatthews.CubicSieveArrayDensityCompare
public import ArtinMatthews.CubicSieveMarkingEnvelope
public import ArtinMatthews.MarkedArrayBandStructure
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! The literal marking bands approximate their true mean, uniformly in
all original squarefree sieve divisors of a fixed polynomial size. -/

noncomputable section
namespace ArtinMatthews

open Filter Finset
open scoped BigOperators Topology

theorem cubicSieve_actualArrayEuler_envelope {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, 0 < e j ∧ e j ≤ 1 / 5) (hinj : Function.Injective e)
    {α c : ℝ} (heα : ∀ j, α ≤ e j) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      let P := fun j => markedLogPowerBand (e j) x
      let V := fun j => bandReciprocalMass (P j)
      let k := cubicSamplingTruncationDepth x
      ∀ r : ℕ, 0 < r → (r : ℝ) ≤ x ^ c →
        |cubicSieveFirstArrayEulerSum P V k r 1 - independentArrayMean P V| ≤
          C * cubicSieveSourceModelEnvelope α x ∧
        |deriv (cubicSieveFirstArrayEulerSum P V k r) 1| ≤
          C * cubicSieveSourceModelEnvelope α x := by
  let v := Real.log 2 / 2
  let M : ℝ := Fintype.card J
  let A := 2 * Real.exp (8 * M) + (1 / v + 1 / 2) * M + (1 / v + 1 / 2) * c / Real.log (3 / 2 : ℝ)
  let B := 16 * (M + 1) * Real.exp (8 * M) + 4 * (1 / v + 1 / 2) * M
  let C := 1 + A + B
  have hv : 0 < v := by dsimp only [v]; positivity
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  have hb := marked_actual_band_structure_eventually e (fun j => (he j).1) hinj
    heα (fun j => (he j).2)
  filter_upwards [hb, Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with x hxBand hL₁ hx₁
  dsimp only
  intro r hr hrc
  let P := fun j => markedLogPowerBand (e j) x
  let V := fun j => bandReciprocalMass (P j)
  let k := cubicSamplingTruncationDepth x
  let L := Real.log x
  let y := Real.exp (L ^ α)
  let Z := Real.exp (2 * L ^ (1 / 5 : ℝ))
  let q := (1 / 4 : ℝ) ^ k
  have hL : 0 < L := Real.log_pos hx₁
  have hy : 0 < y := Real.exp_pos _
  have hZ : 1 ≤ Z := Real.one_le_exp (by positivity)
  have hq : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hlogZ : 0 ≤ Real.log Z := Real.log_nonneg hZ
  have hZL : Real.log Z ≤ 2 * L := by
    dsimp only [Z]
    rw [Real.log_exp]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL₁ (by norm_num : (1 / 5 : ℝ) ≤ 1))
      (by norm_num)
  have hPr (j : J) (p : ℕ) (hp : p ∈ P j) := (hxBand.2.1 j p hp).1
  have hmin (j : J) (p : ℕ) (hp : p ∈ P j) := (hxBand.2.1 j p hp).2.1
  have hmax (j : J) (p : ℕ) (hp : p ∈ P j) := (hxBand.2.1 j p hp).2.2
  have hE : 0 ≤ cubicSieveSourceModelEnvelope α x := by
    dsimp only [cubicSieveSourceModelEnvelope]
    positivity
  have hlogr : Real.log (r : ℝ) ≤ c * L := by
    have h := Real.log_le_log (by exact_mod_cast hr) hrc
    rw [Real.log_rpow (zero_lt_one.trans hx₁)] at h
    exact h
  have hval := cubicSieve_firstArray_restricted_value_error P hPr hxBand.1 hv hy hM
    hxBand.2.2.1 hmin hxBand.2.2.2 hr k
  rw [← cubicSieve_firstArrayEulerSum_eq_model P V hPr] at hval
  have hval' : |cubicSieveFirstArrayEulerSum P V k r 1 - independentArrayMean P V| ≤
      A * cubicSieveSourceModelEnvelope α x := by
    refine hval.trans (le_trans ?_ (cubicSieve_marking_value_envelope hL.le hy hq hM hv hc))
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add le_rfl (div_le_div_of_nonneg_right hlogr (by positivity))
  have ht := cubicSieve_firstArray_restricted_tangent_error P hPr hxBand.1 hv hy hZ hM
    hxBand.2.2.1 hmin hmax hxBand.2.2.2 r k
  have htan : |deriv (cubicSieveFirstArrayEulerSum P V k r) 1| ≤
      B * cubicSieveSourceModelEnvelope α x := by
    rw [(cubicSieve_firstArrayEulerSum_hasDerivAt_one P V hPr k r).deriv]
    exact ht.trans (cubicSieve_marking_tangent_envelope hy hq hq1 hM hv hM hlogZ hZL)
  exact ⟨hval'.trans (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) hE),
    htan.trans (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) hE)⟩

end ArtinMatthews

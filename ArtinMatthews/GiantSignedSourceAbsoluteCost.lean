module

public import ArtinMatthews.GiantSignedRawEdgeEnergy
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The source absolute-edge cost is polynomial in L, with an exponent
fixed independently of the copied-slot count. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedSmallRowBudget_exists {q vmin : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hvmin : 0 < vmin) (ell : ℕ) :
    ∃ BS : ℝ, 0 ≤ BS ∧ ∀ V : ℝ, vmin ≤ V → ∀ z : ℕ,
      V⁻¹ ^ ell * ((z : ℝ) + (ell : ℝ)) ^ ell * q ^ ((z : ℝ) / 2) ≤ BS := by
  let r := Real.sqrt q
  have hr : 0 < r := Real.sqrt_pos.2 hq
  have hr1 : r < 1 := by
    dsimp [r]
    nlinarith [Real.sq_sqrt hq.le, Real.sqrt_nonneg q]
  have hnorm : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_pos hr]
  let T := ∑' n : ℕ, (n : ℝ)^ell * r^n
  have hT0 : 0 ≤ T := tsum_nonneg fun _ => by positivity
  have hT := summable_pow_mul_geometric_of_norm_lt_one ell hnorm
  refine ⟨vmin⁻¹ ^ ell * (T / r ^ ell), by positivity, ?_⟩
  intro V hV z
  have hqpow : q ^ ((z : ℝ) / 2) = r ^ z := by
    rw [show r = q ^ (1/2 : ℝ) from Real.sqrt_eq_rpow q, ← Real.rpow_mul_natCast hq.le]
    congr 1
    ring
  have hterm : (((z + ell : ℕ) : ℝ) ^ ell) * r ^ (z + ell) ≤ T := by
    simpa only [Finset.sum_singleton] using
      sum_le_hasSum ({z + ell} : Finset ℕ) (fun n _ =>
        mul_nonneg (pow_nonneg (Nat.cast_nonneg n) _) (pow_nonneg hr.le _)) hT.hasSum
  rw [Nat.cast_add, pow_add, ← mul_assoc] at hterm
  have hterm' := (le_div_iff₀ (pow_pos hr ell)).mpr hterm
  have hV0 := lt_of_lt_of_le hvmin hV
  have hi : V⁻¹ ≤ vmin⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le hvmin hV
  rw [hqpow, mul_assoc]
  exact mul_le_mul (pow_le_pow_left₀ (inv_nonneg.mpr hV0.le) hi ell) hterm'
    (by positivity) (by positivity)

private theorem pow_le_source_group_cost {L C₀ b : ℝ} {n : ℕ}
    (hL : 0 < L) (hb : 0 ≤ b) (hn : (n : ℝ) ≤ C₀ * Real.log L) :
    b ^ n ≤ L ^ (C₀ * Real.log (max 1 b)) := by
  let R := max 1 b
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  calc
    _ ≤ R ^ n := pow_le_pow_left₀ hb (le_max_right _ _) _
    _ = Real.exp (Real.log R * (n : ℝ)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hR]
    _ ≤ Real.exp (Real.log L * (C₀ * Real.log R)) := by
      apply Real.exp_le_exp.mpr
      calc
        _ = (n : ℝ) * Real.log R := mul_comm _ _
        _ ≤ (C₀ * Real.log L) * Real.log R := mul_le_mul_of_nonneg_right hn (Real.log_nonneg hR1)
        _ = _ := by ring
    _ = _ := (Real.rpow_def_of_pos hL _).symm

def giantSignedSourceAbsoluteExponent (C₀ C₁ BS ρ v vmin vmax massMax : ℝ) (tmax : ℕ) : ℝ :=
  C₁ + C₀ * Real.log (max 1 BS) + (C₀ / 2) *
    Real.log (max 1 (giantSignedEdgeEnergyConstant ρ v vmin vmax massMax tmax))

theorem giantSignedSourceAbsoluteEnergyConstant_le
    {L C₀ C₁ W BS ρ v vmin vmax massMax : ℝ} (nS nB tmax : ℕ)
    (hL : 0 < L) (hW : 0 ≤ W) (hWcost : W ≤ L ^ C₁) (hBS : 0 ≤ BS)
    (hS : (nS : ℝ) ≤ C₀ * Real.log L) (hB : (nB : ℝ) ≤ C₀ * Real.log L) :
    giantSignedRawEdgeEnergyConstant W BS nS nB ρ v vmin vmax massMax tmax ≤
      L ^ (2 * giantSignedSourceAbsoluteExponent C₀ C₁ BS ρ v vmin vmax massMax tmax) := by
  let E := giantSignedEdgeEnergyConstant ρ v vmin vmax massMax tmax
  have hE : 0 ≤ E := mul_nonneg (giantSignedEdgeReverseConstant_nonneg _ _ _) (sq_nonneg _)
  have hsmall := pow_le_source_group_cost hL hBS hS
  have hbig := pow_le_source_group_cost hL hE hB
  unfold giantSignedRawEdgeEnergyConstant
  calc
    _ ≤ (L ^ C₁) ^ 2 * ((L ^ (C₀ * Real.log (max 1 BS))) ^ 2 *
        L ^ (C₀ * Real.log (max 1 E))) :=
      mul_le_mul (pow_le_pow_left₀ hW hWcost 2)
        (mul_le_mul (pow_le_pow_left₀ (pow_nonneg hBS _) hsmall 2) hbig
          (pow_nonneg hE _) (sq_nonneg _)) (mul_nonneg (sq_nonneg _) (pow_nonneg hE _)) (sq_nonneg _)
    _ = _ := by
      simp only [← Real.rpow_mul_natCast hL.le, ← Real.rpow_add hL]
      congr 1
      unfold giantSignedSourceAbsoluteExponent E
      norm_num
      ring

end
end ArtinMatthews

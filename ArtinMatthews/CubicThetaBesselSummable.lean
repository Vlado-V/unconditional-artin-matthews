module

public import ArtinMatthews.CubicThetaBesselSquareAll
public import ArtinMatthews.ShiftedBesselScale
public import ArtinMatthews.ShiftedReciprocalSquare
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute convergence of the actual ideal-theta Bessel coefficients.
This uses their proved polynomial bound and the third-order Bessel decay,
independently of the remaining modular transformation law. -/

noncomputable section
open Set OAI
namespace ArtinMatthews

theorem thetaBesselCoeff_summable (χ : SevenEighths.HeckeFamily.Character)
    (W : SchwartzMap ℝ ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hW : Function.support W ⊆ Icc 0 B)
    (K Q : ℝ) (hK : 0 < K) (hQ : 0 < Q) :
    Summable (thetaBesselCoeff χ W K Q) := by
  obtain ⟨s, C, hC, hdecay⟩ := weightOneBesselTransform_dilate_euler_source_bound 3 0
  let S : ℝ := Q / K
  let E : ℝ := s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let V : ℝ := C * K * E
  have hS : 0 < S := div_pos hQ hK
  have hE : 0 ≤ E := apply_nonneg (s.sup (schwartzSeminormFamily ℝ ℝ ℂ)) W
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hmajor (n : ℕ) : ‖thetaBesselCoeff χ W K Q (n + 1)‖ ≤
      (128 * S * V) * (1 / (1 + ((n + 1 : ℕ) : ℝ) / S)^2) := by
    let t : ℝ := 1 + ((n + 1 : ℕ) : ℝ) / S
    have ht : 0 < t := by dsimp [t]; positivity
    have hn : ((n + 1 : ℕ) : ℝ) ≤ S * t := by
      dsimp [t]
      field_simp
      nlinarith
    have ha : ‖idealThetaCoeff χ (n + 1)‖ ≤ 128 * ((n + 1 : ℕ) : ℝ) := by
      have ha := idealThetaCoeff_norm_le χ (n + 1)
      push_cast at ha ⊢
      nlinarith
    have hd : t^3 * ‖weightOneBesselTransform (fun x => W (x / K))
        (((n + 1 : ℕ) : ℝ) / Q)‖ ≤ V := by
      have hd := hdecay W B hB hW K (((n + 1 : ℕ) : ℝ) / Q) hK (by positivity) 0 le_rfl
      have heq : K * (((n + 1 : ℕ) : ℝ) / Q) = ((n + 1 : ℕ) : ℝ) / S := by
        dsimp [S]
        field_simp
      simpa only [LocalLogFourier.eulerDeriv, iteratedDeriv_zero,
        Real.exp_zero, mul_one, heq] using hd
    rw [mul_one_div]
    apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
    rw [thetaBesselCoeff, norm_mul]
    calc
      _ ≤ (128 * (S * t)) *
          ‖weightOneBesselTransform (fun x => W (x / K)) (((n + 1 : ℕ) : ℝ) / Q)‖ * t^2 := by
        gcongr
        exact ha.trans (by gcongr)
      _ = (128 * S) * (t^3 *
          ‖weightOneBesselTransform (fun x => W (x / K)) (((n + 1 : ℕ) : ℝ) / Q)‖) := by ring
      _ ≤ 128 * S * V := mul_le_mul_of_nonneg_left hd (by positivity)
  have hs := ((shifted_reciprocal_square_sum S hS).1.mul_left (128 * S * V))
  have hnorm : Summable (fun n : ℕ => ‖thetaBesselCoeff χ W K Q (n + 1)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hmajor hs
  exact (summable_nat_add_iff 1).mp hnorm.of_norm

end ArtinMatthews

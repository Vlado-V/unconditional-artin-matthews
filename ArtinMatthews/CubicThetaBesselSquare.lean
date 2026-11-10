module

public import Mathlib.Algebra.Lie.OfAssociative
public import ArtinMatthews.CubicThetaCoefficients
public import ArtinMatthews.ShiftedVoronoiBesselTransform
public import ArtinMatthews.CubicThetaMeanSquare
public import ArtinMatthews.ShiftedBesselScale
public import ArtinMatthews.ShiftedWeightedSquare
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

/-! Actual ideal-theta coefficients satisfy a square-sum bound at the true
Bessel scale, uniformly in the character and source dilation. -/

noncomputable section
open Set OAI
namespace ArtinMatthews

theorem idealTheta_weighted_square (ε : ℝ) (hε : 0 < ε) (hεtwo : ε ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : SevenEighths.HeckeFamily.Character)
      (S B : ℝ), 0 < S → 0 ≤ B → ∀ b : ℕ → ℂ,
      (∀ n : ℕ, (1 + ((n + 1 : ℕ) : ℝ) / S)^2 * ‖b (n + 1)‖ ≤ B) →
      Summable (fun n : ℕ => ‖idealThetaCoeff χ (n + 1) * b (n + 1)‖^2) ∧
      (∑' n : ℕ, ‖idealThetaCoeff χ (n + 1) * b (n + 1)‖^2) ≤ C * B^2 * S^(1 + ε) := by
  obtain ⟨C, hC, hcoeff⟩ := idealThetaCoeff_square_subpower ε hε
  refine ⟨C, hC, ?_⟩
  intro χ S B hS hB b hb
  exact shifted_weighted_square_sum ε S C B hε hεtwo hS hC.le hB
    (idealThetaCoeff χ) b (fun n => hcoeff χ (n + 1)) hb

theorem idealTheta_bessel_square_uniform (ε : ℝ) (hε : 0 < ε) (hεtwo : ε ≤ 2) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (χ : SevenEighths.HeckeFamily.Character) (W : SchwartzMap ℝ ℂ)
        (B : ℝ), 0 ≤ B → Function.support W ⊆ Icc 0 B →
      ∀ (K Q : ℝ), 0 < K → 0 < Q →
      Summable (fun n : ℕ => ‖idealThetaCoeff χ (n + 1) *
        weightOneBesselTransform (fun x => W (x / K)) (((n + 1 : ℕ) : ℝ) / Q)‖^2) ∧
      (∑' n : ℕ, ‖idealThetaCoeff χ (n + 1) *
        weightOneBesselTransform (fun x => W (x / K)) (((n + 1 : ℕ) : ℝ) / Q)‖^2) ≤
        C * K^2 * (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)^2 * (Q / K)^(1 + ε) := by
  obtain ⟨s, Cb, hCb, hweight⟩ := weightOneBesselTransform_dilate_euler_source_bound 2 0
  obtain ⟨Ca, hCa, hsum⟩ := idealTheta_weighted_square ε hε hεtwo
  refine ⟨s, Ca * Cb^2, by positivity, ?_⟩
  intro χ W B hB hWs K Q hK hQ
  let E : ℝ := s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hE : 0 ≤ E := apply_nonneg (s.sup (schwartzSeminormFamily ℝ ℝ ℂ)) W
  have hb (n : ℕ) :
      (1 + ((n + 1 : ℕ) : ℝ) / (Q / K))^2 *
        ‖weightOneBesselTransform (fun x => W (x / K)) (((n + 1 : ℕ) : ℝ) / Q)‖ ≤
          Cb * K * E := by
    have h := hweight W B hB hWs K (((n + 1 : ℕ) : ℝ) / Q) hK (by positivity) 0 le_rfl
    have heq : K * (((n + 1 : ℕ) : ℝ) / Q) = ((n + 1 : ℕ) : ℝ) / (Q / K) := by
      field_simp
    simpa only [LocalLogFourier.eulerDeriv, iteratedDeriv_zero, Real.exp_zero,
      mul_one, heq] using h
  obtain ⟨hs, hh⟩ := hsum χ (Q / K) (Cb * K * E) (div_pos hQ hK) (by positivity)
    (fun n => weightOneBesselTransform (fun x => W (x / K)) ((n : ℝ) / Q)) hb
  refine ⟨hs, ?_⟩
  convert hh using 1
  ring

end ArtinMatthews

module

public import ArtinMatthews.SpectralBareModulusSeries
public import ArtinMatthews.SpectralBareSpectrumLimit
public import ArtinMatthews.SpectralABLExceptionalKLMass
public import ArtinMatthews.SpectralABLSourceBareTrace
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

/-! The actual exceptional bare diagonal and its fixed-parameter Weil scale. -/

noncomputable section
open Set
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0ABLExceptional_bare_diagonal_norm_le (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (a : ℝ) (A : ℕ) (hA : 3 ≤ A) (B : ℝ)
    (hB : ‖∑' c : Ioi (0 : ℕ), gamma0TrueWidthBareFibre N r r c n n
      (spectralABLExceptionalCorrected a A)‖ ≤ B) :
    ‖gamma0BareSourceSpectralSide N (spectralABLExceptionalEnergyTest a A (by omega))
      r r Y hY n n hn hn‖ ≤ (spectralABLExceptionalBound A/Real.pi+B)/4 := by
  rw [gamma0ABLExceptional_sameCusp_bare_source_trace N r Y hY n n hn hn a A hA,
    if_pos rfl, norm_mul]
  have hquarter : ‖(1/4 : ℂ)‖ = (1/4 : ℝ) := by
    rw [norm_div, norm_one, show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num,
      Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
  rw [hquarter]
  calc
    _ ≤ (1/4 : ℝ)*(‖spectralABLBareDiagonal (spectralABLExceptionalCorrected a A)‖+
        ‖∑' c : Ioi (0 : ℕ), gamma0TrueWidthBareFibre N r r c n n
          (spectralABLExceptionalCorrected a A)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ ≤ (1/4 : ℝ)*(spectralABLExceptionalBound A/Real.pi+B) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (spectralABLExceptionalBareDiagonal_norm_le a hA) hB) (by norm_num)
    _ = _ := by ring

theorem spectralABLExceptional_weil_factor_eq (N : ℕ) (n : ℤ) (ε a : ℝ)
    (ha : 0 < a) :
    ((N : ℝ)*(n.natAbs : ℝ)/a)^ε*
      (Real.sqrt ((n.natAbs : ℝ)*(Nat.gcd N n.natAbs : ℝ))/((N : ℝ)*a)) =
      (((N : ℝ)*(n.natAbs : ℝ))^ε*
        (Real.sqrt ((n.natAbs : ℝ)*(Nat.gcd N n.natAbs : ℝ))/(N : ℝ)))*a^(-1-ε) := by
  rw [Real.div_rpow (by positivity) ha.le, show -1-ε = -1+(-ε) by ring,
    Real.rpow_add ha, Real.rpow_neg_one, Real.rpow_neg ha.le]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end ArtinMatthews

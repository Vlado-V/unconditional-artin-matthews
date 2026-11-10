module

public import ArtinMatthews.SpectralTrueWidthBesselPairing
public import ArtinMatthews.SpectralCuspWidthNormalization
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

/-! The literal square root of the cusp width converts the native
coefficient Bessel bound to primitive unit-period normalization. -/

noncomputable section
open Set
open scoped MatrixGroups ContDiff BigOperators

namespace ArtinMatthews

theorem gamma0FourierPoincareTest_trueWidth_finite_bessel (N : ℕ) [NeZero N]
    (u : Finset (Gamma0AllHeightSpectralIndex N)) (a : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (n : ℤ) (hn : n ≠ 0) (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hsρ : tsupport ρ ⊆ Ioi Y) :
    let w := (gamma0CuspTrueWidth N a : ℝ)
    let nN := (gamma0CuspFrequencyStep N a : ℤ)*n
    let q := |cuspFourierFrequency 1 n|/w
    let ν (i : Gamma0AllHeightSpectralIndex N) :=
      Complex.sqrt (1/4-(gamma0AllHeightGradientSpectralValue N i : ℂ))
    let b (i : Gamma0AllHeightSpectralIndex N) := gamma0CuspBesselAmplitude N i a Y hY nN
      (gamma0CuspFrequencyStep_mul_ne_zero N a hn)
    (2*(N : ℝ))^2*(∑ i ∈ u, ‖cuspBesselTransform (ν i) q Y ρ‖^2*‖(Real.sqrt w : ℂ)*b i‖^2) ≤
      w*‖gamma0FourierPoincareTest N a nN ρ hρ hcρ hpρ‖^2 := by
  dsimp only
  let w := (gamma0CuspTrueWidth N a : ℝ)
  let nN := (gamma0CuspFrequencyStep N a : ℤ)*n
  let q := |cuspFourierFrequency 1 n|/w
  let ν (i : Gamma0AllHeightSpectralIndex N) :=
    Complex.sqrt (1/4-(gamma0AllHeightGradientSpectralValue N i : ℂ))
  let b (i : Gamma0AllHeightSpectralIndex N) := gamma0CuspBesselAmplitude N i a Y hY nN
    (gamma0CuspFrequencyStep_mul_ne_zero N a hn)
  let T (i : Gamma0AllHeightSpectralIndex N) := cuspBesselTransform (ν i) q Y ρ
  let P := gamma0FourierPoincareTest N a nN ρ hρ hcρ hpρ
  have hw : 0 < w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N a)
  have hFreq : |cuspFourierFrequency (N : ℝ) nN| = q :=
    (eq_div_iff hw.ne').mpr (cuspFourierFrequency_abs_trueWidth N a n)
  have hTest : (∑ i ∈ u, ‖(2*(N : ℂ))*b i*T i‖^2) ≤ ‖P‖^2 := by
    have h := gamma0FourierPoincareTest_native_finite_bessel N u a Y hY nN
      (gamma0CuspFrequencyStep_mul_ne_zero N a hn) ρ hρ hcρ hpρ hsρ
    change (∑ i ∈ u, ‖(2*(N : ℂ))*b i*cuspBesselTransform (ν i)
      |cuspFourierFrequency (N : ℝ) nN| Y ρ‖^2) ≤ ‖P‖^2 at h
    rw [hFreq] at h
    exact h
  change (2*(N : ℝ))^2*(∑ i ∈ u, ‖T i‖^2*‖(Real.sqrt w : ℂ)*b i‖^2) ≤ w*‖P‖^2
  calc
    _ = w*(∑ i ∈ u, ‖(2*(N : ℂ))*b i*T i‖^2) := by
      rw [Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
        Real.sq_sqrt hw.le,Complex.norm_natCast,show ‖(2 : ℂ)‖ = (2 : ℝ) from Complex.norm_natCast 2]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hTest hw.le

end ArtinMatthews

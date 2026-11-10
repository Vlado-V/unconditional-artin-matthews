module

public import ArtinMatthews.SpectralABLExceptionalJTransform
public import ArtinMatthews.SpectralABLSameCuspBareReindex
public import ArtinMatthews.SpectralBareSpectrumLimit
public import ArtinMatthews.SpectralABLExceptionalBareUpper
public import ArtinMatthews.SpectralABLSameCuspWeightedSeries
public import ArtinMatthews.SpectralInfinityBareReindex
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
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

/-! Uniform arithmetic bounds for the actual exceptional bare diagonal.
The level and frequency dependence is the literal same-cusp Weil factor. -/

noncomputable section
open Set
open scoped MatrixGroups
namespace ArtinMatthews

theorem spectralABLExceptionalDiagonalBareAmplitude_eq_J (a : ℝ) (A : ℕ)
    (n : ℤ) (hn : n ≠ 0) (X : ℝ) :
    spectralABLDiagonalBareAmplitude (spectralABLExceptionalCorrected a A) n X =
      spectralABLExceptionalJTransform a A X := by
  unfold spectralABLDiagonalBareAmplitude spectralABLBareKernel spectralABLExceptionalJTransform
  simp only [spectralWeylIntegerSignMultiplier, ite_eq_left (mul_self_pos.mpr hn),
    Complex.ofReal_div, Complex.ofReal_ofNat]

theorem gamma0ABLExceptional_mixed_bare_diagonal_bound (A : ℕ) (hA : 3 ≤ A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (r s : ℕ) [NeZero r] [NeZero s], r.Coprime s →
      ∀ (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) (a : ℝ), 0 < a → a ≤ 1 →
      let N := r*s
      let b := gamma0CuspOneOver s
      ‖gamma0BareSourceSpectralSide N (spectralABLExceptionalEnergyTest a A (by omega))
        b b Y hY n n hn hn‖ ≤
        (spectralABLExceptionalBound A/Real.pi+
          D*((N : ℝ)*(n.natAbs : ℝ)/a)^ε*
            (Real.sqrt ((n.natAbs : ℝ)*(Nat.gcd N n.natAbs : ℝ))/((N : ℝ)*a)))/4 := by
  obtain ⟨B,hB,hJ⟩ := spectralABLExceptionalJTransform_allX A hA
  obtain ⟨D,hD,hWeil⟩ := gamma0AtkinSameCusp_bareSeries_weighted hε
  refine ⟨D*B,mul_pos hD hB,?_⟩
  intro r s ir is hcop Y hY n hn a ha ha1
  dsimp only
  have hK (X : ℝ) (hX : 0 < X) :
      ‖spectralABLDiagonalBareAmplitude (spectralABLExceptionalCorrected a A) n X‖ ≤
        B*min 1 ((X/a^2)^(2*A)) := by
    rw [spectralABLExceptionalDiagonalBareAmplitude_eq_J a A n hn X]
    exact hJ a X ha ha1 hX
  have hSeries := (hWeil r s hcop n hn a ha ha1 A (by omega)
    (spectralABLExceptionalCorrected a A) B hB.le hK).2.2
  exact gamma0ABLExceptional_bare_diagonal_norm_le (r*s) (gamma0CuspOneOver s)
    Y hY n hn a A hA _ hSeries

theorem gamma0ABLExceptional_infinity_bare_diagonal_bound (A : ℕ) (hA : 3 ≤ A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (N : ℕ) [NeZero N]
      (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) (a : ℝ), 0 < a → a ≤ 1 →
      ‖gamma0BareSourceSpectralSide N (spectralABLExceptionalEnergyTest a A (by omega))
        1 1 Y hY n n hn hn‖ ≤
        (spectralABLExceptionalBound A/Real.pi+
          D*((N : ℝ)*(n.natAbs : ℝ)/a)^ε*
            (Real.sqrt ((n.natAbs : ℝ)*(Nat.gcd N n.natAbs : ℝ))/((N : ℝ)*a)))/4 := by
  obtain ⟨B,hB,hJ⟩ := spectralABLExceptionalJTransform_allX A hA
  obtain ⟨D,hD,hWeil⟩ := spectralABLOrdinaryDiagonal_bareSeries_weighted hε
  refine ⟨D*B,mul_pos hD hB,?_⟩
  intro N inst Y hY n hn a ha ha1
  have hK (X : ℝ) (hX : 0 < X) :
      ‖spectralABLDiagonalBareAmplitude (spectralABLExceptionalCorrected a A) n X‖ ≤
        B*min 1 ((X/a^2)^(2*A)) := by
    rw [spectralABLExceptionalDiagonalBareAmplitude_eq_J a A n hn X]
    exact hJ a X ha ha1 hX
  have hSeries := (hWeil N n hn a ha ha1 A (by omega)
    (spectralABLExceptionalCorrected a A) B hB.le hK).2.2
  apply gamma0ABLExceptional_bare_diagonal_norm_le N 1 Y hY n hn a A hA
  rw [gamma0Infinity_bareSeries_reindex N n (spectralABLExceptionalCorrected a A)]
  exact hSeries

end ArtinMatthews

module

public import ArtinMatthews.SpectralBareSpectrumLimit
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

/-! Positivity of the actual bare diagonal for tests nonnegative on every
energy. The continuous and residual contributions are kept as actual terms. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace ArtinMatthews

private theorem spectral_mul_star_self_re (z a : ℂ) :
    (z * (a * star a)).re = z.re * ‖a‖ ^ 2 := by
  have ha : a * star a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_pow, Complex.star_def] using Complex.mul_conj' a
  rw [ha]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

theorem gamma0BareCuspidalTerm_diagonal_re (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (i : Gamma0AllHeightSpectralIndex N) :
    (gamma0BareCuspidalTerm N h r r Y hY n n hn hn i).re =
      gamma0BareCuspidalDiagonalDensity N h r Y hY n hn i := by
  unfold gamma0BareCuspidalTerm gamma0BareCuspidalDiagonalDensity
  exact spectral_mul_star_self_re _ _

theorem gamma0BareResidualRhoSum_diagonal_re_nonneg (N : ℕ) [NeZero N]
    (h : SpectralEnergyTest) (hp : ∀ l, 0 ≤ (h l).re)
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) :
    0 ≤ (gamma0BareResidualRhoSum N h r r n n hn hn).re := by
  unfold gamma0BareResidualRhoSum
  simp only [Complex.re_sum]
  apply Finset.sum_nonneg
  intro l _
  apply Finset.sum_nonneg
  intro j _
  unfold gamma0BareResidualRhoTerm
  rw [spectral_mul_star_self_re]
  exact mul_nonneg (hp l) (sq_nonneg _)

theorem gamma0BareContinuousRhoIntegral_diagonal_re_nonneg (N : ℕ) [NeZero N]
    (h : SpectralEnergyTest) (hr : ∀ l, ((h l).re : ℂ) = h l)
    (hp : ∀ l, 0 ≤ (h l).re) (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (n : ℤ) (hn : n ≠ 0)
    (hI : IntegrableOn (gamma0BareContinuousRhoIntegrand N h r r Y hY n n hn hn)
      (Ioi (0 : ℝ))) :
    0 ≤ (∫ t in Ioi (0 : ℝ), gamma0BareContinuousRhoIntegrand N h r r Y hY n n hn hn t).re := by
  have heq :
      (∫ t in Ioi (0 : ℝ), gamma0BareContinuousRhoIntegrand N h r r Y hY n n hn hn t).re =
        ∫ t in Ioi (0 : ℝ), (gamma0BareContinuousRhoIntegrand N h r r Y hY n n hn hn t).re :=
    (integral_re hI).symm
  rw [heq]
  apply integral_nonneg
  intro t
  change 0 ≤ (gamma0BareContinuousRhoIntegrand N h r r Y hY n n hn hn t).re
  rw [gamma0BareContinuousRhoIntegrand_diagonal N h r Y hY n hn t
    (hr (spectralContinuousEnergyParameter t)), Complex.ofReal_re]
  exact gamma0BareContinuousRhoDiagonal_nonneg N h r Y hY n hn t
    (hp (spectralContinuousEnergyParameter t))

theorem gamma0BareSourceSpectralDiagonal_cusp_finset_le (N : ℕ) [NeZero N]
    (h : SpectralEnergyTest) (hr : ∀ l, ((h l).re : ℂ) = h l)
    (hp : ∀ l, 0 ≤ (h l).re) (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (n : ℤ) (hn : n ≠ 0) (F : Finset (Gamma0AllHeightSpectralIndex N))
    (hC : Summable (gamma0BareCuspidalTerm N h r r Y hY n n hn hn))
    (hI : IntegrableOn (gamma0BareContinuousRhoIntegrand N h r r Y hY n n hn hn)
      (Ioi (0 : ℝ))) :
    (∑ i ∈ F, gamma0BareCuspidalDiagonalDensity N h r Y hY n hn i) ≤
      (gamma0BareSourceSpectralSide N h r r Y hY n n hn hn).re := by
  have hs : Summable (fun i => (gamma0BareCuspidalTerm N h r r Y hY n n hn hn i).re) :=
    Complex.reCLM.summable hC
  have hfin := hs.sum_le_tsum F (fun i _ => by
    rw [gamma0BareCuspidalTerm_diagonal_re]
    unfold gamma0BareCuspidalDiagonalDensity gamma0CuspidalTestSymbol
    exact mul_nonneg (hp _) (sq_nonneg _))
  simp only [gamma0BareCuspidalTerm_diagonal_re] at hfin
  have hCon := gamma0BareContinuousRhoIntegral_diagonal_re_nonneg N h hr hp r Y hY n hn hI
  have hRes := gamma0BareResidualRhoSum_diagonal_re_nonneg N h hp r n hn
  unfold gamma0BareSourceSpectralSide
  rw [Complex.add_re, Complex.add_re, Complex.re_tsum hC]
  simp only [gamma0BareCuspidalTerm_diagonal_re]
  linarith

end ArtinMatthews

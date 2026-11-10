module

public import ArtinMatthews.SpectralHeatCuspidalSplit
public import ArtinMatthews.SpectralBareResidualLimit
public import ArtinMatthews.SpectralBareEisensteinLimit
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

/-! A bounded actual Gaussian diagonal controls its two positive
principal parts after keeping the finite complementary and residual sums. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0HeatSourceSpectralSide_split (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (R : ℝ) :
    gamma0HeatSourceSpectralSide N h r s Y hY m n hm hn R =
      (∑' i, gamma0HeatCuspidalTerm N h r s Y hY m n hm hn R i)+
        ((∫ t in Ioi (0 : ℝ), gamma0HeatContinuousRhoIntegrand N h r s Y hY m n hm hn R t)+
          gamma0HeatResidualRhoSum N h r s m n hm hn R) := rfl

theorem gamma0HeatSpectrum_diagonal_bounds (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (hCusp : ∀ i : Gamma0HeatPrincipalCuspidalIndex N,
      ‖gamma0CuspidalTestSymbol N h i.val‖ = (gamma0CuspidalTestSymbol N h i.val).re)
    (hReal : ∀ t : ℝ, ((spectralContinuousTestSymbol h t).re : ℂ) = spectralContinuousTestSymbol h t)
    (hPos : ∀ t : ℝ, 0 ≤ (spectralContinuousTestSymbol h t).re)
    (C : ℝ) (hC : 0 ≤ C)
    (hTotal : ∀ R : ℝ, 1 ≤ R → ‖gamma0HeatSourceSpectralSide N h r r Y hY n n hn hn R‖ ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧
      (∀ k : ℕ, gamma0HeatPrincipalCuspidalDiagonal N h r Y hY n hn ((k : ℝ)+1) ≤ D) ∧
      (∀ k : ℕ, (∫ t in Ioi (0 : ℝ),
        gamma0HeatContinuousRhoIntegrand N h r r Y hY n n hn hn ((k : ℝ)+1) t).re ≤ D) := by
  let Bc := Real.exp (1/2 : ℝ)*∑ i∈gamma0HeatComplementaryCuspidalIndices N,
    ‖gamma0BareCuspidalTerm N h r r Y hY n n hn hn i‖
  let Br := Real.exp (1/2 : ℝ)*∑ l∈gamma0ResidualEnergyWindow N,
    ∑ j, ‖gamma0BareResidualRhoTerm N h r r n n hn hn l j‖
  let D := C+Bc+Br
  have hD : 0 ≤ D := by
    unfold D Bc Br
    positivity
  have hb (k : ℕ) :
      gamma0HeatPrincipalCuspidalDiagonal N h r Y hY n hn ((k : ℝ)+1) ≤ D ∧
      (∫ t in Ioi (0 : ℝ), gamma0HeatContinuousRhoIntegrand N h r r Y hY n n hn hn ((k : ℝ)+1) t).re ≤ D := by
    let R : ℝ := (k : ℝ)+1
    have hR : 1 ≤ R := by
      dsimp only [R]
      linarith [Nat.cast_nonneg (α := ℝ) k]
    have hR0 : 0 < R := zero_lt_one.trans_le hR
    let P := gamma0HeatPrincipalCuspidalDiagonal N h r Y hY n hn R
    let I := (∫ t in Ioi (0 : ℝ), gamma0HeatContinuousRhoIntegrand N h r r Y hY n n hn hn R t).re
    let E := ∑ i∈gamma0HeatComplementaryCuspidalIndices N,
      gamma0HeatCuspidalTerm N h r r Y hY n n hn hn R i
    let V := gamma0HeatResidualRhoSum N h r r n n hn hn R
    have hEq : (gamma0HeatSourceSpectralSide N h r r Y hY n n hn hn R).re =
        P+E.re+(I+V.re) := by
      rw [gamma0HeatSourceSpectralSide_split,
        gamma0HeatCuspidal_tsum_split N _ (gamma0HeatCuspidalTerm_summable N h r r Y hY n n hn hn R hR0)]
      simp only [Complex.add_re]
      rfl
    have hP : 0 ≤ P := gamma0HeatPrincipalCuspidalDiagonal_nonneg N h r Y hY n hn hR0 hCusp
    have hI : 0 ≤ I := by
      dsimp only [I,R]
      rw [gamma0HeatContinuousRhoDiagonal_integral_re N h r Y hY n hn hReal k]
      exact integral_nonneg (fun t => mul_nonneg
        (gamma0BareContinuousRhoDiagonal_nonneg N h r Y hY n hn t (hPos t))
        (spectralGaussianCutoff_nonneg k (2*t^2)))
    have hE : -E.re ≤ Bc := by
      have hnorm : -E.re ≤ ‖E‖ := by
        simpa only [Complex.neg_re,norm_neg] using Complex.re_le_norm (-E)
      exact hnorm.trans (gamma0HeatComplementaryCuspidal_norm_le N h r r Y hY n n hn hn hR)
    have hV : -V.re ≤ Br := by
      have hnorm : -V.re ≤ ‖V‖ := by
        simpa only [Complex.neg_re,norm_neg] using Complex.re_le_norm (-V)
      exact hnorm.trans (gamma0HeatResidualRhoSum_norm_le N h r r n n hn hn hR)
    have hB : (gamma0HeatSourceSpectralSide N h r r Y hY n n hn hn R).re ≤ C :=
      (Complex.re_le_norm _).trans (hTotal R hR)
    have hPI : P+I ≤ D := by
      dsimp only [D]
      linarith
    change P ≤ D ∧ I ≤ D
    exact ⟨by linarith,by linarith⟩
  exact ⟨D,hD,fun k => (hb k).1,fun k => (hb k).2⟩

end ArtinMatthews

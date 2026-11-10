module

public import ArtinMatthews.SpectralBareSpectrumLimit
public import ArtinMatthews.SpectralJClippedEnergyTest
public import ArtinMatthews.SpectralJRegularizedEnergyTest
public import ArtinMatthews.SpectralAbsoluteComparison
public import ArtinMatthews.SpectralJRegularizationGap
public import ArtinMatthews.SpectralJRegularizedNativeTerms
public import ArtinMatthews.SpectralJRegularizedSourceAbsolute
public import ArtinMatthews.SpectralJSourceAbsolute
public import ArtinMatthews.SpectralNativeHermitian
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

/-! The actual regularized source side converges with an explicit gap error. -/
namespace ArtinMatthews
open Set Filter MeasureTheory
open scoped ContDiff MatrixGroups BigOperators Topology
noncomputable section

def gamma0BareSourceAbsoluteMass (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) : ℝ :=
  (∑' i, ‖gamma0BareCuspidalTerm N h r s Y hY m n hm hn i‖) +
    (∫ t in Ioi (0 : ℝ), ‖gamma0BareContinuousRhoIntegrand N h r s Y hY m n hm hn t‖) +
      ∑ l ∈ gamma0ResidualEnergyWindow N, ∑ j, ‖gamma0BareResidualRhoTerm N h r s m n hm hn l j‖

theorem gamma0BareSourceAbsoluteMass_nonneg (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    0 ≤ gamma0BareSourceAbsoluteMass N h r s Y hY m n hm hn := by
  unfold gamma0BareSourceAbsoluteMass
  exact add_nonneg
    (add_nonneg (tsum_nonneg (fun _ => norm_nonneg _))
      (integral_nonneg (fun _ => norm_nonneg _)))
    (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)))

theorem gamma0BareSourceAbsoluteMass_swap (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    gamma0BareSourceAbsoluteMass N h r s Y hY m n hm hn =
      gamma0BareSourceAbsoluteMass N h s r Y hY n m hn hm := by
  unfold gamma0BareSourceAbsoluteMass
  simp_rw [gamma0BareCuspidalTerm_norm_swap N h r s Y hY m n hm hn,
    gamma0BareContinuousRhoIntegrand_norm_swap N h r s Y hY m n hm hn,
    gamma0BareResidualRhoTerm_norm_swap N h r s m n hm hn]

theorem gamma0JSource_regularization_error (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (L : ℝ) (hL : 0 ≤ L) :
    ‖gamma0BareSourceSpectralSide (r * s) (spectralJRegularizedEnergyTest f hf hc hp L hL)
        1 (gamma0CuspOneOver s) Y hY m n hm hn -
      gamma0BareSourceSpectralSide (r * s) (spectralJClippedEnergyTest f hf hc hp)
        1 (gamma0CuspOneOver s) Y hY m n hm hn‖ ≤
      Real.exp (-(L * (3 / 16))) *
        gamma0BareSourceAbsoluteMass (r * s) (spectralJClippedEnergyTest f hf hc hp)
          1 (gamma0CuspOneOver s) Y hY m n hm hn := by
  obtain ⟨hC, hI⟩ := gamma0JSource_absolute f hf hc hp r s hcop Y hY m n hm hn
  obtain ⟨hCL, hIL⟩ := gamma0JRegularizedSource_absolute f hf hc hp r s hcop Y hY m n hm hn L hL
  have h := spectralThreeSector_absolute_comparison
    (ι := Gamma0AllHeightSpectralIndex (r * s))
    (κ := Ici (0 : ℝ))
    (β := fun l => Fin (Module.finrank ℂ (gamma0ResidualEnergyEigenspace (r * s) l)))
    (gamma0ResidualEnergyWindow (r * s))
    (gamma0BareCuspidalTerm (r * s) (spectralJRegularizedEnergyTest f hf hc hp L hL)
      1 (gamma0CuspOneOver s) Y hY m n hm hn)
    (gamma0BareCuspidalTerm (r * s) (spectralJClippedEnergyTest f hf hc hp)
      1 (gamma0CuspOneOver s) Y hY m n hm hn)
    (gamma0BareContinuousRhoIntegrand (r * s) (spectralJRegularizedEnergyTest f hf hc hp L hL)
      1 (gamma0CuspOneOver s) Y hY m n hm hn)
    (gamma0BareContinuousRhoIntegrand (r * s) (spectralJClippedEnergyTest f hf hc hp)
      1 (gamma0CuspOneOver s) Y hY m n hm hn)
    (gamma0BareResidualRhoTerm (r * s) (spectralJRegularizedEnergyTest f hf hc hp L hL)
      1 (gamma0CuspOneOver s) m n hm hn)
    (gamma0BareResidualRhoTerm (r * s) (spectralJClippedEnergyTest f hf hc hp)
      1 (gamma0CuspOneOver s) m n hm hn)
    (Real.exp (-(L * (3 / 16)))) hCL hC hIL hI
    (gamma0JRegularized_cuspidal_error_le f hf hc hp (r * s)
      1 (gamma0CuspOneOver s) Y hY m n hm hn L hL)
    (gamma0JRegularized_continuous_error_le f hf hc hp (r * s)
      1 (gamma0CuspOneOver s) Y hY m n hm hn L hL)
    (fun l _ j => gamma0JRegularized_residual_error_le f hf hc hp (r * s)
      (gamma0CuspOneOver s) m n hm hn L hL l j)
  simpa only [gamma0BareSourceSpectralSide, gamma0BareSourceAbsoluteMass, gamma0BareResidualRhoSum] using h

theorem gamma0JSource_regularization_tendsto (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    Tendsto (fun k : ℕ => gamma0BareSourceSpectralSide (r * s)
      (spectralJRegularizedEnergyTest f hf hc hp (k : ℝ) (Nat.cast_nonneg k))
        1 (gamma0CuspOneOver s) Y hY m n hm hn) atTop
      (𝓝 (gamma0BareSourceSpectralSide (r * s) (spectralJClippedEnergyTest f hf hc hp)
        1 (gamma0CuspOneOver s) Y hY m n hm hn)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hE := (spectralJRegularizationMultiplier_gap_error_tendsto (3 / 16)
    (by norm_num)).comp tendsto_natCast_atTop_atTop
  apply squeeze_zero (fun _ : ℕ => norm_nonneg _)
    (fun k : ℕ => gamma0JSource_regularization_error f hf hc hp r s hcop Y hY m n hm hn
      (k : ℝ) (Nat.cast_nonneg k))
  simpa only [Function.comp_def, zero_mul] using hE.mul_const
    (gamma0BareSourceAbsoluteMass (r * s) (spectralJClippedEnergyTest f hf hc hp)
      1 (gamma0CuspOneOver s) Y hY m n hm hn)

end
end ArtinMatthews

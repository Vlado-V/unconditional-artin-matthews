module

public import ArtinMatthews.SpectralJPrincipalMass
public import ArtinMatthews.SpectralJClippedEnergyTest
public import ArtinMatthews.SpectralJForwardRealWeight
public import ArtinMatthews.SpectralJForwardStripRapid
public import ArtinMatthews.SpectralJNativeAmplitudes
public import ArtinMatthews.SpectralJNativeSymbols
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

/-! Rapid source weights are absolutely summable against the actual cusp amplitudes. -/
namespace ArtinMatthews
open Set
open scoped ContDiff MatrixGroups
noncomputable section

theorem gamma0JClipped_cuspidal_absolute_of_principal
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (N : ℕ) [NeZero N] (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (hr : Summable (fun i : Gamma0HeatPrincipalCuspidalIndex N =>
      gamma0NativePrincipalDensity N r Y hY m hm i /
        (1 + |gamma0CuspPrincipalParameter N i.val|) ^ 4))
    (hs : Summable (fun i : Gamma0HeatPrincipalCuspidalIndex N =>
      gamma0NativePrincipalDensity N s Y hY n hn i /
        (1 + |gamma0CuspPrincipalParameter N i.val|) ^ 4)) :
    Summable (fun i : Gamma0AllHeightSpectralIndex N =>
      ‖gamma0BareCuspidalTerm N (spectralJClippedEnergyTest f hf hc hp) r s Y hY m n hm hn i‖) := by
  obtain ⟨C, hC, hbound⟩ := spectralJForwardTransform_real_rapid f hf hc hp 4
  apply gamma0HeatCuspidal_summable_of_principal N
  have hmaj := (hr.add hs).mul_left (Real.pi * C / 2)
  apply hmaj.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro i
  let t := gamma0CuspPrincipalParameter N i.val
  let W := Real.cosh (Real.pi * t)
  let a := gamma0BareCuspidalAmplitude N i.val r Y hY m hm
  let b := gamma0BareCuspidalAmplitude N i.val s Y hY n hn
  let A := gamma0CuspUnitAmplitude N i.val r Y hY m hm
  let B := gamma0CuspUnitAmplitude N i.val s Y hY n hn
  have hW : 0 < W := Real.cosh_pos _
  have ha : ‖a‖ ≤ ‖A‖ := gamma0BareCuspidalAmplitude_norm_le_unit N i.val r Y hY m hm
  have hb : ‖b‖ ≤ ‖B‖ := gamma0BareCuspidalAmplitude_norm_le_unit N i.val s Y hY n hn
  have hab : ‖a‖ * ‖b‖ ≤ (‖A‖ ^ 2 + ‖B‖ ^ 2) / 2 := by
    have hmul := mul_le_mul ha hb (norm_nonneg _) (norm_nonneg _)
    have hsq := sq_nonneg (‖A‖ - ‖B‖)
    nlinarith
  have hd : 0 ≤ gamma0NativePrincipalDensity N r Y hY m hm i +
      gamma0NativePrincipalDensity N s Y hY n hn i :=
    add_nonneg (div_nonneg (sq_nonneg _) hW.le) (div_nonneg (sq_nonneg _) hW.le)
  change ‖gamma0BareCuspidalTerm N (spectralJClippedEnergyTest f hf hc hp)
      r s Y hY m n hm hn i.val‖ ≤ _
  rw [gamma0BareCuspidalTerm, gamma0JClipped_principal_symbol f hf hc hp N i,
    norm_mul, norm_mul, norm_star, spectralJForwardSpectralWeight_norm_real]
  change (Real.pi / W) * ‖spectralJForwardTransform f (t : ℂ)‖ * (‖a‖ * ‖b‖) ≤ _
  calc
    _ ≤ ((Real.pi / W) * ‖spectralJForwardTransform f (t : ℂ)‖) *
        ((‖A‖ ^ 2 + ‖B‖ ^ 2) / 2) :=
      mul_le_mul_of_nonneg_left hab (mul_nonneg (div_nonneg Real.pi_pos.le hW.le) (norm_nonneg _))
    _ = (Real.pi / 2) * ‖spectralJForwardTransform f (t : ℂ)‖ *
        (gamma0NativePrincipalDensity N r Y hY m hm i +
          gamma0NativePrincipalDensity N s Y hY n hn i) := by
      dsimp only [gamma0NativePrincipalDensity, A, B, W, t]
      ring
    _ ≤ (Real.pi / 2) * (C / (1 + |t|) ^ 4) *
        (gamma0NativePrincipalDensity N r Y hY m hm i +
          gamma0NativePrincipalDensity N s Y hY n hn i) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hbound t) (by positivity)) hd
    _ = _ := by
      change _ = (Real.pi * C / 2) *
        (gamma0NativePrincipalDensity N r Y hY m hm i / (1 + |t|) ^ 4 +
          gamma0NativePrincipalDensity N s Y hY n hn i / (1 + |t|) ^ 4)
      ring

end
end ArtinMatthews

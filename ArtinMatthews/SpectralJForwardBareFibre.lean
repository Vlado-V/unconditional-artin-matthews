module

public import ArtinMatthews.SpectralBareModulusSeries
public import ArtinMatthews.SpectralJForwardWeylNormalization
public import ArtinMatthews.SpectralJOddSynthesis
public import ArtinMatthews.SpectralGamma0LocalFourierBessel
public import ArtinMatthews.SpectralJForwardInverse
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
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

namespace ArtinMatthews
open Set MeasureTheory
open scoped ContDiff MatrixGroups
noncomputable section

theorem spectralJForwardTransform_bareKernel
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioi (0 : ℝ))
    (m n : ℤ) (hmn : 0 < m * n) {X : ℝ} (hX : 0 < X) :
    spectralABLBareKernel (spectralJForwardSpectralWeight f) m n X =
      (2 / (X : ℂ)) * (f X - spectralJOddSynthesis f X) := by
  have hinv := spectralJForwardTransform_inverse_apply f hf hc hs hX
  have hk : spectralJWeightedSynthesis
      (fun r : ℝ => spectralJForwardSpectralWeight f (r : ℂ)) X =
      (X : ℂ) / 2 * spectralABLBareKernel (spectralJForwardSpectralWeight f) m n X := by
    simp only [spectralJWeightedSynthesis, spectralABLBareKernel,
      spectralWeylIntegerSignMultiplier, ite_eq_left hmn]
  rw [hk] at hinv
  have hXc : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  apply mul_left_cancel₀ (show (X : ℂ) / 2 ≠ 0 from div_ne_zero hXc (by norm_num))
  calc
    (X : ℂ) / 2 * spectralABLBareKernel (spectralJForwardSpectralWeight f) m n X =
        f X - spectralJOddSynthesis f X := by linear_combination -hinv
    _ = _ := by field_simp [hXc] <;> ring

theorem gamma0TrueWidthBareFibre_forwardJ
    (N : ℕ) [NeZero N] (r s : SL(2, ℤ)) (c : Ioi (0 : ℕ))
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : 0 < m * n)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioi (0 : ℝ)) :
    let _ : NeZero c.val := ⟨c.property.ne'⟩
    let C := gamma0TrueWidthModulus N r s (c.val : ℝ)
    let X := Real.sqrt (|cuspFourierFrequency 1 m| * |cuspFourierFrequency 1 n|) * (2 / C)
    gamma0TrueWidthBareFibre N r s c m n (spectralJForwardSpectralWeight f) =
      (gamma0TrueWidthKloostermanSum N r s c.val m n / (C : ℂ)) *
        (f X - spectralJOddSynthesis f X) := by
  letI : NeZero c.val := ⟨c.property.ne'⟩
  dsimp only
  let C := gamma0TrueWidthModulus N r s (c.val : ℝ)
  let K := Real.sqrt (|cuspFourierFrequency 1 m| * |cuspFourierFrequency 1 n|)
  have hC : 0 < C := gamma0TrueWidthModulus_pos N r s (Nat.cast_pos.mpr c.property)
  have hK : 0 < K := Real.sqrt_pos.mpr (mul_pos
    (abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one m hm))
    (abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one n hn)))
  have hX : 0 < K * (2 / C) := mul_pos hK (div_pos two_pos hC)
  unfold gamma0TrueWidthBareFibre
  change gamma0TrueWidthKloostermanSum N r s c.val m n *
    ((K / C ^ 2 : ℝ) : ℂ) *
    spectralABLBareKernel (spectralJForwardSpectralWeight f) m n (K * (2 / C)) =
      (gamma0TrueWidthKloostermanSum N r s c.val m n / (C : ℂ)) *
        (f (K * (2 / C)) - spectralJOddSynthesis f (K * (2 / C)))
  rw [spectralJForwardTransform_bareKernel f hf hc hs m n hmn hX]
  have hCc : (C : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hC.ne'
  have hKc : (K : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hK.ne'
  push_cast
  field_simp [hCc, hKc]
  <;> ring

end
end ArtinMatthews

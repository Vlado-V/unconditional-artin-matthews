module

public import ArtinMatthews.SpectralCuspFourierTestSeed
public import ArtinMatthews.KloostermanDoubleCoset
public import ArtinMatthews.SpectralCuspDoubleCosetPeriod
public import ArtinMatthews.SpectralCuspTranslationAdmissibility
public import ArtinMatthews.SpectralHorizontalLatticePartition
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! Exact parabolic unfolding of the actual compact Fourier test.  The
translate step is N, and the Fourier phase is the existing frequency n/N. -/

noncomputable section
open Set
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

def cuspFourierWave (N : ℕ) (n : ℤ) (ρ : ℝ → ℝ) (z : UpperHalfPlane) : ℂ :=
  (ρ z.im : ℂ) * star (cuspFourierPhase (N : ℝ) n z.re)

theorem cuspFourierTestSeed_period_translate (N : ℕ) [NeZero N]
    (n : ℤ) (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpos : tsupport ρ ⊆ Ioi (0 : ℝ)) (l : ℤ) (z : UpperHalfPlane) :
    (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) n ρ hρ hcρ hpos).val
      (integerTranslation ((N : ℤ) * l) • z) =
        spectralHorizontalPartition (N : ℝ) (z.re + (N : ℝ) * l) • cuspFourierWave N n ρ z := by
  rw [cuspFourierTestSeed_apply, integerTranslation_eq_T_zpow,
    ModularGroup.re_T_zpow_smul, ModularGroup.im_T_zpow_smul]
  have hp := cuspFourierPhase_integer_shift_of_dvd N n ((N : ℤ) * l)
    (show (N : ℤ) ∣ n * ((N : ℤ) * l) from ⟨n*l,by ring⟩) z.re
  rw [hp]
  unfold cuspFourierWave
  simp only [Complex.real_smul, Complex.ofReal_mul, Int.cast_mul, Int.cast_natCast]
  ring

theorem cuspFourierTestSeed_parabolic_finsum (N : ℕ) [NeZero N]
    (n : ℤ) (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpos : tsupport ρ ⊆ Ioi (0 : ℝ)) (z : UpperHalfPlane) :
    (∑ᶠ l : ℤ,
      (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) n ρ hρ hcρ hpos).val
        (integerTranslation ((N : ℤ) * l) • z)) = cuspFourierWave N n ρ z := by
  simp_rw [cuspFourierTestSeed_period_translate]
  rw [← finsum_smul, spectralHorizontalPartition_lattice_finsum (Nat.cast_pos.mpr (NeZero.pos N)),
    one_smul]

theorem cuspFourierWave_translate_of_admissible (N : ℕ) [NeZero N]
    (n k : ℤ) (hNk : (N : ℤ) ∣ n*k) (ρ : ℝ → ℝ) (z : UpperHalfPlane) :
    cuspFourierWave N n ρ (integerTranslation k • z) = cuspFourierWave N n ρ z := by
  unfold cuspFourierWave
  rw [integerTranslation_eq_T_zpow, ModularGroup.re_T_zpow_smul, ModularGroup.im_T_zpow_smul,
    cuspFourierPhase_integer_shift_of_dvd N n k hNk]

end ArtinMatthews

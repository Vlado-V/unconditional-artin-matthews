module

public import ArtinMatthews.SpectralCuspEisensteinWidthFormula
public import ArtinMatthews.SpectralTrueWidthOrbitalBessel
public import ArtinMatthews.SpectralCuspEisensteinInfinity
public import ArtinMatthews.SpectralInfinityOrbitalWeil
public import ArtinMatthews.SpectralMixedCuspNormalization
public import ArtinMatthews.SpectralMixedCuspSourcePhase
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual two-height J/K expression in the source mixed cusp
coordinates. The ABL frequency order is `m,n`, whereas the native
right-chart-first input is `n,m`. -/

noncomputable section
open MeasureTheory
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0MixedCuspFrequencyStep (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) : gamma0CuspFrequencyStep (r*s) (gamma0CuspOneOver s) = s := by
  rw [gamma0CuspFrequencyStep,gamma0MixedCusp_trueWidth r s hcop,mul_comm r s,
    Nat.mul_div_cancel s (NeZero.pos r)]

theorem spectral_mixed_weyl_argument (C : ℝ) (m n : ℤ) :
    Real.sqrt (|cuspFourierFrequency 1 n| * |cuspFourierFrequency 1 m|)*(2/C) =
      (4*Real.pi*Real.sqrt (|(m : ℝ)*(n : ℝ)|))/C := by
  have hπ : 0 ≤ 2*Real.pi := by positivity
  have hprod : |cuspFourierFrequency 1 n| * |cuspFourierFrequency 1 m| =
      (2*Real.pi)^2*|(m : ℝ)*(n : ℝ)| := by
    simp only [cuspFourierFrequency,div_one,abs_mul,abs_of_nonneg hπ]
    ring
  rw [hprod,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hπ]
  ring

theorem gamma0MixedBesselOrbital_source (r s c : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) (m n : ℤ) (ρ η : ℝ → ℝ) :
    let C := (s : ℝ)*Real.sqrt (r : ℝ)*(c : ℝ)
    let a := |cuspFourierFrequency 1 n|
    let b := |cuspFourierFrequency 1 m|
    let X := (4*Real.pi*Real.sqrt (|(m : ℝ)*(n : ℝ)|))/C
    gamma0TrueWidthBesselOrbital (r*s) (gamma0CuspOneOver s) 1 (s*c) n m ρ η =
      ((Real.sqrt (a*b)/C^2 : ℝ) : ℂ)*
        (∫ v : ℝ, spectralWeylIntegerSignMultiplier m n v X*
          spectralKLPhysicalAnalysisIntegral (spectralKLHeightPhysicalTest b η) v*
          star (spectralKLPhysicalAnalysisIntegral
            (spectralKLHeightPhysicalTest a (fun y => ρ ((r : ℝ)*y))) v) ∂spectralKLSpectralMeasure) := by
  simp only [gamma0TrueWidthBesselOrbital,gamma0MixedCusp_trueModulus r s hcop,
    gamma0MixedCusp_trueWidth r s hcop,gamma0CuspTrueWidth_identity,Nat.cast_one,one_mul,
    spectral_mixed_weyl_argument,spectralWeylIntegerSignMultiplier,mul_comm n m]

theorem gamma0MixedBesselGeometricFibre_source (r s c : ℕ) [NeZero r] [NeZero s] [NeZero c]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (m n : ℤ) (ρ η : ℝ → ℝ) :
    gamma0TrueWidthBesselGeometricFibre (r*s) (gamma0CuspOneOver s) 1 (s*c) n m ρ η =
      ((r*s*s : ℕ) : ℂ)*(lowerTriMixedResidueSum (NeZero.pos r) hab c m n*
        gamma0TrueWidthBesselOrbital (r*s) (gamma0CuspOneOver s) 1 (s*c) n m ρ η) := by
  simp only [gamma0TrueWidthBesselGeometricFibre,gamma0CuspFrequencyStep_identity,
    gamma0MixedCuspFrequencyStep r s hcop,gamma0MixedKloosterman_eq_source_lowerTri r s c hcop hab,
    Nat.cast_mul]

theorem gamma0MixedBesselGeometricFibre_zero_off_source_moduli (r s q : ℕ)
    [NeZero r] [NeZero s] [NeZero q] (hcop : r.Coprime s) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (m n : ℤ) (ρ η : ℝ → ℝ)
    (hq : ¬ ∃ c : ℕ, 0 < c ∧ q = s*c ∧ r.Coprime c) :
    gamma0TrueWidthBesselGeometricFibre (r*s) (gamma0CuspOneOver s) 1 q n m ρ η = 0 := by
  rw [gamma0TrueWidthBesselGeometricFibre,
    gamma0MixedKloosterman_zero_off_source_moduli r s q hcop hab m n hq,zero_mul,mul_zero]

end ArtinMatthews

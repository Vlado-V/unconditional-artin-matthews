module

public import ArtinMatthews.SpectralCuspFourierTestPairing
public import ArtinMatthews.SpectralCuspBesselTransform
public import ArtinMatthews.SpectralGamma0CuspidalProjection
public import ArtinMatthews.SpectralGamma0NativeFourierBessel
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

/-! Exact Bessel transforms of genuine compact Poincare tests against the
native cuspidal basis.  No trace formula or large-sieve estimate is assumed. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff MatrixGroups InnerProductSpace BigOperators

namespace ArtinMatthews

local instance poincareBessel_innerProduct (N : ℕ) [NeZero N] :
    InnerProductSpace ℂ (gamma0AllHeightCuspidalMassSpace N) :=
  Submodule.innerProductSpace (𝕜 := ℂ) (E := Gamma0RegionL2 N) (gamma0AllHeightCuspidalMassSpace N)

theorem gamma0FourierPoincareTest_inner_of_bessel (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ)
    (f : Gamma0RegionL2 N) (a ν : ℂ) (q : ℝ)
    (hf : gamma0CuspFourierCoefficient N r Y hY n f =ᵐ[volume.restrict (Ioi Y)]
      fun y => a * cuspBesselKernel ν q y)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpos : tsupport ρ ⊆ Ioi (0 : ℝ)) (hs : tsupport ρ ⊆ Ioi Y) :
    inner ℂ (gamma0FourierPoincareTest N r n ρ hρ hcρ hpos) f =
      (2 * (N : ℂ)) * a * cuspBesselTransform ν q Y ρ := by
  rw [gamma0FourierPoincareTest_inner N r Y hY n ρ hρ hcρ hpos hs f]
  have he : (∫ y in Ioi Y, (ρ y / y ^ 2) • (gamma0CuspFourierCoefficient N r Y hY n f) y) =
      ∫ y in Ioi Y, a * cuspBesselTransformIntegrand ν q ρ y := by
    apply integral_congr_ae
    filter_upwards [hf] with y hy
    rw [hy]
    simp only [cuspBesselTransformIntegrand, Complex.real_smul]
    ring
  rw [he, integral_const_mul]
  simp only [cuspBesselTransform, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
  push_cast
  ring

def gamma0CuspBesselAmplitude (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) (r : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) : ℂ :=
  Classical.choose (gamma0FullCuspidalSpectralBasis_fourier_bessel_ae N i r Y hY n hn)

theorem gamma0CuspBesselAmplitude_fourier_ae (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) (r : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) :
    gamma0CuspFourierCoefficient N r Y hY n (gamma0FullCuspidalSpectralBasis N i).val
      =ᵐ[volume.restrict (Ioi Y)] fun y =>
        gamma0CuspBesselAmplitude N i r Y hY n hn *
          cuspBesselKernel (Complex.sqrt (1 / 4 - (gamma0AllHeightGradientSpectralValue N i : ℂ)))
            (|cuspFourierFrequency (N : ℝ) n|) y :=
  Classical.choose_spec (gamma0FullCuspidalSpectralBasis_fourier_bessel_ae N i r Y hY n hn)

theorem gamma0FourierPoincareTest_native_inner (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) (r : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpos : tsupport ρ ⊆ Ioi (0 : ℝ)) (hs : tsupport ρ ⊆ Ioi Y) :
    inner ℂ (gamma0FourierPoincareTest N r n ρ hρ hcρ hpos)
      (gamma0FullCuspidalSpectralBasis N i).val =
        (2 * (N : ℂ)) * gamma0CuspBesselAmplitude N i r Y hY n hn *
          cuspBesselTransform
            (Complex.sqrt (1 / 4 - (gamma0AllHeightGradientSpectralValue N i : ℂ)))
            (|cuspFourierFrequency (N : ℝ) n|) Y ρ :=
  gamma0FourierPoincareTest_inner_of_bessel N r Y hY n _ _ _ _
    (gamma0CuspBesselAmplitude_fourier_ae N i r Y hY n hn) ρ hρ hcρ hpos hs

theorem gamma0FourierPoincareTest_native_projected_inner (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) (r : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpos : tsupport ρ ⊆ Ioi (0 : ℝ)) (hs : tsupport ρ ⊆ Ioi Y) :
    inner ℂ (gamma0CuspidalProjection N (gamma0FourierPoincareTest N r n ρ hρ hcρ hpos))
      (gamma0FullCuspidalSpectralBasis N i) =
        (2 * (N : ℂ)) * gamma0CuspBesselAmplitude N i r Y hY n hn *
          cuspBesselTransform
            (Complex.sqrt (1 / 4 - (gamma0AllHeightGradientSpectralValue N i : ℂ)))
            (|cuspFourierFrequency (N : ℝ) n|) Y ρ := by
  rw [gamma0CuspidalProjection_inner_right]
  exact gamma0FourierPoincareTest_native_inner N i r Y hY n hn ρ hρ hcρ hpos hs

theorem gamma0FourierPoincareTest_native_finite_bessel (N : ℕ) [NeZero N]
    (s : Finset (Gamma0AllHeightSpectralIndex N)) (r : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpos : tsupport ρ ⊆ Ioi (0 : ℝ)) (hs : tsupport ρ ⊆ Ioi Y) :
    ∑ i ∈ s, ‖(2 * (N : ℂ)) * gamma0CuspBesselAmplitude N i r Y hY n hn *
      cuspBesselTransform
        (Complex.sqrt (1 / 4 - (gamma0AllHeightGradientSpectralValue N i : ℂ)))
        (|cuspFourierFrequency (N : ℝ) n|) Y ρ‖ ^ 2 ≤
      ‖gamma0FourierPoincareTest N r n ρ hρ hcρ hpos‖ ^ 2 := by
  have hb := gamma0CuspidalSpectral_finite_bessel N s
    (gamma0FourierPoincareTest N r n ρ hρ hcρ hpos)
  convert hb using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← gamma0FourierPoincareTest_native_inner N i r Y hY n hn ρ hρ hcρ hpos hs,
    norm_inner_symm]

end ArtinMatthews

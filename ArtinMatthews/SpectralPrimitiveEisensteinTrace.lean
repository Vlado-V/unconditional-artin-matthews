module

public import ArtinMatthews.SpectralEisensteinFourierCompact
public import ArtinMatthews.SpectralPrimitiveOrbitalPairing
public import ArtinMatthews.SpectralStoneEisensteinSesquilinear
public import ArtinMatthews.SpectralStoneResidualPair
public import ArtinMatthews.SpectralEisensteinFourierInitial
public import ArtinMatthews.SpectralPrimitiveEisensteinFourier
public import ArtinMatthews.SpectralPrimitiveStonePairing
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

/-! The full compact trace with the continuous term written as actual
one-dimensional unit-height Fourier integrals. The measure is literal
dt/(2*pi) on positive frequencies, and the residual term is retained. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace

namespace ArtinMatthews

def gamma0PrimitiveEisensteinTransform (N : ℕ) [NeZero N] (a r : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (m : ℤ) (s : ℂ) (ρ : ℝ → ℝ) : ℂ :=
  ∫ u in Ioi (Y/(gamma0CuspTrueWidth N r : ℝ)),
    (ρ ((gamma0CuspTrueWidth N r : ℝ)*u)/u^2) •
      gamma0CuspEisensteinFourierCoefficient N a r Y hY m s ((gamma0CuspTrueWidth N r : ℝ)*u)

theorem gamma0PrimitiveEisensteinTransform_integrable (N : ℕ) [NeZero N]
    (a r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m : ℤ) (s : ℂ)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hsρ : tsupport ρ ⊆ Ioi Y) :
    IntegrableOn (fun u => (ρ ((gamma0CuspTrueWidth N r : ℝ)*u)/u^2) •
      gamma0CuspEisensteinFourierCoefficient N a r Y hY m s ((gamma0CuspTrueWidth N r : ℝ)*u))
      (Ioi (Y/(gamma0CuspTrueWidth N r : ℝ))) :=
  spectralFourierHeightPairing_dilation_integrable _ Y
    (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)) hY ρ _
    (gamma0CuspEisensteinFourierCoefficient_compact_integrable N a r Y hY m s ρ hρ hcρ hpρ hsρ)

theorem gamma0PrimitiveEisensteinTransform_eq_test (N : ℕ) [NeZero N]
    (a r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m : ℤ) (s : ℂ)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hsρ : tsupport ρ ⊆ Ioi Y) :
    gamma0PrimitiveEisensteinTransform N a r Y hY m s ρ =
      gamma0CuspEisensteinMeromorphicTest N a
        (gamma0PrimitiveFourierPoincareSeed N r m ρ hρ hcρ hpρ) s :=
  (gamma0PrimitiveEisensteinFourier_unit_test N a r Y hY m s ρ hρ hcρ hpρ hsρ).symm

theorem gamma0PrimitiveEisensteinTransform_initial (N : ℕ) [NeZero N]
    (a r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m : ℤ) (s : ℂ) (hs : 1 < s.re)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hsρ : tsupport ρ ⊆ Ioi Y) :
    gamma0PrimitiveEisensteinTransform N a r Y hY m s ρ =
      ∫ u in Ioi (Y/(gamma0CuspTrueWidth N r : ℝ)),
        (ρ ((gamma0CuspTrueWidth N r : ℝ)*u)/u^2) •
          gamma0UnitCuspFourierMean N r m (gamma0CuspEisenstein N a s) u := by
  let w : ℝ := gamma0CuspTrueWidth N r
  have hw : 0 < w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  let V (y : ℝ) := gamma0UnitCuspFourierMean N r m (gamma0CuspEisenstein N a s) (y/w)
  rw [gamma0PrimitiveEisensteinTransform_eq_test N a r Y hY m s ρ hρ hcρ hpρ hsρ,
    gamma0PrimitiveEisensteinFourier_compact_test N a r Y hY m s ρ hρ hcρ hpρ hsρ]
  change w • (∫ y in Ioi Y,(ρ y/y^2) • gamma0CuspEisensteinFourierCoefficient N a r Y hY m s y) = _
  calc
    _ = w • (∫ y in Ioi Y,(ρ y/y^2) • V y) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [gamma0CuspEisensteinFourierCoefficient_initial_ae N a r Y hY m s hs] with y hy
      rw [hy]
    _ = ∫ u in Ioi (Y/w),(ρ (w*u)/u^2) • V (w*u) :=
      spectralFourierHeightPairing_dilation w Y hw hY ρ V
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _
      dsimp only [V]
      rw [mul_div_cancel_left₀ u hw.ne']
def gamma0PrimitiveEisensteinProduct (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (ρ η : ℝ → ℝ) (t : ℝ) : ℂ :=
  (∑ a : Gamma0EisensteinCuspClasses N,
    gamma0PrimitiveEisensteinTransform N (gamma0EisensteinCuspClassRepresentative N a) r
        Y hY m (eisensteinCriticalPoint t) ρ *
      star (gamma0PrimitiveEisensteinTransform N (gamma0EisensteinCuspClassRepresentative N a) s
        Y hY n (eisensteinCriticalPoint t) η)) / ((2*Real.pi : ℝ) : ℂ)

theorem gamma0PrimitiveEisensteinProduct_eq_integrand (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    (hsρ : tsupport ρ ⊆ Ioi Y) (hsη : tsupport η ⊆ Ioi Y) (t : ℝ) :
    gamma0PrimitiveEisensteinProduct N r s Y hY m n ρ η t =
      gamma0StoneEisensteinPairIntegrand N (gamma0PrimitiveFourierPoincareSeed N r m ρ hρ hcρ hpρ)
        (gamma0PrimitiveFourierPoincareSeed N s n η hη hcη hpη) t := by
  unfold gamma0PrimitiveEisensteinProduct gamma0StoneEisensteinPairIntegrand
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  change gamma0PrimitiveEisensteinTransform N (gamma0EisensteinCuspClassRepresentative N a) r
      Y hY m (eisensteinCriticalPoint t) ρ *
    star (gamma0PrimitiveEisensteinTransform N (gamma0EisensteinCuspClassRepresentative N a) s
      Y hY n (eisensteinCriticalPoint t) η) =
    gamma0CuspEisensteinMeromorphicTest N (gamma0EisensteinCuspClassRepresentative N a)
      (gamma0PrimitiveFourierPoincareSeed N r m ρ hρ hcρ hpρ) (eisensteinCriticalPoint t) *
    star (gamma0CuspEisensteinMeromorphicTest N (gamma0EisensteinCuspClassRepresentative N a)
      (gamma0PrimitiveFourierPoincareSeed N s n η hη hcη hpη) (eisensteinCriticalPoint t))
  rw [gamma0PrimitiveEisensteinTransform_eq_test N _ r Y hY m _ ρ hρ hcρ hpρ hsρ,
    gamma0PrimitiveEisensteinTransform_eq_test N _ s Y hY n _ η hη hcη hpη hsη]

theorem gamma0PrimitiveEisenstein_product_integrable (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    (hsρ : tsupport ρ ⊆ Ioi Y) (hsη : tsupport η ⊆ Ioi Y) :
    IntegrableOn (gamma0PrimitiveEisensteinProduct N r s Y hY m n ρ η) (Ioi 0) := by
  have h := gamma0StoneEisensteinPairIntegrand_integrableOn N
    (gamma0PrimitiveFourierPoincareSeed N r m ρ hρ hcρ hpρ)
    (gamma0PrimitiveFourierPoincareSeed N s n η hη hcη hpη)
  apply h.congr
  exact ae_of_all _ (fun t => (gamma0PrimitiveEisensteinProduct_eq_integrand N r s Y hY m n
    ρ η hρ hη hcρ hcη hpρ hpη hsρ hsη t).symm)

theorem gamma0PrimitiveEisensteinPair_eq_integral (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    (hsρ : tsupport ρ ⊆ Ioi Y) (hsη : tsupport η ⊆ Ioi Y) :
    gamma0StoneEisensteinPair N (gamma0PrimitiveFourierPoincareSeed N r m ρ hρ hcρ hpρ)
      (gamma0PrimitiveFourierPoincareSeed N s n η hη hcη hpη) =
      ∫ t in Ioi 0,gamma0PrimitiveEisensteinProduct N r s Y hY m n ρ η t := by
  change (∫ t in Ioi 0,gamma0StoneEisensteinPairIntegrand N
    (gamma0PrimitiveFourierPoincareSeed N r m ρ hρ hcρ hpρ)
    (gamma0PrimitiveFourierPoincareSeed N s n η hη hcη hpη) t) = _
  apply integral_congr_ae
  exact ae_of_all _ (fun t => (gamma0PrimitiveEisensteinProduct_eq_integrand N r s Y hY m n
    ρ η hρ hη hcρ hcη hpρ hpη hsρ hsη t).symm)

theorem gamma0PrimitiveFourierPoincareTest_full_trace (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    (hsρ : tsupport ρ ⊆ Ioi Y) (hsη : tsupport η ⊆ Ioi Y) :
    let mN := (gamma0CuspFrequencyStep N r : ℤ)*m
    let nN := (gamma0CuspFrequencyStep N s : ℤ)*n
    let ψ := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) mN ρ hρ hcρ hpρ
    let φ := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) nN η hη hcη hpη
    (gamma0PrimitiveFourierScale N r * gamma0PrimitiveFourierScale N s) *
        (2*gamma0ZeroGeometricSum N r s ψ φ) +
      (∑ᶠ c : Ioi (0 : ℕ), gamma0PrimitivePositiveBesselFibre N r s c m n ρ η) =
      (∑' i : Gamma0AllHeightSpectralIndex N,
        gamma0PrimitiveFourierSpectralCoefficient N i r Y hY m hm ρ *
          star (gamma0PrimitiveFourierSpectralCoefficient N i s Y hY n hn η)) +
      ((∫ t in Ioi 0,gamma0PrimitiveEisensteinProduct N r s Y hY m n ρ η t) +
        gamma0StoneResidualPair N (gamma0PrimitiveFourierPoincareTest N r m ρ hρ hcρ hpρ)
          (gamma0PrimitiveFourierPoincareTest N s n η hη hcη hpη)) := by
  dsimp only
  rw [← gamma0PrimitiveEisensteinPair_eq_integral N r s Y hY m n ρ η hρ hη hcρ hcη hpρ hpη hsρ hsη]
  exact gamma0PrimitiveFourierPoincareTest_trace N r s Y hY m n hm hn
    ρ η hρ hη hcρ hcη hpρ hpη hsρ hsη

end ArtinMatthews



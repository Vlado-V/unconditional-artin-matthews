module

public import ArtinMatthews.SpectralCuspDiagonalFourierIntegral
public import ArtinMatthews.SpectralCuspTrueWidth
public import ArtinMatthews.SpectralGeometricSignSectors
public import ArtinMatthews.SpectralCuspWidthParabolicWindow
public import ArtinMatthews.SpectralCuspWidthRefinement
public import ArtinMatthews.SpectralFiniteFunctionIntegrals
public import ArtinMatthews.SpectralOrbitalCompactSupport
public import ArtinMatthews.SpectralSameCuspZeroTranslations
public import Mathlib.Algebra.FiniteSupport.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The exact same-cusp zero modulus contribution for the actual compact
Fourier seeds. The two central signs and the primitive width lattice
produce the literal scalar 2*(N/w)*N on the diagonal. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups InnerProductSpace ContDiff

namespace ArtinMatthews

theorem gamma0CuspWidthTranslation_injective (N : ℕ) [NeZero N] (r : SL(2, ℤ)) :
    Function.Injective (fun k : ℤ => integerTranslation ((gamma0CuspTrueWidth N r : ℤ)*k)) := by
  intro k l h
  have hkl := congrArg (fun M : SL(2, ℤ) => M 0 1) h
  change (gamma0CuspTrueWidth N r : ℤ)*k = (gamma0CuspTrueWidth N r : ℤ)*l at hkl
  exact mul_left_cancel₀ (by exact_mod_cast (gamma0CuspTrueWidth_pos N r).ne') hkl

theorem gamma0ZeroGeometricSum_sameCusp_fourier (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (m n : ℤ) (ρ η : ℝ → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ)) :
    let d := gamma0CuspFrequencyStep N r
    let mN := (d : ℤ)*m
    let nN := (d : ℤ)*n
    let ψ := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) mN ρ hρ hcρ hpρ
    let φ := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) nN η hη hcη hpη
    gamma0ZeroGeometricSum N r r ψ φ =
      if m = n then 2*(d : ℂ)*(N : ℂ)*(cuspFourierHeightPairing ρ η : ℂ) else 0 := by
  dsimp only
  let d := gamma0CuspFrequencyStep N r
  let w := gamma0CuspTrueWidth N r
  let mN := (d : ℤ)*m
  let nN := (d : ℤ)*n
  let ψ := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) mN ρ hρ hcρ hpρ
  let φ := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) nN η hη hcη hpη
  let T (k : ℤ) := integerTranslation ((w : ℤ)*k)
  let F (k : ℤ) (z : UpperHalfPlane) := inner ℂ (ψ.val z) (φ.val (T k • z))
  have hF : Function.HasFiniteSupport F :=
    Function.HasFiniteSupport.fun_comp_of_injective (g := T) (gamma0CuspWidthTranslation_injective N r)
      (compactPoincareIntegrand_hasFiniteSupport ψ φ)
  have hI (k : ℤ) : Integrable (F k) := compactPoincareGeometricKernel_integrable ψ φ (T k)
  have hsum (z : UpperHalfPlane) : (∑ᶠ k : ℤ, F k z) = (d : ℝ) •
      inner ℂ (ψ.val z) (cuspFourierWave N nN η z) := by
    simp only [F,RCLike.inner_apply]
    rw [← finsum_mul,cuspFourierTestSeed_trueWidth_parabolic_finsum N r n η hη hcη hpη]
    simp only [Complex.real_smul]
    ring
  have hd : (d : ℤ) ≠ 0 := by exact_mod_cast (gamma0CuspFrequencyStep_pos N r).ne'
  have he : mN = nN ↔ m = n := ⟨mul_left_cancel₀ hd,fun h => congrArg ((d : ℤ)*·) h⟩
  change gamma0ZeroGeometricSum N r r ψ φ = if m = n then _ else _
  rw [gamma0ZeroGeometricSum_sameCusp_translations N r ψ φ]
  change 2*(∑ᶠ k : ℤ, ∫ z : UpperHalfPlane, F k z) = _
  rw [← finiteFunctionSupport_integral volume F hF hI]
  simp_rw [hsum]
  rw [integral_smul]
  change 2*((d : ℝ) • ∫ z : UpperHalfPlane, inner ℂ
    ((cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) mN ρ hρ hcρ hpρ).val z)
    (cuspFourierWave N nN η z)) = _
  rw [cuspFourierTestSeed_inner_wave N mN nN ρ η hρ hcρ hpρ]
  simp only [he]
  by_cases hmn : m = n
  · simp only [hmn,ite_true,Complex.real_smul,Complex.ofReal_natCast]
    ring
  · simp only [hmn,ite_false,smul_zero,mul_zero]

end ArtinMatthews

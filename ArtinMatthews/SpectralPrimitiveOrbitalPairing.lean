module

public import ArtinMatthews.SpectralPrimitiveFourierPoincare
public import ArtinMatthews.SpectralCuspDiagonalFourierIntegral
public import ArtinMatthews.SpectralOrbitalKloosterman
public import ArtinMatthews.SpectralSameCuspZeroFourierPairing
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

/-! Primitive parabolic normalization of the actual geometric pairing.
Both common-period indices cancel against the seed scales. The signed
zero sector is retained and evaluated explicitly for equal cusps. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace

namespace ArtinMatthews

def gamma0PrimitivePositiveBesselFibre (N : ℕ) [NeZero N] (r s : SL(2, ℤ))
    (c : Ioi (0 : ℕ)) (m n : ℤ) (ρ η : ℝ → ℝ) : ℂ :=
  letI : NeZero c.val := ⟨c.property.ne'⟩
  gamma0TrueWidthKloostermanSum N r s c.val m n *
    gamma0TrueWidthBesselOrbital N r s c.val m n ρ η

theorem gamma0TrueWidthPositiveBesselFibre_primitive (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : Ioi (0 : ℕ)) (m n : ℤ) (ρ η : ℝ → ℝ) :
    (gamma0PrimitiveFourierScale N r * gamma0PrimitiveFourierScale N s * 4) *
      gamma0TrueWidthPositiveBesselFibre N r s c m n ρ η =
        gamma0PrimitivePositiveBesselFibre N r s c m n ρ η := by
  let _ : NeZero c.val := ⟨c.property.ne'⟩
  dsimp only [gamma0TrueWidthPositiveBesselFibre,gamma0TrueWidthBesselGeometricFibre,
    gamma0PrimitivePositiveBesselFibre]
  calc
    _ = (gamma0PrimitiveFourierScale N r * gamma0PrimitiveFourierScale N s *
        (4*((gamma0CuspFrequencyStep N s : ℂ)*(gamma0CuspFrequencyStep N r : ℂ)))) *
        (gamma0TrueWidthKloostermanSum N r s c.val m n *
          gamma0TrueWidthBesselOrbital N r s c.val m n ρ η) := by ring
    _ = _ := by rw [gamma0PrimitiveFourierScale_indices,one_mul]

theorem gamma0PrimitivePositiveBesselFibre_finite (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ)) :
    Function.HasFiniteSupport (fun c : Ioi (0 : ℕ) => gamma0PrimitivePositiveBesselFibre N r s c m n ρ η) := by
  apply (gamma0PositiveGeometricSum_trueWidth_bessel N r s m n hm hn
    ρ η hρ hη hcρ hcη hpρ hpη).1.subset
  intro c hc
  change gamma0TrueWidthPositiveBesselFibre N r s c m n ρ η ≠ 0
  intro hz
  apply hc
  change gamma0PrimitivePositiveBesselFibre N r s c m n ρ η = 0
  rw [← gamma0TrueWidthPositiveBesselFibre_primitive,hz,mul_zero]

theorem gamma0PrimitiveFourierPoincareTest_geometric (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ)) :
    let mN := (gamma0CuspFrequencyStep N r : ℤ)*m
    let nN := (gamma0CuspFrequencyStep N s : ℤ)*n
    let ψ := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) mN ρ hρ hcρ hpρ
    let φ := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) nN η hη hcη hpη
    inner ℂ (gamma0PrimitiveFourierPoincareTest N r m ρ hρ hcρ hpρ)
      (gamma0PrimitiveFourierPoincareTest N s n η hη hcη hpη) =
      (gamma0PrimitiveFourierScale N r * gamma0PrimitiveFourierScale N s) *
        (2*gamma0ZeroGeometricSum N r s ψ φ) +
      ∑ᶠ c : Ioi (0 : ℕ), gamma0PrimitivePositiveBesselFibre N r s c m n ρ η := by
  dsimp only
  rw [gamma0PrimitiveFourierPoincareTest_eq,gamma0PrimitiveFourierPoincareTest_eq,
    inner_smul_left,inner_smul_right,gamma0PrimitiveFourierScale_conj,
    gamma0FourierPoincareTest_sign_sectors]
  rw [(gamma0PositiveGeometricSum_trueWidth_bessel N r s m n hm hn
    ρ η hρ hη hcρ hcη hpρ hpη).2]
  have hSum :
      (gamma0PrimitiveFourierScale N r * gamma0PrimitiveFourierScale N s * 4) *
        (∑ᶠ c : Ioi (0 : ℕ), gamma0TrueWidthPositiveBesselFibre N r s c m n ρ η) =
      ∑ᶠ c : Ioi (0 : ℕ), gamma0PrimitivePositiveBesselFibre N r s c m n ρ η := by
    rw [mul_finsum]
    exact finsum_congr (fun c => gamma0TrueWidthPositiveBesselFibre_primitive N r s c m n ρ η)
  rw [← hSum]
  ring

theorem gamma0PrimitiveFourier_zero_sameCusp (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (m n : ℤ) (ρ η : ℝ → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ)) :
    let mN := (gamma0CuspFrequencyStep N r : ℤ)*m
    let nN := (gamma0CuspFrequencyStep N r : ℤ)*n
    let ψ := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) mN ρ hρ hcρ hpρ
    let φ := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) nN η hη hcη hpη
    (gamma0PrimitiveFourierScale N r * gamma0PrimitiveFourierScale N r) *
      (2*gamma0ZeroGeometricSum N r r ψ φ) =
        if m = n then (gamma0CuspTrueWidth N r : ℂ)*(cuspFourierHeightPairing ρ η : ℂ) else 0 := by
  dsimp only
  rw [gamma0ZeroGeometricSum_sameCusp_fourier N r m n ρ η hρ hη hcρ hcη hpρ hpη]
  split_ifs
  · have hd : (gamma0CuspTrueWidth N r : ℂ)*(gamma0CuspFrequencyStep N r : ℂ) = (N : ℂ) := by
      exact_mod_cast gamma0CuspFrequencyStep_mul_width N r
    calc
      _ = ((gamma0CuspTrueWidth N r : ℂ)*(gamma0CuspFrequencyStep N r : ℂ)) *
          ((gamma0CuspTrueWidth N r : ℂ)*(cuspFourierHeightPairing ρ η : ℂ))/(N : ℂ) := by
        unfold gamma0PrimitiveFourierScale
        push_cast
        field_simp [show (N : ℂ) ≠ 0 by exact_mod_cast NeZero.ne N]
      _ = _ := by
        rw [hd]
        field_simp [show (N : ℂ) ≠ 0 by exact_mod_cast NeZero.ne N]
  · simp

end ArtinMatthews


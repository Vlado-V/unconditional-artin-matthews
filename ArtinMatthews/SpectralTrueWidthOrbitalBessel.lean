module

public import ArtinMatthews.SpectralWeylOrbitalSpectral
public import ArtinMatthews.SpectralTrueWidthKloosterman
public import ArtinMatthews.SpectralTrueWidthOrbitalScaling
public import ArtinMatthews.SpectralKLCuspWidthTransform
public import ArtinMatthews.SpectralTrueWidthOrbitalKloosterman
public import ArtinMatthews.SpectralWeylTwoHeightKernel
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

/-! The actual positive arithmetic orbital fiber has the literal
unregularized J/K Bessel expression in true cusp coordinates.  Both width
indices, the exact modulus and height profiles, and the signed frequencies
are retained. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

def gamma0TrueWidthBesselOrbital (N : ℕ) [NeZero N] (r s : SL(2, ℤ))
    (c : ℕ) (m n : ℤ) (ρ η : ℝ → ℝ) : ℂ :=
  let C := gamma0TrueWidthModulus N r s (c : ℝ)
  let a := |cuspFourierFrequency 1 m|
  let b := |cuspFourierFrequency 1 n|
  let X := Real.sqrt (a*b)*(2/C)
  let f := spectralKLHeightPhysicalTest b (fun y => η ((gamma0CuspTrueWidth N s : ℝ)*y))
  let g := spectralKLHeightPhysicalTest a (fun y => ρ ((gamma0CuspTrueWidth N r : ℝ)*y))
  ((Real.sqrt (a*b)/C^2 : ℝ) : ℂ)*
    (∫ v : ℝ, spectralWeylIntegerSignMultiplier m n v X*spectralKLPhysicalAnalysisIntegral f v*
      star (spectralKLPhysicalAnalysisIntegral g v) ∂spectralKLSpectralMeasure)

def gamma0TrueWidthBesselGeometricFibre (N : ℕ) [NeZero N] (r s : SL(2, ℤ))
    (c : ℕ) [NeZero c] (m n : ℤ) (ρ η : ℝ → ℝ) : ℂ :=
  ((gamma0CuspFrequencyStep N s : ℂ)*(gamma0CuspFrequencyStep N r : ℂ))*
    (gamma0TrueWidthKloostermanSum N r s c m n*gamma0TrueWidthBesselOrbital N r s c m n ρ η)

private theorem spectral_cuspWeylOrbitalIntegrand_congr_modulus (N : ℕ) (m n : ℤ)
    (ρ η : ℝ → ℝ) {C D : ℝ} (he : C = D) (hC : C ≠ 0) (hD : D ≠ 0) :
    cuspWeylOrbitalIntegrand N m n ρ η C hC = cuspWeylOrbitalIntegrand N m n ρ η D hD := by
  subst D
  rfl

theorem gamma0TrueWidthOrbitalKernel_nonzero_bessel (N : ℕ) [NeZero N] (r s : SL(2, ℤ))
    (c : ℕ) [NeZero c] (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ)) :
    cuspWeylOrbitalKernel 1 m n
      (fun y => ρ ((gamma0CuspTrueWidth N r : ℝ)*y)) (fun y => η ((gamma0CuspTrueWidth N s : ℝ)*y))
      (gamma0TrueWidthModulus N r s (c : ℝ))
      (gamma0TrueWidthModulus_ne_zero N r s (by exact_mod_cast NeZero.ne c)) =
        gamma0TrueWidthBesselOrbital N r s c m n ρ η := by
  let R : ℝ → ℝ := fun y => ρ ((gamma0CuspTrueWidth N r : ℝ)*y)
  let E : ℝ → ℝ := fun y => η ((gamma0CuspTrueWidth N s : ℝ)*y)
  let C := gamma0TrueWidthModulus N r s (c : ℝ)
  have hC : 0 < C := gamma0TrueWidthModulus_pos N r s (Nat.cast_pos.mpr (NeZero.pos c))
  have hr : 0 < (gamma0CuspTrueWidth N r : ℝ) := by exact_mod_cast gamma0CuspTrueWidth_pos N r
  have hs : 0 < (gamma0CuspTrueWidth N s : ℝ) := by exact_mod_cast gamma0CuspTrueWidth_pos N s
  obtain ⟨hR,hRc,hRp⟩ := spectral_cusp_width_test_properties _ 0 hr ρ hρ.continuous hcρ hpρ
  obtain ⟨hE,hEc,hEp⟩ := spectral_cusp_width_test_properties _ 0 hs η hη.continuous hcη hpη
  have hRpos : tsupport R ⊆ Ioi (0 : ℝ) := by simpa only [R,zero_div] using hRp
  have hEpos : tsupport E ⊆ Ioi (0 : ℝ) := by simpa only [E,zero_div] using hEp
  have hcz : (c : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne c
  have hI₀ := cuspWeylOrbitalIntegrand_trueWidth_integrable N r s m n ρ η hρ hη hcρ hcη hpρ hpη (c : ℤ) hcz
  have hmod : gamma0TrueWidthModulus N r s (((c : ℤ) : ℝ)) = C := by simp [C]
  have hI : Integrable (cuspWeylOrbitalIntegrand 1 m n R E C hC.ne') := by
    have hcmod := gamma0TrueWidthModulus_ne_zero N r s (by exact_mod_cast hcz : (((c : ℤ) : ℝ)) ≠ 0)
    change Integrable (cuspWeylOrbitalIntegrand 1 m n R E (gamma0TrueWidthModulus N r s (((c : ℤ) : ℝ))) hcmod) at hI₀
    rwa [spectral_cuspWeylOrbitalIntegrand_congr_modulus 1 m n R E hmod hcmod hC.ne'] at hI₀
  simpa only [gamma0TrueWidthBesselOrbital,R,E,C,Nat.cast_one] using!
    cuspWeylOrbitalKernel_nonzero_spectral 1 m n hm hn R E hR hRc hRpos hE hEc hEpos hC
      (weylPlanarDensity_integrable_of_orbital 1 m n R E C hC.ne' hI)

theorem gamma0PositiveGeometricFibre_trueWidth_bessel (N : ℕ) [NeZero N] (r s : SL(2, ℤ))
    (c : ℕ) [NeZero c] (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ)) :
    (∑ᶠ M : gamma0CuspMatrixFibre N r s c, compactPoincareGeometricKernel
      (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
        ((gamma0CuspFrequencyStep N r : ℤ)*m) ρ hρ hcρ hpρ)
      (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
        ((gamma0CuspFrequencyStep N s : ℤ)*n) η hη hcη hpη) M.val) =
      gamma0TrueWidthBesselGeometricFibre N r s c m n ρ η := by
  rw [gamma0PositiveGeometricFibre_trueWidth N r s c m n ρ η hρ hη hcρ hcη hpρ hpη,
    gamma0TrueWidthOrbitalKernel_nonzero_bessel N r s c m n hm hn ρ η hρ hη hcρ hcη hpρ hpη]
  rfl

end ArtinMatthews

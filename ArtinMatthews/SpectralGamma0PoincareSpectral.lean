module

public import ArtinMatthews.SpectralGamma0PoincareBessel
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

/-! A genuine Poincare spectral interface: explicit native Bessel coefficients,
an exact pairing retaining the noncuspidal remainder, and finite-family Bessel
inequalities.  No Kuznetsov or arithmetic large-sieve bound is asserted. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff MatrixGroups InnerProductSpace BigOperators

namespace ArtinMatthews

def gamma0FourierPoincareSpectralCoefficient (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) (r : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) (ρ : ℝ → ℝ) : ℂ :=
  (2 * (N : ℂ)) * gamma0CuspBesselAmplitude N i r Y hY n hn *
    cuspBesselTransform
      (Complex.sqrt (1 / 4 - (gamma0AllHeightGradientSpectralValue N i : ℂ)))
      (|cuspFourierFrequency (N : ℝ) n|) Y ρ

theorem gamma0FourierPoincareSpectralCoefficient_eq_inner (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) (r : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpos : tsupport ρ ⊆ Ioi (0 : ℝ)) (hs : tsupport ρ ⊆ Ioi Y) :
    gamma0FourierPoincareSpectralCoefficient N i r Y hY n hn ρ =
      inner ℂ (gamma0FourierPoincareTest N r n ρ hρ hcρ hpos)
        (gamma0FullCuspidalSpectralBasis N i).val :=
  (gamma0FourierPoincareTest_native_inner N i r Y hY n hn ρ hρ hcρ hpos hs).symm

theorem gamma0FourierPoincareTest_spectral_pairing (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    (hsρ : tsupport ρ ⊆ Ioi Y) (hsη : tsupport η ⊆ Ioi Y) :
    inner ℂ (gamma0FourierPoincareTest N r m ρ hρ hcρ hpρ)
      (gamma0FourierPoincareTest N s n η hη hcη hpη) =
      (∑' i : Gamma0AllHeightSpectralIndex N,
        gamma0FourierPoincareSpectralCoefficient N i r Y hY m hm ρ *
          star (gamma0FourierPoincareSpectralCoefficient N i s Y hY n hn η)) +
      inner ℂ (gamma0NoncuspidalRemainder N (gamma0FourierPoincareTest N r m ρ hρ hcρ hpρ))
        (gamma0NoncuspidalRemainder N (gamma0FourierPoincareTest N s n η hη hcη hpη)) := by
  rw [gamma0_mass_spectral_split N]
  congr 1
  apply tsum_congr
  intro i
  rw [gamma0FourierPoincareSpectralCoefficient_eq_inner N i r Y hY m hm ρ hρ hcρ hpρ hsρ,
    gamma0FourierPoincareSpectralCoefficient_eq_inner N i s Y hY n hn η hη hcη hpη hsη]
  congr 1
  exact (inner_conj_symm _ _).symm

def gamma0FourierPoincarePacket {ι : Type*} (N : ℕ) [NeZero N]
    (t : Finset ι) (c : ι → ℂ) (r : ι → SL(2, ℤ)) (n : ι → ℤ)
    (ρ : ι → ℝ → ℝ) (hρ : ∀ j, ContDiff ℝ ∞ (ρ j))
    (hcρ : ∀ j, HasCompactSupport (ρ j))
    (hpρ : ∀ j, tsupport (ρ j) ⊆ Ioi (0 : ℝ)) : Gamma0RegionL2 N :=
  ∑ j ∈ t, c j • gamma0FourierPoincareTest N (r j) (n j) (ρ j) (hρ j) (hcρ j) (hpρ j)

theorem gamma0FourierPoincarePacket_inner {ι : Type*} (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) (t : Finset ι) (c : ι → ℂ)
    (r : ι → SL(2, ℤ)) (n : ι → ℤ) (hn : ∀ j, n j ≠ 0)
    (Y : ℝ) (hY : 0 < Y) (ρ : ι → ℝ → ℝ) (hρ : ∀ j, ContDiff ℝ ∞ (ρ j))
    (hcρ : ∀ j, HasCompactSupport (ρ j)) (hpρ : ∀ j, tsupport (ρ j) ⊆ Ioi (0 : ℝ))
    (hsρ : ∀ j, tsupport (ρ j) ⊆ Ioi Y) :
    inner ℂ (gamma0FourierPoincarePacket N t c r n ρ hρ hcρ hpρ)
      (gamma0FullCuspidalSpectralBasis N i).val =
        ∑ j ∈ t, star (c j) * gamma0FourierPoincareSpectralCoefficient N i (r j) Y hY (n j) (hn j) (ρ j) := by
  classical
  simp only [gamma0FourierPoincarePacket, sum_inner, inner_smul_left]
  apply Finset.sum_congr rfl
  intro j _
  rw [← gamma0FourierPoincareSpectralCoefficient_eq_inner N i (r j) Y hY (n j)
    (hn j) (ρ j) (hρ j) (hcρ j) (hpρ j) (hsρ j)]
  rfl

theorem gamma0FourierPoincarePacket_finite_bessel {ι : Type*} (N : ℕ) [NeZero N]
    (u : Finset (Gamma0AllHeightSpectralIndex N)) (t : Finset ι) (c : ι → ℂ)
    (r : ι → SL(2, ℤ)) (n : ι → ℤ) (hn : ∀ j, n j ≠ 0)
    (Y : ℝ) (hY : 0 < Y) (ρ : ι → ℝ → ℝ) (hρ : ∀ j, ContDiff ℝ ∞ (ρ j))
    (hcρ : ∀ j, HasCompactSupport (ρ j)) (hpρ : ∀ j, tsupport (ρ j) ⊆ Ioi (0 : ℝ))
    (hsρ : ∀ j, tsupport (ρ j) ⊆ Ioi Y) :
    ∑ i ∈ u, ‖∑ j ∈ t, star (c j) *
      gamma0FourierPoincareSpectralCoefficient N i (r j) Y hY (n j) (hn j) (ρ j)‖ ^ 2 ≤
      ‖gamma0FourierPoincarePacket N t c r n ρ hρ hcρ hpρ‖ ^ 2 := by
  have hb := gamma0CuspidalSpectral_finite_bessel N u
    (gamma0FourierPoincarePacket N t c r n ρ hρ hcρ hpρ)
  convert hb using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← gamma0FourierPoincarePacket_inner N i t c r n hn Y hY ρ hρ hcρ hpρ hsρ,
    norm_inner_symm]

end ArtinMatthews

module

public import ArtinMatthews.SpectralOrbitalFirstUnfolding
public import ArtinMatthews.SpectralPoincareGeometricKernel
public import ArtinMatthews.SpectralFiniteFunctionIntegrals
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Both horizontal windows are removed by genuine finite function-support
exchanges and invariant-measure translations. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff InnerProductSpace

namespace ArtinMatthews

theorem spectralHorizontalPartition_lattice_neg_finsum {w : ℝ} (hw : 0 < w) (x : ℝ) :
    (∑ᶠ k : ℤ, spectralHorizontalPartition w (x - w*k)) = 1 := by
  have h := finsum_comp_equiv
    (f := fun k : ℤ => spectralHorizontalPartition w (x + w*k)) (Equiv.neg ℤ)
  have he : (∑ᶠ k : ℤ, spectralHorizontalPartition w (x - w*k)) =
      ∑ᶠ k : ℤ, spectralHorizontalPartition w (x + w*k) := by
    simpa only [Equiv.neg_apply,Int.cast_neg,mul_neg,sub_eq_add_neg] using h
  rw [he,spectralHorizontalPartition_lattice_finsum hw]

def cuspUnwindowedOrbitalIntegrand (N : ℕ) (m n : ℤ) (ρ η : ℝ → ℝ)
    (R : SL(2, ℤ)) (z : UpperHalfPlane) : ℂ :=
  inner ℂ (cuspFourierWave N m ρ z) (cuspFourierWave N n η (R • z))

def cuspUnwindowedOrbitalKernel (N : ℕ) (m n : ℤ) (ρ η : ℝ → ℝ) (R : SL(2, ℤ)) : ℂ :=
  ∫ z : UpperHalfPlane, cuspUnwindowedOrbitalIntegrand N m n ρ η R z

theorem cuspTranslatedOrbitalIntegrand_finsum (N : ℕ) [NeZero N]
    (m n : ℤ) (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (R : SL(2, ℤ)) (z : UpperHalfPlane) :
    (∑ᶠ k : ℤ, cuspTranslatedOrbitalIntegrand N
      (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) m ρ hρ hcρ hpρ)
      n η R k z) = cuspUnwindowedOrbitalIntegrand N m n ρ η R z := by
  have he (k : ℤ) : cuspTranslatedOrbitalIntegrand N
      (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) m ρ hρ hcρ hpρ)
      n η R k z = spectralHorizontalPartition (N : ℝ) (z.re - (N : ℝ)*k) •
        cuspUnwindowedOrbitalIntegrand N m n ρ η R z := by
    unfold cuspTranslatedOrbitalIntegrand cuspUnwindowedOrbitalIntegrand
    have ht := cuspFourierTestSeed_period_translate N m ρ hρ hcρ hpρ (-k) z
    simp only [mul_neg,Int.cast_neg,sub_eq_add_neg] at ht ⊢
    rw [ht]
    change inner ℂ ((spectralHorizontalPartition (N : ℝ) (z.re + -((N : ℝ)*k)) : ℂ) •
      cuspFourierWave N m ρ z) (cuspFourierWave N n η (R • z)) = _
    exact inner_smul_real_left _ _ _
  simp_rw [he]
  rw [← finsum_smul,spectralHorizontalPartition_lattice_neg_finsum (Nat.cast_pos.mpr (NeZero.pos N)),one_smul]

theorem cuspUnwindowedOrbitalIntegrand_integrable (N : ℕ) [NeZero N]
    (m n : ℤ) (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    (R : SL(2, ℤ)) (hR : R 1 0 ≠ 0) :
    Integrable (cuspUnwindowedOrbitalIntegrand N m n ρ η R) := by
  let ψ := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) m ρ hρ hcρ hpρ
  have h := finiteFunctionSupport_integrable volume (cuspTranslatedOrbitalIntegrand N ψ n η R)
    (cuspTranslatedOrbitalIntegrand_hasFiniteSupport N ψ n η hη hcη hpη R hR)
    (cuspTranslatedOrbitalIntegrand_integrable N ψ n η hη hcη hpη R hR)
  apply h.congr
  exact Eventually.of_forall (cuspTranslatedOrbitalIntegrand_finsum N m n ρ η hρ hcρ hpρ R)

theorem cuspOrbitalIntegral_eq_unwindowed (N : ℕ) [NeZero N]
    (m n : ℤ) (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    (R : SL(2, ℤ)) (hR : R 1 0 ≠ 0) :
    (∑ᶠ p : ℤ × ℤ, compactPoincareGeometricKernel
      (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) m ρ hρ hcρ hpρ)
      (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) n η hη hcη hpη)
      (integerTranslation ((N : ℤ)*p.1) * R * integerTranslation ((N : ℤ)*p.2))) =
      cuspUnwindowedOrbitalKernel N m n ρ η R := by
  let ψ := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) m ρ hρ hcρ hpρ
  let φ := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) n η hη hcη hpη
  let F := cuspOrbitalIntegrand N ψ φ R
  let G := cuspPartialOrbitalIntegrand N ψ n η R
  let H := cuspTranslatedOrbitalIntegrand N ψ n η R
  have hF := cuspOrbitalIntegrand_hasFiniteSupport N ψ φ R hR
  have hG := cuspPartialOrbitalIntegrand_hasFiniteSupport N ψ n η hη hcη hpη R hR
  have hH := cuspTranslatedOrbitalIntegrand_hasFiniteSupport N ψ n η hη hcη hpη R hR
  calc
    _ = ∑ᶠ p : ℤ × ℤ, ∫ z, F p z := by
      have he := finsum_comp_equiv (f := fun p : ℤ × ℤ => compactPoincareGeometricKernel ψ φ
        (integerTranslation ((N : ℤ)*p.1) * R * integerTranslation ((N : ℤ)*p.2))) (Equiv.prodComm ℤ ℤ)
      exact he.symm
    _ = ∫ z, ∑ᶠ p : ℤ × ℤ, F p z :=
      (finiteFunctionSupport_integral volume F hF (cuspOrbitalIntegrand_integrable N ψ φ R)).symm
    _ = ∫ z, ∑ᶠ k : ℤ, G k z := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [finsum_curry _ (finiteFunctionSupport_eval F hF z)]
      apply finsum_congr
      intro k
      exact (cuspPartialOrbitalIntegrand_finsum N ψ n η hη hcη hpη R k z).symm
    _ = ∑ᶠ k : ℤ, ∫ z, G k z :=
      finiteFunctionSupport_integral volume G hG
        (cuspPartialOrbitalIntegrand_integrable N ψ n η hη hcη hpη R hR)
    _ = ∑ᶠ k : ℤ, ∫ z, H k z := by
      apply finsum_congr
      intro k
      exact cuspPartialOrbitalIntegral_translate N ψ n η R k
    _ = ∫ z, ∑ᶠ k : ℤ, H k z :=
      (finiteFunctionSupport_integral volume H hH
        (cuspTranslatedOrbitalIntegrand_integrable N ψ n η hη hcη hpη R hR)).symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (cuspTranslatedOrbitalIntegrand_finsum N m n ρ η hρ hcρ hpρ R)

end ArtinMatthews

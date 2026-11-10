module

public import ArtinMatthews.SpectralPrimitiveKTransform
public import ArtinMatthews.SpectralAnalyticNonzeroGerm
public import ArtinMatthews.SpectralPrimitiveEisensteinBessel
public import ArtinMatthews.SpectralPrimitiveEisensteinDeterminant
public import ArtinMatthews.SpectralPrimitiveKProbe
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

/-! A genuine scalar meromorphic Fourier amplitude is obtained from one
proved nonzero compact K probe. Its factorization for every compact test
is derived from the actual determinant identity. -/

noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups ContDiff Topology

namespace ArtinMatthews

def gamma0PrimitiveFourierProbe (N : ℕ) [NeZero N] (r : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) : ℝ → ℝ :=
  Classical.choose (gamma0PrimitiveKTransform_exists_nonzero_probe N r Y hY n hn (2 : ℂ) (by norm_num))

theorem gamma0PrimitiveFourierProbe_spec (N : ℕ) [NeZero N] (r : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) :
    let ρ := gamma0PrimitiveFourierProbe N r Y hY n hn
    ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ tsupport ρ ⊆ Ioi Y ∧
      gamma0PrimitiveKTransform N r Y n ρ (2 : ℂ) ≠ 0 :=
  Classical.choose_spec (gamma0PrimitiveKTransform_exists_nonzero_probe N r Y hY n hn (2 : ℂ) (by norm_num))

def gamma0PrimitiveFourierAmplitude (N : ℕ) [NeZero N] (a r : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) (s : ℂ) : ℂ :=
  let ρ := gamma0PrimitiveFourierProbe N r Y hY n hn
  gamma0PrimitiveEisensteinTransform N a r Y hY n s ρ/gamma0PrimitiveKTransform N r Y n ρ s

theorem gamma0PrimitiveFourierAmplitude_meromorphic (N : ℕ) [NeZero N]
    (a r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) :
    Meromorphic (gamma0PrimitiveFourierAmplitude N a r Y hY n hn) := by
  obtain ⟨hρ,hcρ,hsρ,_⟩ := gamma0PrimitiveFourierProbe_spec N r Y hY n hn
  have hpρ : tsupport (gamma0PrimitiveFourierProbe N r Y hY n hn) ⊆ Ioi (0 : ℝ) :=
    fun y hy => hY.trans (hsρ hy)
  exact (gamma0PrimitiveEisensteinTransform_meromorphic N a r Y hY n _ hρ hcρ hpρ hsρ).div
    (fun s => (gamma0PrimitiveKTransform_analytic N r Y hY n hn _ hρ hcρ hsρ s (mem_univ s)).meromorphicAt)

theorem gamma0PrimitiveFourierProbe_nonzero_germ (N : ℕ) [NeZero N] (r : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) (s : ℂ) :
    ∀ᶠ z in 𝓝[≠] s,
      gamma0PrimitiveKTransform N r Y n (gamma0PrimitiveFourierProbe N r Y hY n hn) z ≠ 0 := by
  obtain ⟨hρ,hcρ,hsρ,hne⟩ := gamma0PrimitiveFourierProbe_spec N r Y hY n hn
  exact spectralAnalytic_nonzero_germ_of_value _
    (gamma0PrimitiveKTransform_analytic N r Y hY n hn _ hρ hcρ hsρ) (2 : ℂ) hne s

theorem gamma0PrimitiveFourierAmplitude_factorization_germ (N : ℕ) [NeZero N]
    (a r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hsρ : tsupport ρ ⊆ Ioi Y) (s : ℂ) :
    ∀ᶠ z in 𝓝[≠] s, gamma0PrimitiveEisensteinTransform N a r Y hY n z ρ =
      gamma0PrimitiveFourierAmplitude N a r Y hY n hn z*gamma0PrimitiveKTransform N r Y n ρ z := by
  obtain ⟨hη,hcη,hsη,_⟩ := gamma0PrimitiveFourierProbe_spec N r Y hY n hn
  have hd := gamma0PrimitiveEisenstein_K_determinant_germ N a r Y hY n hn
    ρ (gamma0PrimitiveFourierProbe N r Y hY n hn) hρ hη hcρ hcη hsρ hsη s
  filter_upwards [hd,gamma0PrimitiveFourierProbe_nonzero_germ N r Y hY n hn s] with z hz hne
  unfold gamma0PrimitiveFourierAmplitude
  dsimp only
  calc
    _ = (gamma0PrimitiveEisensteinTransform N a r Y hY n z ρ*
        gamma0PrimitiveKTransform N r Y n (gamma0PrimitiveFourierProbe N r Y hY n hn) z)/
        gamma0PrimitiveKTransform N r Y n (gamma0PrimitiveFourierProbe N r Y hY n hn) z :=
      (mul_div_cancel_right₀ _ hne).symm
    _ = _ := by rw [hz]; ring

theorem gamma0PrimitiveFourierAmplitude_initial_germ (N : ℕ) [NeZero N]
    (a r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (s : ℂ) (hs : 1 < s.re) :
    ∀ᶠ z in 𝓝[≠] s,
      gamma0PrimitiveFourierAmplitude N a r Y hY n hn z = gamma0CuspInitialFourierAmplitude N r a n z := by
  obtain ⟨hρ,hcρ,hsρ,_⟩ := gamma0PrimitiveFourierProbe_spec N r Y hY n hn
  have hpρ : tsupport (gamma0PrimitiveFourierProbe N r Y hY n hn) ⊆ Ioi (0 : ℝ) :=
    fun y hy => hY.trans (hsρ hy)
  have hnear : ∀ᶠ z in 𝓝 s, 1 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,
    gamma0PrimitiveFourierProbe_nonzero_germ N r Y hY n hn s] with z hz hne
  unfold gamma0PrimitiveFourierAmplitude
  dsimp only
  rw [gamma0PrimitiveEisensteinTransform_initial_factor N a r Y hY n hn z hz _ hρ hcρ hpρ hsρ,
    mul_div_cancel_right₀ _ hne]

end ArtinMatthews

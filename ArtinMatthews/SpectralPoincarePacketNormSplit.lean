module

public import ArtinMatthews.SpectralGamma0PoincareSpectral
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

/-! The real norm-square identity for the genuine cusp projection.
The complementary ambient mass occurs as its actual nonnegative
norm square, including for a compact Fourier Poincare packet. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace BigOperators

namespace ArtinMatthews

theorem gamma0_mass_spectral_normsq (N : ℕ) [NeZero N] (f : Gamma0RegionL2 N) :
    Summable (fun i : Gamma0AllHeightSpectralIndex N =>
      ‖inner ℂ f (gamma0FullCuspidalSpectralBasis N i).val‖^2) ∧
    ‖f‖^2 = (∑' i : Gamma0AllHeightSpectralIndex N,
      ‖inner ℂ f (gamma0FullCuspidalSpectralBasis N i).val‖^2) +
        ‖gamma0NoncuspidalRemainder N f‖^2 := by
  let b (i : Gamma0AllHeightSpectralIndex N) := inner ℂ f (gamma0FullCuspidalSpectralBasis N i).val
  have hterm (i : Gamma0AllHeightSpectralIndex N) :
      (b i * inner ℂ (gamma0FullCuspidalSpectralBasis N i).val f).re = ‖b i‖^2 := by
    rw [← inner_conj_symm (gamma0FullCuspidalSpectralBasis N i).val f]
    change (b i * (starRingEnd ℂ) (b i)).re = _
    rw [mul_comm,← Complex.normSq_eq_conj_mul_self,Complex.ofReal_re,Complex.normSq_eq_norm_sq]
  have hs := Complex.reCLM.hasSum (gamma0CuspidalProjection_spectral_hasSum N f f)
  change HasSum (fun i => (b i*inner ℂ (gamma0FullCuspidalSpectralBasis N i).val f).re)
    (inner ℂ (gamma0CuspidalProjection N f) (gamma0CuspidalProjection N f)).re at hs
  simp only [hterm] at hs
  refine ⟨hs.summable,?_⟩
  rw [hs.tsum_eq,← inner_self_eq_norm_sq (𝕜 := ℂ) f,
    ← inner_self_eq_norm_sq (𝕜 := ℂ) (gamma0NoncuspidalRemainder N f)]
  change (inner ℂ f f).re = (inner ℂ (gamma0CuspidalProjection N f) (gamma0CuspidalProjection N f)).re +
    (inner ℂ (gamma0NoncuspidalRemainder N f) (gamma0NoncuspidalRemainder N f)).re
  simpa only [Complex.add_re] using congrArg Complex.re (gamma0_mass_cuspidal_split N f f)

theorem gamma0FourierPoincarePacket_spectral_normsq {ι : Type*} (N : ℕ) [NeZero N]
    (t : Finset ι) (α : ι → ℂ) (r : ι → SL(2, ℤ)) (n : ι → ℤ) (hn : ∀ j, n j ≠ 0)
    (Y : ℝ) (hY : 0 < Y) (ρ : ι → ℝ → ℝ) (hρ : ∀ j, ContDiff ℝ ∞ (ρ j))
    (hcρ : ∀ j, HasCompactSupport (ρ j)) (hpρ : ∀ j, tsupport (ρ j) ⊆ Ioi (0 : ℝ))
    (hsρ : ∀ j, tsupport (ρ j) ⊆ Ioi Y) :
    let P := gamma0FourierPoincarePacket N t α r n ρ hρ hcρ hpρ
    let C (i : Gamma0AllHeightSpectralIndex N) := ∑ j ∈ t, star (α j)*
      gamma0FourierPoincareSpectralCoefficient N i (r j) Y hY (n j) (hn j) (ρ j)
    Summable (fun i => ‖C i‖^2) ∧
      ‖P‖^2 = (∑' i : Gamma0AllHeightSpectralIndex N, ‖C i‖^2) +
        ‖gamma0NoncuspidalRemainder N P‖^2 := by
  dsimp only
  simpa only [gamma0FourierPoincarePacket_inner N _ t α r n hn Y hY ρ hρ hcρ hpρ hsρ] using
    gamma0_mass_spectral_normsq N (gamma0FourierPoincarePacket N t α r n ρ hρ hcρ hpρ)

end ArtinMatthews

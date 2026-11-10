module

public import ArtinMatthews.SourceQuadraticB3SignedAssembly
public import ArtinMatthews.SourceQuadraticDiagonalResidue
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain QuadraticScale
open scoped NumberField Classical
noncomputable section

private theorem signed_re_le_norms (d e t s r : ℂ) :
    (d + e + t - s + r).re ≤ ‖d‖ + ‖e‖ + ‖t‖ + ‖s‖ + ‖r‖ := by
  have hs : -s.re ≤ ‖s‖ := (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  simp only [Complex.add_re, Complex.sub_re]
  linarith [Complex.re_le_norm d, Complex.re_le_norm e, Complex.re_le_norm t,
    Complex.re_le_norm r]

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀

theorem sourceQuadraticB3Block_re_le_component_norms {M K σ τ : ℝ}
    (hM : 0 < M) (hK : 0 ≤ K) (hσ : 0 < σ) (hσone : σ < 1)
    (hτ : 0 < τ) (hτone : τ < 1)
    (cols : Finset E) (u : E → ℂ) (g : E)
    (hcols : ∀ b ∈ cols, sourceReflectionIsSquarefree b) :
    (sourceQuadraticB3Block F S₀ hζ (sourceQuadraticB2Rows F S₀ M K) cols
        (sourceQuadraticB2RowWeight F S₀ M) u g).re ≤
      ‖sourceQuadraticZeroResidualBlock F S₀
          (sourceQuadraticBlockIdealFull F S₀ hζ M g) cols u g‖ +
        ‖sourceQuadraticNonzeroResidualBlock F S₀
          (sourceQuadraticDualDivisorError F S₀ hζ M K τ g) cols u g‖ +
        ‖sourceQuadraticNonzeroResidualBlock F S₀
          (sourceQuadraticDualDivisorTail F S₀ hζ M K g) cols u g‖ +
        ‖sourceQuadraticOriginalSmallErrorBlock F S₀ hζ M K σ cols u g‖ +
        ‖sourceQuadraticCommonPairBlock F S₀ (fun e =>
          sourceQuadraticDualDivisorResidue F S₀ hζ M K g e -
          sourceQuadraticOriginalSmallResidue F S₀ hζ M K g e) cols u g‖ := by
  rw [sourceQuadraticB3Block_signed_components F S₀ hζ hM hK hσ hσone hτ hτone cols u g hcols]
  exact (sourceQuadratic_sub_fullResidueDiagonal_re_le F S₀ hζ hM K cols u g _).trans
    (signed_re_le_norms _ _ _ _ _)

end
end ArtinMatthews.SourceEulerAssembly

module

public import ArtinMatthews.SourcePoissonPhysicalScalars
public import ArtinMatthews.SourcePoissonResidueDescent
public import ArtinMatthews.SourcePoissonOriginalSeries
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
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization
open SourcePhysical VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "S" => sourceHilbertSet F S₀
local notation "T" => sourceHilbertSeed F S₀
local notation "R" => PrincipalIntegerRing T
local notation "a" => (sourcePrimeExponentGenerator F hζ S₀ : SourcePrimeExponents F S₀ → R)
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "C" => ReflectionSquarefreeExponents F S₀
local notation "E" => SourcePrimeExponents F S₀

/-- The original S-integer sum for one pair of exterior moduli, as an actual
periodic weight times the original compact test. -/
def sourcePoissonPrimalBlock (s A : E) (t : SNormOne F S) (V : ℝ) : ℂ :=
  ∑' m : R, sourcePoissonNormalizedQuotientWeight F S₀ hζ s A
      (Ideal.Quotient.mk (Ideal.span {a s * a A} : Ideal R) m) *
    sourcePoissonOriginalTest F S₀ hζ t V m

variable [IsTotallyComplex F] {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)

/-- Expanded physical density with one literal periodic S-integer sum for
each original pair `(s,c*n³)`. -/
def sourcePoissonPrimalExpandedDensity
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    (X Y Z : ℝ) (t : SNormOne F S) : ℂ :=
  (Y : ℂ)⁻¹ * ∑' s : E, sourceProbeW1Complex ((q s : ℝ) / Y) *
    ((Real.sqrt ((q s : ℝ) * X) : ℂ)⁻¹ * ∑' p : C × E,
      sourcePoissonPhysicalGaussianCoefficient F S₀ hζ η hBad p.1 p.2 Z *
        sourcePoissonPrimalBlock F S₀ hζ s (p.1.val + 3 • p.2) t ((q s : ℝ) * X))

theorem sourcePoissonOriginalDensity_eq_primalExpanded
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    (X Y Z : ℝ) (hZ : 0 < Z) (t : SNormOne F S)
    (hTest : ∀ s : E, Summable fun m : R =>
      ‖sourcePoissonOriginalTest F S₀ hζ t ((q s : ℝ) * X) m‖) :
    sourcePoissonOriginalDensity F S₀ hζ η hBad X Y Z t =
      sourcePoissonPrimalExpandedDensity F S₀ hζ η hBad X Y Z t := by
  let g (s : E) (m : R) :=
    (sourcePoissonOriginalGauss F S₀ hζ s (-m) / (Real.sqrt (q s : ℝ) : ℂ)) *
      sourcePoissonOriginalTest F S₀ hζ t ((q s : ℝ) * X) m
  let D (p : C × E) := sourcePoissonPhysicalGaussianCoefficient F S₀ hζ η hBad p.1 p.2 Z
  let b (s : E) (p : C × E) (m : R) :=
    sourcePoissonNormalizedQuotientWeight F S₀ hζ s (p.1.val + 3 • p.2)
      (Ideal.Quotient.mk (Ideal.span {a s * a (p.1.val + 3 • p.2)} : Ideal R) m) *
      sourcePoissonOriginalTest F S₀ hζ t ((q s : ℝ) * X) m
  have hTerm (s : E) (p : C × E) (m : R) :
      g s m * reflectionCoefficientTerm F hζ S₀ hBad η p.1 p.2 m Z =
      D p * b s p m := by
    rw [← sourcePoissonPhysicalGaussianCoefficient_mul_residue F S₀ hζ η hBad p.1 p.2 m Z]
    dsimp only [g, b, D]
    rw [sourcePoissonNormalizedQuotientWeight_mk F S₀ hζ]
    ac_rfl
  have hBlock (s : E) :
      (∑' m : R, g s m * reflectionCoefficientRow F hζ S₀ hBad η m Z) =
      ∑' p : C × E, D p * sourcePoissonPrimalBlock F S₀ hζ s (p.1.val + 3 • p.2) t
        ((q s : ℝ) * X) := by
    have hG : Summable (fun m : R => ‖g s m‖) :=
      sourcePoissonOriginalGauss_test_summable_norm F S₀ hζ s t ((q s : ℝ) * X) (hTest s)
    refine (sourcePoissonOriginalCoefficient_expand F S₀ hζ η hBad hZ (g s) hG).trans ?_
    apply tsum_congr
    intro p
    calc
      _ = ∑' m : R, D p * b s p m := tsum_congr (hTerm s p)
      _ = _ := by
        rw [tsum_mul_left]
        rfl
  let H (s : E) (z : ℂ) := sourceProbeW1Complex ((q s : ℝ) / Y) *
    ((Real.sqrt ((q s : ℝ) * X) : ℂ)⁻¹ * z)
  have hOuter :
      (∑' s : E, H s (∑' m : R, g s m * reflectionCoefficientRow F hζ S₀ hBad η m Z)) =
      ∑' s : E, H s (∑' p : C × E, D p *
        sourcePoissonPrimalBlock F S₀ hζ s (p.1.val + 3 • p.2) t ((q s : ℝ) * X)) :=
    tsum_congr fun s => congrArg (H s) (hBlock s)
  exact congrArg (fun z : ℂ => (Y : ℂ)⁻¹ * z) hOuter

end
end ArtinMatthews.SourceEulerAssembly

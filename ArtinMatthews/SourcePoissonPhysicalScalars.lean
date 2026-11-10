module

public import ArtinMatthews.ReflectionCoefficientRow
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
import ArtinMatthews.QuotientPeriodization


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SourcePhysical VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical
noncomputable section

/-- The exact index, dilation and finite Fourier factors in physical Poisson. -/
theorem sourcePoissonPhysicalDilationFactor {X qs qA : ℝ}
    (hX : 0 < X) (hs : 0 < qs) (hA : 0 < qA) :
    (Real.sqrt (qs * X))⁻¹ * ((qs * X) / (qs * qA)) * Real.sqrt qs =
      Real.sqrt X / qA := by
  have hs' := (Real.sqrt_pos.mpr hs).ne'
  have hX' := (Real.sqrt_pos.mpr hX).ne'
  rw [Real.sqrt_mul hs.le]
  field_simp [hs.ne', hA.ne', hs', hX']
  exact (Real.sq_sqrt hX.le).symm

theorem sourcePoissonPhysicalDilationFactor_complex {X qs qA : ℝ}
    (hX : 0 < X) (hs : 0 < qs) (hA : 0 < qA) :
    (Real.sqrt (qs * X) : ℂ)⁻¹ * (((qs * X) / (qs * qA) : ℝ) : ℂ) *
      (Real.sqrt qs : ℂ) = ((Real.sqrt X / qA : ℝ) : ℂ) := by
  exact_mod_cast sourcePoissonPhysicalDilationFactor hX hs hA

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)

/-- The Gaussian factor independent of the original lattice point. -/
def sourcePoissonPhysicalGaussianCoefficient
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    (c : ReflectionSquarefreeExponents F S₀) (n : SourcePrimeExponents F S₀)
    (Z : ℝ) : ℂ :=
  let A := c.val + 3 • n
  reflectionGammaTwo F hζ S₀ c.val /
      ((Real.sqrt (sourcePrimeExponentNorm F S₀ c.val : ℝ) : ℂ) *
        (sourcePrimeExponentNorm F S₀ n : ℂ)) *
    reflectionThetaValue F hζ S₀ hBad η A *
    (reflectionGaussian ((sourcePrimeExponentNorm F S₀ A : ℝ) / Z) : ℂ)

theorem sourcePoissonPhysicalGaussianCoefficient_mul_residue
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    (c : ReflectionSquarefreeExponents F S₀) (n : SourcePrimeExponents F S₀)
    (m : sourceRing F S₀) (Z : ℝ) :
    sourcePoissonPhysicalGaussianCoefficient F S₀ hζ η hBad c n Z *
      reflectionExponentResidueValue F hζ S₀ (c.val + 3 • n) m =
    reflectionCoefficientTerm F hζ S₀ hBad η c n m Z := by
  unfold sourcePoissonPhysicalGaussianCoefficient reflectionCoefficientTerm
  dsimp only
  ac_rfl

end
end ArtinMatthews.SourceEulerAssembly

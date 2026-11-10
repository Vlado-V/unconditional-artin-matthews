module

public import ArtinMatthews.SourceKPTraceJacquetUnfolding
public import ArtinMatthews.SourceAdelicScalarHaar
public import ArtinMatthews.SourceKPAdelicTorusUpper
public import ArtinMatthews.SourceKPAutomorphicEisenstein
public import ArtinMatthews.SourceKPIntertwinerRationalKernel
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

/-! Rational diagonal covariance of the actual nonzero Fourier coefficient.
The negative trace character, principal adelic multiplication and normalized
fundamental-domain integral retain their original conventions. -/
namespace ArtinMatthews

open NumberField MeasureTheory
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance sourceKPJacquetRationalMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance sourceKPJacquetRationalBorel : BorelSpace 𝔸[K] := ⟨rfl⟩

theorem sourceKPTraceJacquetCharacter_principal_mul (m a : Kˣ) (y : 𝔸[K]) :
    sourceKPTraceJacquetCharacter K m (algebraMap K 𝔸[K] (a : K) * y) =
      sourceKPTraceJacquetCharacter K (m * a) y := by
  simp only [sourceKPTraceJacquetCharacter, Units.val_mul, map_mul, mul_assoc]

theorem sourceKPAdelicCompactEisenstein_upper_rational_diagonal (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (a : Kˣ) (y : 𝔸[K]) :
    sourceKPAdelicCompactEisenstein K hζ s
      (sourceKPAdelicUpperLift K hζ (algebraMap K 𝔸[K] (a : K) * y) *
        (sourceKPAdelicProjectiveRationalLift K hζ (sourceKPProjectiveDiagonalHom K a) * g)) =
      sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicUpperLift K hζ y * g) := by
  have hu := sourceKPAdelicProjectiveDiagonalLift_upper K hζ
    (IdeleGroup.unitEmbedding (𝓞 K) K a) y
  rw [← sourceKPAdelicProjectiveRationalLift_diagonal] at hu
  change sourceKPAdelicProjectiveRationalLift K hζ (sourceKPProjectiveDiagonalHom K a) *
    sourceKPAdelicUpperLift K hζ y =
      sourceKPAdelicUpperLift K hζ (algebraMap K 𝔸[K] (a : K) * y) *
        sourceKPAdelicProjectiveRationalLift K hζ (sourceKPProjectiveDiagonalHom K a) at hu
  rw [← mul_assoc, ← hu, mul_assoc,
    sourceKPAdelicCompactEisenstein_rational_invariant]

theorem sourceKPAdelicTraceJacquetKernel_rational_diagonal (m a : Kˣ) (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (y : 𝔸[K]) :
    sourceKPAdelicTraceJacquetKernel K hζ m s
      (sourceKPAdelicProjectiveRationalLift K hζ (sourceKPProjectiveDiagonalHom K a) * g)
      (algebraMap K 𝔸[K] (a : K) * y) =
      sourceKPAdelicTraceJacquetKernel K hζ (m * a) s g y := by
  unfold sourceKPAdelicTraceJacquetKernel
  rw [sourceKPTraceJacquetCharacter_principal_mul,
    sourceKPAdelicIntertwiningKernel_rational_diagonal, ← mul_assoc, ← map_mul,
    Units.inv_mul, map_one, one_mul]

theorem sourceKPAdelicTraceJacquetKernel_integral_rational_diagonal
    (m a : Kˣ) (s : ℂ) (g : SourceKPAdelicProjective K hζ) :
    (∫ y, sourceKPAdelicTraceJacquetKernel K hζ (m * a) s g y ∂sourceKPAdelicTraceProduct K) =
      ∫ y, sourceKPAdelicTraceJacquetKernel K hζ m s
        (sourceKPAdelicProjectiveRationalLift K hζ (sourceKPProjectiveDiagonalHom K a) * g) y
        ∂sourceKPAdelicTraceProduct K := by
  have hp : MeasurePreserving (fun y : 𝔸[K] => algebraMap K 𝔸[K] (a : K) * y)
      (sourceKPAdelicTraceProduct K) (sourceKPAdelicTraceProduct K) := by
    rw [sourceKPAdelicTraceProduct_eq_standard_of_primitiveRoot K hζ]
    exact sourceKPAdelicStandardHaar_principal_mul K a
  calc
    _ = ∫ y, sourceKPAdelicTraceJacquetKernel K hζ m s
        (sourceKPAdelicProjectiveRationalLift K hζ (sourceKPProjectiveDiagonalHom K a) * g)
        (algebraMap K 𝔸[K] (a : K) * y) ∂sourceKPAdelicTraceProduct K :=
      integral_congr_ae (Filter.Eventually.of_forall fun y =>
        (sourceKPAdelicTraceJacquetKernel_rational_diagonal K hζ m a s g y).symm)
    _ = _ := hp.integral_comp (sourceKPAdelicPrincipalMul_measurableEmbedding K a) _

theorem sourceKPAdelicCompactEisenstein_traceJacquet_rational_diagonal_frequency
    {s : ℂ} (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1)
    (m a : Kˣ) (g : SourceKPAdelicProjective K hζ) :
    (∫ y in sourceKPAdelicFundamentalDomain K,
      sourceKPTraceJacquetCharacter K (m * a) y *
        sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicUpperLift K hζ y * g)
      ∂sourceKPAdelicTraceProduct K) =
      ∫ y in sourceKPAdelicFundamentalDomain K,
        sourceKPTraceJacquetCharacter K m y * sourceKPAdelicCompactEisenstein K hζ s
          (sourceKPAdelicUpperLift K hζ y *
            (sourceKPAdelicProjectiveRationalLift K hζ (sourceKPProjectiveDiagonalHom K a) * g))
        ∂sourceKPAdelicTraceProduct K := by
  rw [sourceKPAdelicCompactEisenstein_traceJacquet K hζ hs (m * a),
    sourceKPAdelicCompactEisenstein_traceJacquet K hζ hs m,
    sourceKPAdelicTraceJacquetKernel_integral_rational_diagonal]

theorem sourceKPAdelicCompactEisenstein_traceJacquet_rational_diagonal
    {s : ℂ} (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1)
    (m : Kˣ) (g : SourceKPAdelicProjective K hζ) :
    (∫ y in sourceKPAdelicFundamentalDomain K,
      sourceKPTraceJacquetCharacter K m y *
        sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicUpperLift K hζ y * g)
      ∂sourceKPAdelicTraceProduct K) =
      ∫ y in sourceKPAdelicFundamentalDomain K,
        sourceKPTraceJacquetCharacter K 1 y * sourceKPAdelicCompactEisenstein K hζ s
          (sourceKPAdelicUpperLift K hζ y *
            (sourceKPAdelicProjectiveRationalLift K hζ (sourceKPProjectiveDiagonalHom K m) * g))
        ∂sourceKPAdelicTraceProduct K := by
  simpa only [one_mul] using
    sourceKPAdelicCompactEisenstein_traceJacquet_rational_diagonal_frequency K hζ hs 1 m g

end
end ArtinMatthews

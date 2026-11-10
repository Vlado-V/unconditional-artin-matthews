module

public import ArtinMatthews.SourceKPCuspRationalHeight
public import ArtinMatthews.SourceKPAdelicEisensteinHolomorphic
public import ArtinMatthews.SourceKPTraceJacquetCharacter
public import ArtinMatthews.SourceKPAutomorphicCompactEisenstein
public import ArtinMatthews.SourceKPTraceJacquetRational
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

/-! Unit-frequency reduction on positive archimedean heights keeps the
literal finite rational translate and removes only the proved compact
phase factor. -/
namespace ArtinMatthews
open NumberField MeasureTheory
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance sourceKPJacquetHeightMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance sourceKPJacquetHeightBorel : BorelSpace 𝔸[K] := ⟨rfl⟩

theorem sourceKPTraceJacquetFundamental_right_deep (s : ℂ) (m : Kˣ)
    (g : SourceKPAdelicProjective K hζ) (k : sourceKPAdelicDeepCompact K hζ) :
    (∫ z in sourceKPAdelicFundamentalDomain K,
      sourceKPTraceJacquetCharacter K m z *
        sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicUpperLift K hζ z * (g * k.val))
      ∂sourceKPAdelicTraceProduct K) =
      ∫ z in sourceKPAdelicFundamentalDomain K,
        sourceKPTraceJacquetCharacter K m z *
          sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicUpperLift K hζ z * g)
        ∂sourceKPAdelicTraceProduct K := by
  apply integral_congr_ae
  filter_upwards [] with z
  rw [← mul_assoc, sourceKPAdelicCompactEisenstein_right_deep K hζ s _ k]

theorem sourceKPAdelicCompactEisenstein_traceJacquet_positive_height
    {s : ℂ} (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1)
    (m : Kˣ) (y : InfinitePlace K → ℝ) (hy : ∀ v, 0 < y v)
    (qf : SourceKPFiniteAdeleProjective K hζ) :
    (∫ z in sourceKPAdelicFundamentalDomain K,
      sourceKPTraceJacquetCharacter K m z * sourceKPAdelicCompactEisenstein K hζ s
        (sourceKPAdelicUpperLift K hζ z * (sourceKPCuspHeightSection K hζ y hy,qf))
      ∂sourceKPAdelicTraceProduct K) =
      ∫ z in sourceKPAdelicFundamentalDomain K,
        sourceKPTraceJacquetCharacter K 1 z * sourceKPAdelicCompactEisenstein K hζ s
          (sourceKPAdelicUpperLift K hζ z *
            (sourceKPCuspHeightSection K hζ (sourceKPCuspRationalHeight K hζ m y)
                (sourceKPCuspRationalHeight_pos K hζ m y hy),
              (sourceKPAdelicProjectiveRationalLift K hζ (sourceKPProjectiveDiagonalHom K m)).2 * qf))
        ∂sourceKPAdelicTraceProduct K := by
  rw [sourceKPAdelicCompactEisenstein_traceJacquet_rational_diagonal K hζ hs m
    (sourceKPCuspHeightSection K hζ y hy,qf)]
  rw [sourceKPCuspRationalHeight_factor K hζ m y hy qf]
  exact sourceKPTraceJacquetFundamental_right_deep K hζ s 1 _ _

end
end ArtinMatthews

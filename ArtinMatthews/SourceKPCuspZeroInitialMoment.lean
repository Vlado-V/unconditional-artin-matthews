module

public import ArtinMatthews.SourceKPCuspPowerMoment
public import ArtinMatthews.SourceKPCuspNativeFourierTest
public import ArtinMatthews.SourceKPCuspFourierFactor
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

namespace ArtinMatthews
open NumberField Module.Free MeasureTheory StandardAdelic SourceHyperbolicGreen
open scoped NumberField AdeleRing MatrixGroups Topology NNReal ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (d : 𝓞 K) (hd : d ≠ 0) (qf : SourceKPFiniteAdeleProjective K hζ)
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "V" => InfinitePlace K
local notation "E" => sourceKPCuspProductCoordinates K hζ d hd
variable (hperiod : ∀ t ∈ sourceKPCuspFiniteIdeal K d,
  ∃ k : sourceKPFiniteDeepMatrixGroup K,
    (1,qf)⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t) * (1,qf) =
      sourceKPFiniteDeepCoverLift K hζ k)

include hperiod in
theorem sourceKPCuspNativeZeroTest_initial
    (c : ℝ≥0) (hc : 0 < c)
    (hmap : Measure.map (E).symm (productVolume V) =
      (c:ℝ≥0∞) • (volume : Measure (I → ℝ)).prod (sourceKPCuspProductHeightMeasure K))
    (B : Set (V → ℝ)) (hB : IsCompact B) (hpos : ∀ y ∈ B, ∀ v, 0 < y v)
    {T : ℝ} (hT : 1 ≤ T) {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1):ℕ):ℝ) ≤ 2*s.re+1) :
    sourceKPCuspNativeFourierTest K hζ d hd qf B hB hpos (0:K) hT s =
      (c:ℂ) * (sourceKPCuspPowerMoment K B s * sourceKPAdelicCompactScalar K hζ s (1,qf) +
        sourceKPCuspPowerMoment K B (-s) * sourceKPAdelicTraceIntertwiner K hζ s (1,qf)) := by
  have hspos : 0 < s.re := by
    have hn : 0 ≤ (Module.finrank ℚ K : ℝ) := Nat.cast_nonneg _
    push_cast at hs
    linarith
  rw [sourceKPCuspNativeFourierTest_initial_band K hζ d hd qf B hB hpos (0:K) hT hs,
    sourceKPCuspNativeBand_integral K hζ d hd c hc hmap B hB.measurableSet _
      (sourceKPCuspNativeFourierTest_band_integrable K hζ d hd qf B hB hpos (0:K) hT hs)]
  congr 1
  calc
    _ = ∫ y in B, sourceKPCuspArchPower K s y * sourceKPAdelicCompactScalar K hζ s (1,qf) +
        sourceKPCuspArchPower K (-s) y * sourceKPAdelicTraceIntertwiner K hζ s (1,qf)
        ∂sourceKPCuspProductHeightMeasure K := by
      apply setIntegral_congr_fun hB.measurableSet
      intro y hy
      simp only [sourceKPCuspNativeFrequency_coordinates, map_zero, zero_mul,
        AddChar.map_zero_eq_one, star_one, one_mul]
      rw [sourceKPCuspNativeEisenstein_mean K hζ d hd qf hperiod hs y (hpos y hy),
        sourceKPCuspHeightSection_scalar, sourceKPCuspHeightSection_intertwiner K hζ hspos]
    _ = _ := by
      rw [integral_add
        ((sourceKPCuspArchPower_integrableOn K hζ d hd s B hB hpos).mul_const _)
        ((sourceKPCuspArchPower_integrableOn K hζ d hd (-s) B hB hpos).mul_const _),
        integral_mul_const, integral_mul_const]
      rfl

end
end ArtinMatthews

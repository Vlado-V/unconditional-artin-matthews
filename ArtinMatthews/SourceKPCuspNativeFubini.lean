module

public import ArtinMatthews.SourceKPCuspNativeIntegral
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
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.ENatToNat
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

/-! Integrability transports through the actual principal-cell chart before
applying Fubini, with its fixed Haar normalization. -/
namespace ArtinMatthews
open NumberField Module.Free MeasureTheory SourceHyperbolicGreen
open scoped NumberField AdeleRing ENNReal NNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (d : 𝓞 K) (hd : d ≠ 0)
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "V" => InfinitePlace K
local notation "E" => sourceKPCuspProductCoordinates K hζ d hd

theorem sourceKPCuspNativeBand_integrable_product
    (c : ℝ≥0) (hc : 0 < c)
    (hm : Measure.map (E).symm (productVolume V) =
      (c:ℝ≥0∞) • (volume : Measure (I → ℝ)).prod (sourceKPCuspProductHeightMeasure K))
    (B : Set (InfinitePlace K → ℝ)) (hB : MeasurableSet B)
    (f : ProductSpace V → ℂ)
    (hf : IntegrableOn f (sourceKPCuspNativeBand K hζ d hd B) (productVolume V)) :
    Integrable (fun p : (I → ℝ) × (V → ℝ) => f (E p))
      ((unitTorusUnitCellMeasure I).prod ((sourceKPCuspProductHeightMeasure K).restrict B)) := by
  let μ := (productVolume V).restrict (sourceKPCuspNativeBand K hζ d hd B)
  let e := (E).symm.toHomeomorph.toMeasurableEquiv
  let F : (I → ℝ) × (V → ℝ) → ℂ := fun p => f (E p)
  have he (p : ProductSpace V) : F (e p) = f p := congrArg f ((E).apply_symm_apply p)
  have hi : Integrable F (Measure.map e μ) := by
    apply (integrable_map_equiv e F).mpr
    exact hf.congr (Filter.Eventually.of_forall fun p => (he p).symm)
  have hmap : Measure.map e μ = (c:ℝ≥0∞) •
      (unitTorusUnitCellMeasure I).prod ((sourceKPCuspProductHeightMeasure K).restrict B) :=
    sourceKPCuspProductCoordinates_map_restrict_unitCell K hζ d hd c hm B hB
  rw [hmap] at hi
  exact (integrable_smul_measure (by exact_mod_cast hc.ne') ENNReal.coe_ne_top).mp hi

end
end ArtinMatthews

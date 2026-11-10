module

public import ArtinMatthews.SourceKPCuspResidualFourierValue
public import ArtinMatthews.SourceKPCuspNativeTraceSlice
public import ArtinMatthews.SourceKPCuspResidualDualCell
public import ArtinMatthews.SourceKPCuspTraceModeDictionary
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

/-! The actual analytic residual profile on a denominator-valid cell also
holds on every cell where the same character is trace-dual. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain Module.Free MeasureTheory SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing nonZeroDivisors NNReal ENNReal

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "V" => InfinitePlace K
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "D[" d "]" => FractionalIdeal.dual ℤ ℚ
  ((Ideal.span ({d} : Set (𝓞 K)) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)

theorem sourceKPCuspResidualFourierCell_ae_eq_value_of_dual
    (d : 𝓞 K) (hd : d ≠ 0) (qf : Gf)
    (hpd : sourceKPCuspNativeFinitePeriod K hζ d qf) (m : Kˣ) (hmd : (m : K) ∈ D[d])
    (B : Set (V → ℝ)) (hB : IsCompact B) (hpos : ∀ y ∈ B, ∀ v, 0 < y v)
    {T : ℝ} (hT : 1 ≤ T) :
    sourceKPCuspResidualFourierCell K hζ d hd qf (m:K) hT =ᵐ[
        (sourceKPCuspProductHeightMeasure K).restrict B]
      fun y => sourceKPCuspResidualFourierValue K hζ m hT qf *
        sourceKPTraceJacquetArchProfile K hζ m (1/6) y := by
  let g : SourceKPAdelicProjective K hζ := (1,qf)
  obtain ⟨e,he,hm,hp⟩ := sourceKPAdelicCuspFrequencyPeriod K hζ (m:K) g
  have hpe : sourceKPCuspNativeFinitePeriod K hζ e qf := hp
  have hme : (m:K) ∈ D[e] := (sourceKPCuspTraceDualFrequency_period_iff K e he (m:K)).mp
    (fun _ hz => sourceKPCuspPrincipalFrequency_period K e (m:K) hm hz)
  obtain ⟨c,hc,hmap⟩ := sourceKPCuspProductCoordinates_map_productVolume K hζ e he
  have hprofile := sourceKPCuspResidualFourierCell_ae_eq_general K hζ e he qf m hpe hm
    c hc hmap B hB hpos hT
  have hvalue := sourceKPCuspResidualFourierValue_eq_coefficient K hζ m hT qf e he c hc hpe hm hmap
  filter_upwards [hprofile, ae_restrict_mem hB.measurableSet] with y hy hyB
  calc
    _ = sourceKPCuspResidualFourierCell K hζ e he qf (m:K) hT y :=
      sourceKPCuspResidualFourierCell_period_independent_of_dual K hζ d e hd he qf
        hpd hpe (m:K) hmd hme hT y (hpos y hyB)
    _ = sourceKPCuspResidualCoefficient K hζ e he qf m c hT *
        sourceKPTraceJacquetArchProfile K hζ m (1/6) y := hy
    _ = _ := by rw [← hvalue]

end
end ArtinMatthews

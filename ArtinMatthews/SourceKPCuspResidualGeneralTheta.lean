module

public import ArtinMatthews.SourceKPArchJacquetProfile
public import ArtinMatthews.SourceKPCuspRationalHeight
public import ArtinMatthews.SourceKPCuspResidualFourierIntegral
public import ArtinMatthews.SourceKPArchJacquetFrequencyScale
public import ArtinMatthews.SourceKPCuspResidualGeneralFourier
public import ArtinMatthews.SourceKPCuspResidualThetaProfile
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

/-! The actual nonzero-frequency residue has the literal source Bessel
profile with the embedded-frequency scaling kept explicit. -/
namespace ArtinMatthews
open NumberField MeasureTheory SourceArchJacquet SourceReflection
open scoped NumberField AdeleRing MatrixGroups Topology BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPCuspFrequencyThetaScale (m : Kˣ) : ℂ :=
  (∏ v : InfinitePlace K,
    (‖(sourceKPCuspRationalComplexUnit K hζ m v : ℂ)‖:ℂ) ^ (2*(1/6:ℂ)-1)) /
      ∏ v : InfinitePlace K, (‖(sourceKPCuspRationalComplexUnit K hζ m v : ℂ)‖:ℂ)

theorem sourceKPTraceJacquetArchProfile_theta (m : Kˣ)
    (y : InfinitePlace K → ℝ) (hy : ∀ v, 0 < y v) :
    (∏ v : InfinitePlace K, (y v:ℂ)) * sourceKPTraceJacquetArchProfile K hζ m (1/6) y =
      sourceKPCuspFrequencyThetaScale K hζ m *
        (sourceArchJacquetConstant:ℂ)^Fintype.card (InfinitePlace K) *
        ∏ v : InfinitePlace K,
          sourceThetaBesselProfile (4*Real.pi) ((sourceKPCuspRationalHeight K hζ m y v)^2) := by
  classical
  let Y := sourceKPCuspRationalHeight K hζ m y
  let Q : ℂ := ∏ v : InfinitePlace K, (‖(sourceKPCuspRationalComplexUnit K hζ m v : ℂ)‖:ℂ)
  let H : ℂ := ∏ v : InfinitePlace K, (y v:ℂ)
  let P : ℂ := ∏ v : InfinitePlace K,
    (‖(sourceKPCuspRationalComplexUnit K hζ m v : ℂ)‖:ℂ) ^ (2*(1/6:ℂ)-1)
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun v _ =>
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (sourceKPCuspRationalComplexUnit K hζ m v).ne_zero))
  have hY : (∏ v : InfinitePlace K, (Y v:ℂ)) = Q*H := by
    dsimp only [Y,sourceKPCuspRationalHeight,Q,H]
    simp only [Complex.ofReal_mul,Finset.prod_mul_distrib]
  have htheta := sourceKPTraceJacquetArchProfile_unit_theta K hζ Y
    (sourceKPCuspRationalHeight_pos K hζ m y hy)
  rw [hY] at htheta
  have hscale := sourceKPTraceJacquetArchProfile_frequency_scale K hζ m (1/6) y hy
  change H * sourceKPTraceJacquetArchProfile K hζ m (1/6) y =
    (P/Q) * (sourceArchJacquetConstant:ℂ)^Fintype.card (InfinitePlace K) *
      ∏ v : InfinitePlace K, sourceThetaBesselProfile (4*Real.pi) ((Y v)^2)
  calc
    _ = H*(P*sourceKPTraceJacquetArchProfile K hζ 1 (1/6) Y) := by rw [hscale]
    _ = (P/Q)*((Q*H)*sourceKPTraceJacquetArchProfile K hζ 1 (1/6) Y) := by
      field_simp [hQ]
      <;> ring
    _ = _ := by rw [← htheta]; ring

theorem sourceKPCuspResidualTheta_has_general_profile
    (qf : SourceKPFiniteAdeleProjective K hζ) (m : Kˣ) {T : ℝ} (hT : 1 ≤ T) :
    ∃ (d : 𝓞 K) (hd : d ≠ 0) (a : ℂ),
      ∀ (B : Set (InfinitePlace K → ℝ)) (hB : IsCompact B)
        (hpos : ∀ y ∈ B, ∀ v, 0 < y v),
        (fun y => (∏ v : InfinitePlace K, (y v:ℂ)) *
          sourceKPCuspResidualFourierCell K hζ d hd qf (m:K) hT y) =ᵐ[(sourceKPCuspProductHeightMeasure K).restrict B]
        fun y => a * (sourceArchJacquetConstant:ℂ)^Fintype.card (InfinitePlace K) *
          ∏ v : InfinitePlace K,
            sourceThetaBesselProfile (4*Real.pi) ((sourceKPCuspRationalHeight K hζ m y v)^2) := by
  classical
  obtain ⟨d,hd,a,ha⟩ := sourceKPCuspResidualFourierCell_has_profile K hζ qf m hT
  refine ⟨d,hd,a*sourceKPCuspFrequencyThetaScale K hζ m,?_⟩
  intro B hB hpos
  filter_upwards [ha B hB hpos,ae_restrict_mem hB.measurableSet] with y hy hmem
  rw [hy]
  have h := sourceKPTraceJacquetArchProfile_theta K hζ m y (hpos y hmem)
  calc
    _ = a*((∏ v : InfinitePlace K, (y v:ℂ))*sourceKPTraceJacquetArchProfile K hζ m (1/6) y) := by ring
    _ = _ := by rw [h]; ring

end
end ArtinMatthews

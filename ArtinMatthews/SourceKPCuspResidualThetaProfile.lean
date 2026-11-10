module

public import ArtinMatthews.SourceKPArchJacquetProfile
public import ArtinMatthews.SourceKPCuspResidualFourierIntegral
public import ArtinMatthews.SourceArchUnitFrequencyProfile
public import ArtinMatthews.SourceKPCuspResidualFourierCoefficient
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

/-! The actual residue's normalized Fourier profile is the literal source
Bessel tensor after the required square-norm substitution and radial weight. -/
namespace ArtinMatthews
open NumberField Module.Free MeasureTheory SourceArchJacquet SourceReflection
open scoped NumberField AdeleRing MatrixGroups Topology BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPTraceJacquetArchProfile_unit_theta
    (y : InfinitePlace K → ℝ) (hy : ∀ v, 0 < y v) :
    (sourceArchJacquetConstant:ℂ)^Fintype.card (InfinitePlace K) *
        (∏ v : InfinitePlace K, sourceThetaBesselProfile (4*Real.pi) ((y v)^2)) =
      (∏ v : InfinitePlace K, (y v:ℂ)) * sourceKPTraceJacquetArchProfile K hζ 1 (1/6) y := by
  classical
  have hf : sourceKPTraceJacquetProfileFrequency K hζ (1:Kˣ) = fun _ => -1 := by
    funext v
    simp only [sourceKPTraceJacquetProfileFrequency,Units.val_one,map_one]
  have hl (v : InfinitePlace K) :
      (sourceArchJacquetConstant:ℂ)*sourceThetaBesselProfile (4*Real.pi) ((y v)^2) =
        (y v:ℂ)*sourceArchWeightedDiagonalProfile sourceArchTraceCharacter (1/6) (-1) (y v) := by
    rw [sourceArchWeightedDiagonal_unit_whittaker (hy v)]
    let u : ℂˣ := Units.mk0 (y v:ℂ) (Complex.ofReal_ne_zero.mpr (hy v).ne')
    have hn : ‖(u:ℂ)‖ = y v := by
      change ‖(y v:ℂ)‖ = y v
      rw [Complex.norm_real,Real.norm_of_nonneg (hy v).le]
    have h := sourceArchSphericalWhittaker_sourceProfile u
    rw [hn,Real.sqrt_sq (hy v).le] at h
    exact h
  have hp := Finset.prod_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun v _ => hl v)
  simpa only [sourceKPTraceJacquetArchProfile,hf,sourceArchWeightedProduct,
    Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ] using hp

theorem sourceKPCuspResidualTheta_has_profile
    (qf : SourceKPFiniteAdeleProjective K hζ) {T : ℝ} (hT : 1 ≤ T) :
    ∃ (d : 𝓞 K) (hd : d ≠ 0) (a : ℂ),
      ∀ (B : Set (InfinitePlace K → ℝ)) (hB : IsCompact B)
        (hpos : ∀ y ∈ B, ∀ v, 0 < y v),
        (fun y => (∏ v : InfinitePlace K, (y v:ℂ)) *
          sourceKPCuspResidualFourierCell K hζ d hd qf (1:K) hT y) =ᵐ[(sourceKPCuspProductHeightMeasure K).restrict B]
        fun y => a * (sourceArchJacquetConstant:ℂ)^Fintype.card (InfinitePlace K) *
          ∏ v : InfinitePlace K, sourceThetaBesselProfile (4*Real.pi) ((y v)^2) := by
  classical
  obtain ⟨d,hd,a,ha⟩ := sourceKPCuspResidualFourierCell_has_unit_profile K hζ qf hT
  refine ⟨d,hd,a,?_⟩
  intro B hB hpos
  filter_upwards [ha B hB hpos,ae_restrict_mem hB.measurableSet] with y hy hmem
  rw [hy]
  have h := sourceKPTraceJacquetArchProfile_unit_theta K hζ y (hpos y hmem)
  calc
    _ = a*((∏ v : InfinitePlace K, (y v:ℂ))*sourceKPTraceJacquetArchProfile K hζ 1 (1/6) y) := by ring
    _ = _ := by rw [← h]; ring

end
end ArtinMatthews

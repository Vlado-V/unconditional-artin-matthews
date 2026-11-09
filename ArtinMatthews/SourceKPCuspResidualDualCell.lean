module

public import ArtinMatthews.SourceKPCuspTraceDualFrequency
public import ArtinMatthews.SourceKPCuspResidualFourierIntegral
public import ArtinMatthews.SourceKPCuspLevelTopology
public import ArtinMatthews.SourceKPCuspNativeTraceSlice


set_option backward.privateInPublic true
@[expose] public section

/-! The actual residual cell coefficient at a trace-dual frequency is the
literal normalized adelic trace integral, independently of the valid period. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain Module.Free MeasureTheory StandardAdelic
open scoped NumberField MatrixGroups AdeleRing nonZeroDivisors

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "V" => InfinitePlace K
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "D[" d "]" => FractionalIdeal.dual ℤ ℚ
  ((Ideal.span ({d} : Set (𝓞 K)) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
local notation "Q[" d "]" => SourceKPCuspPrincipalQuotient K d

local instance sourceResidualDualCellAdelicMeasurable : MeasurableSpace 𝔸[K] := borel _
local instance sourceResidualDualCellAdelicBorel : BorelSpace 𝔸[K] := ⟨rfl⟩
local instance sourceResidualDualCellQuotientMeasurable (d : 𝓞 K) :
    MeasurableSpace Q[d] := borel _
local instance sourceResidualDualCellQuotientBorel (d : 𝓞 K) : BorelSpace Q[d] := ⟨rfl⟩

theorem sourceKPCuspResidualFourierCell_eq_traceIntegral_of_dual
    (d : 𝓞 K) (hd : d ≠ 0) (qf : Gf)
    (hperiod : sourceKPCuspNativeFinitePeriod K hζ d qf) (m : K) (hm : m ∈ D[d])
    {T : ℝ} (hT : 1 ≤ T) (y : V → ℝ) (hy : ∀ v, 0 < y v) :
    sourceKPCuspResidualFourierCell K hζ d hd qf m hT y =
      ∫ a in sourceKPAdelicFundamentalDomain K, star (character K (algebraMap K 𝔸[K] m * a)) *
        (sourceKPAutomorphicExceptionalResidue K hζ hT).val
          (sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ
            (sourceKPAdelicUpperLift K hζ a * (sourceKPCuspHeightSection K hζ y hy,qf))))
        ∂sourceKPAdelicTraceProduct K := by
  let g : SourceKPAdelicProjective K hζ := (sourceKPCuspHeightSection K hζ y hy,qf)
  have hg := sourceKPCuspFinitePeriod_arch_change K hζ d qf hperiod
    (sourceKPCuspHeightSection K hζ y hy)
  let R := (sourceKPAutomorphicExceptionalResidue K hζ hT).val
  let F : Q[d] → ℂ := fun z => R
    (sourceKPAutomorphicCompactMk K hζ (sourceKPCuspLevelCover K hζ d g hg z))
  have hF : Measurable F := (Lp.stronglyMeasurable R).measurable.comp
    ((sourceKPAutomorphicCompactMk_measurable K hζ).comp
      (sourceKPCuspLevelCover_continuous K hζ d g hg hd).measurable)
  have hcell := sourceKPCuspTraceDualFrequency_integral_unitCell K hζ d hd m hm F hF
  have hpoint (x : I → ℝ) :
      R (sourceKPCompactCoordinateProjection K hζ (QuotientGroup.mk qf)
        (sourceKPCuspProductCoordinates K hζ d hd (x,y))) =
        F (QuotientAddGroup.mk (sourceKPCuspUnitCellAdelicPoint K d hd x)) :=
    congrArg R (sourceKPCuspNativeUpperPoint_compact K hζ d hd x y hy qf)
  calc
    _ = ∫ x : I → ℝ, star (character K (algebraMap K 𝔸[K] m *
          sourceKPCuspUnitCellAdelicPoint K d hd x)) *
        F (QuotientAddGroup.mk (sourceKPCuspUnitCellAdelicPoint K d hd x))
          ∂unitTorusUnitCellMeasure I := by
      unfold sourceKPCuspResidualFourierCell
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => congrArg (fun z =>
        star (character K (algebraMap K 𝔸[K] m * sourceKPCuspUnitCellAdelicPoint K d hd x)) * z)
        (hpoint x)
    _ = _ := hcell.symm

theorem sourceKPCuspResidualFourierCell_period_independent_of_dual
    (d e : 𝓞 K) (hd : d ≠ 0) (he : e ≠ 0) (qf : Gf)
    (hpd : sourceKPCuspNativeFinitePeriod K hζ d qf)
    (hpe : sourceKPCuspNativeFinitePeriod K hζ e qf)
    (m : K) (hmd : m ∈ D[d]) (hme : m ∈ D[e])
    {T : ℝ} (hT : 1 ≤ T) (y : V → ℝ) (hy : ∀ v, 0 < y v) :
    sourceKPCuspResidualFourierCell K hζ d hd qf m hT y =
      sourceKPCuspResidualFourierCell K hζ e he qf m hT y :=
  (sourceKPCuspResidualFourierCell_eq_traceIntegral_of_dual K hζ d hd qf hpd m hmd hT y hy).trans
    (sourceKPCuspResidualFourierCell_eq_traceIntegral_of_dual K hζ e he qf hpe m hme hT y hy).symm

end
end ArtinMatthews

module

public import ArtinMatthews.SourceKPCuspResidualDualCell
public import ArtinMatthews.SourceKPCuspTraceModeDictionary
public import ArtinMatthews.SourceKPCuspResidualFourierValue


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

module

public import ArtinMatthews.SourceEisensteinArchDiagonalGrowth
public import ArtinMatthews.SourceEisensteinNonconstant
public import ArtinMatthews.SourceKPAdelicUpperTopology


set_option backward.privateInPublic true
@[expose] public section

/-! The actual zero-mean remainder has uniform growth along all expanding archimedean diagonals. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance sourceArchNonconstantAdelicMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance sourceArchNonconstantAdelicBorel : BorelSpace 𝔸[K] := ⟨rfl⟩

theorem sourceKPAdelicNonconstantEisenstein_archDiagonal_growth {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1)
    (S : Set (GL (Fin 2) 𝔸[K])) (hS : IsCompact S) :
    ∃ C : ℝ, 0 < C ∧ ∀ g ∈ S, ∀ a : (InfiniteAdeleRing K)ˣ,
      (∀ v, 1 ≤ ‖(a : InfiniteAdeleRing K) v‖) → ∀ q : SourceKPAdelicProjective K hζ,
      sourceKPAdelicProjectiveProjection K hζ q =
          ProjGenLinGroup.mk (g * sourceKPDiagonalHom 𝔸[K] (sourceArchOnlyIdele K a)) →
      ‖sourceKPAdelicNonconstantEisenstein K hζ s q‖ ≤ C * ‖(a : InfiniteAdeleRing K)‖ ^ (s.re + 1 / 2) := by
  let A := (fun p : 𝔸[K] × GL (Fin 2) 𝔸[K] => sourceKPUpperMatrix 𝔸[K] p.1 * p.2) ''
    (CompactQuotient.Construction.adelicCompactRepresentatives K ×ˢ S)
  have hA : IsCompact A :=
    ((CompactQuotient.Construction.isCompact_adelicCompactRepresentatives K).prod hS).image
      (((sourceKPAdelicUpperMatrix_continuous K).comp continuous_fst).mul continuous_snd)
  obtain ⟨C, hC, hbound⟩ := sourceKPAdelicCompactEisenstein_archDiagonal_growth K hζ hs
    (S ∪ A) (hS.union hA)
  refine ⟨2 * C, by positivity, ?_⟩
  intro g hg a ha q hq
  have hE := hbound g (Or.inl hg) a ha q hq
  let μ := sourceKPAdelicTraceProduct K
  let D := sourceKPAdelicFundamentalDomain K
  have hD : μ D = 1 := sourceKPAdelicTraceProduct_fundamentalDomain_of_primitiveRoot K hζ
  let : IsProbabilityMeasure (μ.restrict D) := ⟨by rw [Measure.restrict_apply_univ, hD]⟩
  have hEN : ∀ᵐ y ∂μ.restrict D,
      ‖sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicUpperLift K hζ y * q)‖ ≤
        C * ‖(a : InfiniteAdeleRing K)‖ ^ (s.re + 1 / 2) := by
    filter_upwards [ae_restrict_mem (sourceKPAdelicFundamentalDomain_measurable K)] with y hy
    have hgy : sourceKPUpperMatrix 𝔸[K] y * g ∈ A :=
      ⟨(y, g), ⟨sourceKPAdelicFundamentalDomain_subset_compact K hy, hg⟩, rfl⟩
    apply hbound _ (Or.inr hgy) a ha (sourceKPAdelicUpperLift K hζ y * q)
    rw [map_mul, sourceKPAdelicUpperLift_projection, hq, ← map_mul, mul_assoc]
  have hmean : ‖∫ y in D,
      sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicUpperLift K hζ y * q) ∂μ‖ ≤
        C * ‖(a : InfiniteAdeleRing K)‖ ^ (s.re + 1 / 2) := by
    simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using
      norm_integral_le_of_norm_le_const hEN
  rw [sourceKPAdelicNonconstantEisenstein,
    ← sourceKPAdelicCompactEisenstein_traceConstantTerm K hζ hs q]
  exact (norm_sub_le _ _).trans (by linarith)

end
end ArtinMatthews

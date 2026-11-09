module

public import ArtinMatthews.SourceAdelicSL2Haar
public import ArtinMatthews.SourceAdelicRowBody


set_option backward.privateInPublic true
@[expose] public section

/-! A nonzero rational row with integral finite coordinates and a uniform
archimedean bound after multiplication by an actual determinant-one adele matrix. -/
namespace ArtinMatthews
open NumberField MeasureTheory Set
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField AdeleRing MatrixGroups Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
local instance sourceAdelicShortRow_measurableSpace : MeasurableSpace 𝔸[F] := borel 𝔸[F]
local instance sourceAdelicShortRow_borelSpace : BorelSpace 𝔸[F] := ⟨rfl⟩

def sourceRationalAdelicRow (g : SL(2, 𝔸[F])) (q : F × F) : 𝔸[F] × 𝔸[F] :=
  (algebraMap F 𝔸[F] q.1 * g 0 0 + algebraMap F 𝔸[F] q.2 * g 1 0,
    algebraMap F 𝔸[F] q.1 * g 0 1 + algebraMap F 𝔸[F] q.2 * g 1 1)

theorem sourceSL2Adelic_uniform_short_row :
    ∃ R : ℝ, 0 < R ∧ ∀ g : SL(2, 𝔸[F]), ∃ q : F × F, q ≠ 0 ∧
      (sourceRationalAdelicRow F g q).1.2 ∈ IntegralAdeles.Construction.finiteIntegralRing F ∧
      (sourceRationalAdelicRow F g q).2.2 ∈ IntegralAdeles.Construction.finiteIntegralRing F ∧
      ∀ v : InfinitePlace F, ‖(sourceRationalAdelicRow F g q).1.1 v‖ ≤ R ∧
        ‖(sourceRationalAdelicRow F g q).2.1 v‖ ≤ R := by
  obtain ⟨R, hR, hbound⟩ := sourceKPAdelicBlichfeldtBody_diff_arch_bound F
  refine ⟨R, hR, fun g => ?_⟩
  let T := sourceSL2AdelicRowAction F g
  have hT : MeasurePreserving T (sourceKPAdelicRowHaar F) (sourceKPAdelicRowHaar F) :=
    sourceSL2Adelic_row_measurePreserving F g
  have hmeas : MeasurableSet (T ⁻¹' sourceKPAdelicBlichfeldtBody F) :=
    (sourceKPAdelicBlichfeldtBody_measurable F).preimage hT.measurable
  have hvol : 1 < sourceKPAdelicRowHaar F (T ⁻¹' sourceKPAdelicBlichfeldtBody F) := by
    rw [hT.measure_preimage (sourceKPAdelicBlichfeldtBody_measurable F).nullMeasurableSet,
      sourceKPAdelicBlichfeldtBody_mass]
    norm_num
  obtain ⟨q, hq, x, hx, y, hy, hxy⟩ := sourceKPAdelicRow_blichfeldt F
    (T ⁻¹' sourceKPAdelicBlichfeldtBody F) hmeas.nullMeasurableSet hvol
  have hrow : sourceRationalAdelicRow F g q = T y - T x := by
    calc
      _ = T (algebraMap F 𝔸[F] q.1, algebraMap F 𝔸[F] q.2) :=
        (sourceSL2AdelicRowAction_rational F g q).symm
      _ = _ := by
        rw [hxy]
        exact sourceSL2AdelicRowAction_sub F g y x
  have hfin := sourceKPAdelicBlichfeldtBody_diff_integral F (x := T x) (y := T y) hx hy
  have harch := hbound (T x) hx (T y) hy
  refine ⟨q, hq, ?_, ?_, ?_⟩
  · simpa only [hrow, Prod.fst_sub] using hfin.1
  · simpa only [hrow, Prod.snd_sub] using hfin.2
  · intro v
    simpa only [hrow, Prod.fst_sub, Prod.snd_sub] using harch v

end
end ArtinMatthews

module

public import ArtinMatthews.SourceKPHighCuspMeasure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable


set_option backward.privateInPublic true
@[expose] public section

/-! The full representative measure is archimedean Haar times counting
measure on the actual finite-level fibers. -/
namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory Set
open scoped NumberField MatrixGroups AdeleRing ENNReal

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCuspRationalProjective_countable : Countable (PGL(2,K)) := by
  let : Countable (Matrix (Fin 2) (Fin 2) K) :=
    inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  let : Countable (GL (Fin 2) K) := Units.val_injective.countable
  exact ProjGenLinGroup.mk_surjective.countable

instance sourceKPCuspFiniteLevelFiber_countable : Countable (SourceKPFiniteLevelFiber K hζ) := by
  let : Countable (PGL(2,K)) := sourceKPCuspRationalProjective_countable K
  let f : SourceKPFiniteOrbit K hζ × PGL(2,K) → SourceKPFiniteLevelFiber K hζ :=
    fun p => p.2 • sourceKPFiniteOrbitRepresentative K hζ p.1
  apply Function.Surjective.countable (f := f)
  intro b
  have he := sourceKPFiniteOrbitRepresentative_spec K hζ (sourceKPFiniteOrbitMk K hζ b)
  obtain ⟨γ,hγ⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact he.symm)
  exact ⟨(sourceKPFiniteOrbitMk K hζ b, γ),hγ⟩

instance sourceKPCuspFiniteFiber_measurableSpace :
    MeasurableSpace (SourceKPFiniteLevelFiber K hζ) := borel _

instance sourceKPCuspFiniteFiber_borelSpace :
    BorelSpace (SourceKPFiniteLevelFiber K hζ) := ⟨rfl⟩

def sourceKPFiniteRepresentativeHaar : Measure (SourceKPFiniteLevelSpace K hζ) :=
  (sourceKPArchHaar K hζ).prod Measure.count

instance sourceKPFiniteRepresentativeHaar_sigmaFinite :
    SigmaFinite (sourceKPFiniteRepresentativeHaar K hζ) := by
  unfold sourceKPFiniteRepresentativeHaar
  infer_instance

theorem sourceKPFiniteRepresentativeHaar_apply
    (U : Set (SourceKPFiniteLevelSpace K hζ)) (hU : MeasurableSet U) :
    sourceKPFiniteRepresentativeHaar K hζ U =
      ∑' b : SourceKPFiniteLevelFiber K hζ,
        sourceKPArchHaar K hζ {a | (a,b) ∈ U} := by
  rw [sourceKPFiniteRepresentativeHaar, Measure.prod_apply_symm hU, lintegral_count]
  rfl

def sourceKPFiniteRepresentativeLeft (g : SourceKPAdelicProjective K hζ) :
    SourceKPFiniteLevelSpace K hζ ≃ₜ SourceKPFiniteLevelSpace K hζ where
  toEquiv := MulAction.toPerm g
  continuous_toFun := sourceKPFiniteLevel_left_continuous K hζ g
  continuous_invFun := sourceKPFiniteLevel_left_continuous K hζ g⁻¹

theorem sourceKPFiniteRepresentativeHaar_left (g : SourceKPAdelicProjective K hζ) :
    MeasurePreserving (sourceKPFiniteRepresentativeLeft K hζ g)
      (sourceKPFiniteRepresentativeHaar K hζ) (sourceKPFiniteRepresentativeHaar K hζ) := by
  let e : Equiv.Perm (SourceKPFiniteLevelFiber K hζ) := MulAction.toPerm g.2
  have hem : Measurable (e : SourceKPFiniteLevelFiber K hζ → SourceKPFiniteLevelFiber K hζ) :=
    continuous_of_discreteTopology.measurable
  have he : MeasurePreserving e Measure.count Measure.count := by
    refine ⟨hem, ?_⟩
    ext U hU
    rw [Measure.map_apply hem hU, Measure.count_apply (hU.preimage hem), Measure.count_apply hU]
    rw [← e.injective.encard_image, Set.image_preimage_eq _ e.surjective]
  exact (sourceKPArchHaar_left_preserving K hζ g.1).prod he

theorem sourceKPHighRepresentative_isOpen (T : ℝ) :
    IsOpen {x : SourceKPFiniteLevelSpace K hζ | T < sourceKPFiniteLevelHeight K hζ x} :=
  isOpen_lt continuous_const (sourceKPFiniteLevelHeight_continuous K hζ)

def sourceKPHighRepresentativeHaar (T : ℝ) : Measure (SourceKPHighCuspFinite K hζ T) :=
  Measure.comap Subtype.val (sourceKPFiniteRepresentativeHaar K hζ)

theorem sourceKPHighRepresentativeHaar_apply (T : ℝ)
    (U : Set (SourceKPHighCuspFinite K hζ T)) :
    sourceKPHighRepresentativeHaar K hζ T U =
      sourceKPFiniteRepresentativeHaar K hζ (Subtype.val '' U) :=
  (MeasurableEmbedding.subtype_coe
    (sourceKPHighRepresentative_isOpen K hζ T).measurableSet).comap_apply _ U

theorem sourceKPHighRepresentativeHaar_subtype (T : ℝ) :
    MeasurePreserving (Subtype.val : SourceKPHighCuspFinite K hζ T → SourceKPFiniteLevelSpace K hζ)
      (sourceKPHighRepresentativeHaar K hζ T)
      ((sourceKPFiniteRepresentativeHaar K hζ).restrict
        {x | T < sourceKPFiniteLevelHeight K hζ x}) :=
  measurePreserving_subtype_coe (sourceKPHighRepresentative_isOpen K hζ T).measurableSet

instance sourceKPHighRepresentativeHaar_sigmaFinite (T : ℝ) :
    SigmaFinite (sourceKPHighRepresentativeHaar K hζ T) := by
  have h := sourceKPHighRepresentativeHaar_subtype K hζ T
  apply SigmaFinite.of_map _ h.measurable.aemeasurable
  rw [h.map_eq]
  infer_instance

private theorem sourceKPCuspMeasurePreserving_subtype
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → X}
    (hm : MeasurePreserving f μ μ) (he : MeasurableEmbedding f)
    {S : Set X} (hS : MeasurableSet S) (hpre : f ⁻¹' S = S)
    (F : S → S) (hF : ∀ x, (F x).val = f x.val) :
    MeasurePreserving F (Measure.comap Subtype.val μ) (Measure.comap Subtype.val μ) := by
  let v : S → X := Subtype.val
  let ρ := Measure.comap v μ
  have hv : MeasurePreserving v ρ (μ.restrict S) := measurePreserving_subtype_coe hS
  have hcomp : v ∘ F = f ∘ v := funext hF
  have hfS : Measurable F := by
    apply (MeasurableEmbedding.subtype_coe hS).measurable_comp_iff.mp
    change Measurable (v ∘ F)
    rw [hcomp]
    exact hm.measurable.comp hv.measurable
  have hr := hm.restrict_preimage_emb he S
  rw [hpre] at hr
  refine ⟨hfS, ?_⟩
  apply (MeasurableEmbedding.subtype_coe hS).map_injective
  change Measure.map v (Measure.map F ρ) = Measure.map v ρ
  calc
    _ = Measure.map (v ∘ F) ρ := Measure.map_map hv.measurable hfS
    _ = Measure.map (f ∘ v) ρ := congrArg (fun u => Measure.map u ρ) hcomp
    _ = Measure.map f (Measure.map v ρ) := (Measure.map_map hm.measurable hv.measurable).symm
    _ = _ := by rw [hv.map_eq, hr.map_eq]

theorem sourceKPHighRepresentativeHaar_left (T : ℝ)
    (g : SourceKPAdelicProjective K hζ)
    (h : ∀ x : SourceKPFiniteLevelSpace K hζ,
      sourceKPFiniteLevelHeight K hζ (g • x) = sourceKPFiniteLevelHeight K hζ x)
    (F : SourceKPHighCuspFinite K hζ T → SourceKPHighCuspFinite K hζ T)
    (hF : ∀ x, (F x).val = g • x.val) :
    MeasurePreserving F (sourceKPHighRepresentativeHaar K hζ T)
      (sourceKPHighRepresentativeHaar K hζ T) := by
  let f := sourceKPFiniteRepresentativeLeft K hζ g
  let S : Set (SourceKPFiniteLevelSpace K hζ) := {x | T < sourceKPFiniteLevelHeight K hζ x}
  have hpre : f ⁻¹' S = S := by
    ext x
    change T < sourceKPFiniteLevelHeight K hζ (g • x) ↔ T < sourceKPFiniteLevelHeight K hζ x
    rw [h]
  exact sourceKPCuspMeasurePreserving_subtype (sourceKPFiniteRepresentativeHaar_left K hζ g)
    f.measurableEmbedding (sourceKPHighRepresentative_isOpen K hζ T).measurableSet hpre F hF

end
end ArtinMatthews

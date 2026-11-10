module

public import ArtinMatthews.SourceKPTranslateCompactTrace
public import ArtinMatthews.SourceKPTranslateCompactHaar
public import ArtinMatthews.SourceKPArithmeticDiscreteness
public import ArtinMatthews.SourceKPCompactRationalTransport
public import ArtinMatthews.SourceKPTranslateBaseHaar
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Haar integration of the finite coset trace on the actual compact quotient. -/
namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory Set
open scoped NumberField MatrixGroups AdeleRing BigOperators ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (T : Finset (SourceKPFiniteAdeleProjective K hζ))
include T

local notation "A" => PGL(2, InfiniteAdeleRing K)
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "D" => sourceKPFiniteLevelConjugate K hζ
local notation "J" => sourceKPFiniteTranslateLevel K hζ T
local notation "F" => SourceKPFiniteLevelFiber K hζ
local notation "FJ" => SourceKPTranslateFiniteLevelFiber K hζ T
local notation "X" => SourceKPFiniteLevelSpace K hζ
local notation "XJ" => SourceKPTranslateRepresentativeSpace K hζ T
local notation "YJ" => SourceKPTranslateAutomorphicCompactLevel K hζ T
local notation "μA" => sourceKPArchHaar K hζ
local notation "ν" => sourceKPFiniteRepresentativeHaar K hζ
local notation "νJ" => sourceKPTranslateRepresentativeHaar K hζ T
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "μJ" => sourceKPTranslateCompactHaar K hζ T
local notation "E" => sourceKPTranslateBaseDomain K hζ
local notation "q" => sourceKPFiniteLevelToCompact K hζ
local notation "qJ" => sourceKPTranslateRepresentativeToCompact K hζ T

local notation "C[" t "]" => (D t) ⧸ Subgroup.subgroupOf (J) (D t)
local notation "Et[" t ", " ht "]" => sourceKPTranslateRepresentativeDomain K hζ T t ht
local notation "L[" t ", " ht ", " b "]" =>
  {c : FJ // sourceKPFiniteRightTranslateMap K hζ T t ht c = b}

local instance fiberQuotientFinite (t : Gf) : Finite C[t] := by
  letI : ((J).subgroupOf (D t)).FiniteIndex := Subgroup.isFiniteRelIndex_iff_finiteIndex.mp
    (sourceKPFiniteTranslateLevel_finiteRelIndex_conjugate K hζ T t)
  infer_instance

local instance fiberQuotientMeasurableSpace (t : Gf) : MeasurableSpace C[t] := ⊤

local instance fiberQuotientMeasurableSingleton (t : Gf) : MeasurableSingletonClass C[t] :=
  ⟨fun _ => trivial⟩

private def fiberProdMeasurableEquiv (t : Gf) (ht : J ≤ D t) : FJ ≃ᵐ F × C[t] where
  toEquiv := sourceKPFiniteRightTranslateProductEquiv K hζ T t ht
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

private theorem fiberProdMeasurableEquiv_count (t : Gf) (ht : J ≤ D t) :
    MeasurePreserving (fiberProdMeasurableEquiv K hζ T t ht)
      (Measure.count : Measure FJ) ((Measure.count : Measure F).prod (Measure.count : Measure C[t])) := by
  let e := fiberProdMeasurableEquiv K hζ T t ht
  refine ⟨e.measurable,?_⟩
  apply Measure.ext_of_singleton
  rintro ⟨b,c⟩
  have hp : e ⁻¹' {(b,c)} = {e.symm (b,c)} := by
    ext x
    change e x = (b,c) ↔ x = e.symm (b,c)
    exact e.toEquiv.apply_eq_iff_eq_symm_apply
  rw [Measure.map_apply e.measurable (measurableSet_singleton _), hp,
    Measure.count_singleton, ← singleton_prod_singleton, Measure.prod_prod,
    Measure.count_singleton, Measure.count_singleton, one_mul]

private def repProdMeasurableEquiv (t : Gf) (ht : J ≤ D t) : XJ ≃ᵐ X × C[t] :=
  ((MeasurableEquiv.refl A).prodCongr (fiberProdMeasurableEquiv K hζ T t ht)).trans
    MeasurableEquiv.prodAssoc.symm

private theorem repProdMeasurableEquiv_haar (t : Gf) (ht : J ≤ D t) :
    MeasurePreserving (repProdMeasurableEquiv K hζ T t ht) νJ
      ((ν).prod (Measure.count : Measure C[t])) := by
  exact (MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μA (Measure.count : Measure F) (Measure.count : Measure C[t]))).comp
      ((MeasurePreserving.id μA).prod (fiberProdMeasurableEquiv_count K hζ T t ht))

theorem sourceKPTranslateRepresentative_integral_trace (t : Gf) (ht : J ≤ D t) {M : Type*}
    [NormedAddCommGroup M] [NormedSpace ℝ M] [CompleteSpace M]
    (f : XJ → M) (hf : IntegrableOn f Et[t, ht] νJ) :
    (∫ x in Et[t, ht], f x ∂νJ) = ∫ x in E, ∑ c : L[t, ht, x.2], f (x.1,c.val) ∂ν := by
  letI : Fintype C[t] := Fintype.ofFinite C[t]
  let e := repProdMeasurableEquiv K hζ T t ht
  have hpres := (repProdMeasurableEquiv_haar K hζ T t ht).restrict_preimage_emb
    e.measurableEmbedding (E ×ˢ (Set.univ : Set C[t]))
  have hpre : e ⁻¹' (E ×ˢ (Set.univ : Set C[t])) = Et[t, ht] := by
    ext x
    change (sourceKPTranslateRepresentativeMap K hζ T t ht x ∈ E ∧ (e x).2 ∈ Set.univ) ↔
      sourceKPTranslateRepresentativeMap K hζ T t ht x ∈ E
    simp
  rw [hpre, ← Measure.restrict_prod_eq_prod_univ] at hpres
  let g : X × C[t] → M := f ∘ e.symm
  have hg : g ∘ e = f := by
    funext x
    simp [g,Function.comp_apply]
  have hint : Integrable g (((ν).restrict E).prod (Measure.count : Measure C[t])) :=
    (hpres.integrable_comp_emb e.measurableEmbedding).mp (hg.symm ▸ hf)
  calc
    (∫ x in Et[t, ht], f x ∂νJ) = ∫ x, g x ∂(((ν).restrict E).prod (Measure.count : Measure C[t])) := by
      change (∫ x in Et[t, ht], f x ∂νJ) = _
      rw [← hg]
      exact hpres.integral_comp' g
    _ = ∫ x in E, ∫ c, g (x,c) ∂(Measure.count : Measure C[t]) ∂ν := integral_prod g hint
    _ = _ := by
      apply integral_congr_ae
      apply ae_of_all
      intro x
      change (∫ c, g (x,c) ∂(Measure.count : Measure C[t])) =
        ∑ c : L[t, ht, x.2], f (x.1,c.val)
      rw [integral_count]
      exact Fintype.sum_equiv (sourceKPFiniteRightTranslateFiberEquiv K hζ T t ht x.2).symm
        _ _ (fun _ => rfl)

theorem sourceKPTranslateCompactTrace_integral (t : Gf) (ht : J ≤ D t) {M : Type*}
    [NormedAddCommGroup M] [NormedSpace ℝ M] [CompleteSpace M] [SecondCountableTopology M]
    (v : YJ → M) (hv : Continuous v) (hvi : Integrable v μJ) :
    (∫ y, sourceKPTranslateCompactTrace K hζ T t ht v y ∂μY) = ∫ x, v x ∂μJ := by
  have hbase := sourceKPTranslateBaseHaar_map K hζ
  have hJ := sourceKPTranslateCompactHaar_eq_of_domain K hζ T Et[t, ht]
    (sourceKPTranslateRepresentativeDomain_isFundamental K hζ T t ht)
  have hq := sourceKPFiniteLevelToCompact_measurable K hζ
  have hqJ := sourceKPTranslateRepresentativeToCompact_measurable K hζ T
  have htr := sourceKPTranslateCompactTrace_continuous K hζ T t ht v hv
  have hintegrable : IntegrableOn (v ∘ qJ) Et[t, ht] νJ :=
    (⟨hqJ,hJ.symm⟩ : MeasurePreserving qJ ((νJ).restrict Et[t, ht]) μJ).integrable_comp_of_integrable hvi
  rw [← hbase, hJ, integral_map hq.aemeasurable htr.aestronglyMeasurable,
    integral_map hqJ.aemeasurable hv.aestronglyMeasurable]
  change (∫ x in E, sourceKPTranslateCompactTrace K hζ T t ht v (q x) ∂ν) =
    ∫ x in Et[t, ht], (v ∘ qJ) x ∂νJ
  rw [sourceKPTranslateRepresentative_integral_trace K hζ T t ht (v ∘ qJ) hintegrable]
  apply integral_congr_ae
  apply ae_of_all
  rintro ⟨a,b⟩
  have he : q (a,b) = sourceKPUpperToCompact K hζ b
      (sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk a)) :=
    (sourceKPUpperToCompact_mk K hζ b a).symm
  change sourceKPTranslateCompactTrace K hζ T t ht v (q (a,b)) =
    ∑ c : L[t, ht, b], v (qJ (a,c.val))
  rw [he, sourceKPTranslateCompactTrace_upper] <;> rfl

end
end ArtinMatthews

module

public import ArtinMatthews.SourceKPFiniteUnipotentCompact
public import Mathlib.GroupTheory.OrderOfElement


set_option backward.privateInPublic true
@[expose] public section

/-! An actual scalar integral period inside each finite unipotent level. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain Topology Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K]

def sourceKPIntegralFinitePeriodScalar (U : AddSubgroup 𝔸ᶠ[K]) : 𝓞 K :=
  ((U.comap (sourceKPIntegralFiniteRing K).subtype.toAddMonoidHom).index : 𝓞 K)

lemma sourceKPIntegralFinitePeriodScalar_ne_zero
    (U : AddSubgroup 𝔸ᶠ[K]) (hU : IsOpen (U : Set 𝔸ᶠ[K])) :
    sourceKPIntegralFinitePeriodScalar K U ≠ 0 := by
  let A := sourceKPIntegralFiniteRing K
  let V : AddSubgroup A := U.comap A.subtype.toAddMonoidHom
  let : CompactSpace A := isCompact_iff_compactSpace.mp (sourceKPIntegralFiniteRing_isCompact K)
  have hV : IsOpen (V : Set A) := hU.preimage continuous_subtype_val
  let : Finite (A ⧸ V) := V.quotient_finite_of_isOpen hV
  change (V.index : 𝓞 K) ≠ 0
  exact_mod_cast (V.index_ne_zero_of_finite)

lemma sourceKPIntegralFinitePeriodScalar_mem (U : AddSubgroup 𝔸ᶠ[K])
    (x : sourceKPIntegralFiniteRing K) :
    algebraMap (𝓞 K) 𝔸ᶠ[K] (sourceKPIntegralFinitePeriodScalar K U) * (x : 𝔸ᶠ[K]) ∈ U := by
  let A := sourceKPIntegralFiniteRing K
  let V : AddSubgroup A := U.comap A.subtype.toAddMonoidHom
  have hx : A.subtype (V.index • x) ∈ U := V.nsmul_index_mem x
  rw [map_nsmul] at hx
  change V.index • (x : 𝔸ᶠ[K]) ∈ U at hx
  simpa only [sourceKPIntegralFinitePeriodScalar, map_natCast, nsmul_eq_mul] using hx

lemma sourceKPIntegralFinite_open_contains_multiple
    (U : AddSubgroup 𝔸ᶠ[K]) (hU : IsOpen (U : Set 𝔸ᶠ[K])) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ x : sourceKPIntegralFiniteRing K,
      algebraMap (𝓞 K) 𝔸ᶠ[K] d * (x : 𝔸ᶠ[K]) ∈ U :=
  ⟨sourceKPIntegralFinitePeriodScalar K U, sourceKPIntegralFinitePeriodScalar_ne_zero K U hU,
    sourceKPIntegralFinitePeriodScalar_mem K U⟩

lemma sourceKPFiniteConjugateMatrix_add (a : GL (Fin 2) 𝔸ᶠ[K]) (x y : 𝔸ᶠ[K]) :
    sourceKPFiniteConjugateMatrix K a (x + y) =
      sourceKPFiniteConjugateMatrix K a x * sourceKPFiniteConjugateMatrix K a y := by
  unfold sourceKPFiniteConjugateMatrix
  rw [sourceKPUpperMatrix_add]
  group

def sourceKPFiniteMatrixCuspParameters (a : GL (Fin 2) 𝔸ᶠ[K]) : AddSubgroup 𝔸ᶠ[K] where
  carrier := {t | sourceKPFiniteConjugateMatrix K a t ∈ sourceKPFiniteDeepMatrixGroup K}
  zero_mem' := by
    change sourceKPFiniteConjugateMatrix K a 0 ∈ sourceKPFiniteDeepMatrixGroup K
    rw [sourceKPFiniteConjugateMatrix_zero]
    exact (sourceKPFiniteDeepMatrixGroup K).one_mem
  add_mem' := by
    intro x y hx hy
    change sourceKPFiniteConjugateMatrix K a (x+y) ∈ sourceKPFiniteDeepMatrixGroup K
    rw [sourceKPFiniteConjugateMatrix_add]
    exact (sourceKPFiniteDeepMatrixGroup K).mul_mem hx hy
  neg_mem' := by
    intro x hx
    have he : sourceKPFiniteConjugateMatrix K a (-x) = (sourceKPFiniteConjugateMatrix K a x)⁻¹ := by
      apply eq_inv_iff_mul_eq_one.mpr
      rw [← sourceKPFiniteConjugateMatrix_add, neg_add_cancel, sourceKPFiniteConjugateMatrix_zero]
    change sourceKPFiniteConjugateMatrix K a (-x) ∈ sourceKPFiniteDeepMatrixGroup K
    rw [he]
    exact (sourceKPFiniteDeepMatrixGroup K).inv_mem hx

lemma sourceKPFiniteMatrixCuspParameters_isOpen (a : GL (Fin 2) 𝔸ᶠ[K]) :
    IsOpen (sourceKPFiniteMatrixCuspParameters K a : Set 𝔸ᶠ[K]) :=
  (sourceKPFiniteMatrixCuspParameters K a).isOpen_of_mem_nhds
    (sourceKPFiniteConjugateMatrix_eventually_deep K a)

lemma sourceKPFiniteMatrixCuspPeriod (a : GL (Fin 2) 𝔸ᶠ[K]) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ x : sourceKPIntegralFiniteRing K,
      sourceKPFiniteConjugateMatrix K a (algebraMap (𝓞 K) 𝔸ᶠ[K] d * (x : 𝔸ᶠ[K])) ∈
        sourceKPFiniteDeepMatrixGroup K :=
  sourceKPIntegralFinite_open_contains_multiple K (sourceKPFiniteMatrixCuspParameters K a)
    (sourceKPFiniteMatrixCuspParameters_isOpen K a)

def sourceKPFiniteAddEmbedding : 𝔸ᶠ[K] →+ 𝔸[K] where
  toFun t := (0,t)
  map_zero' := rfl
  map_add' _ _ := Prod.ext (zero_add 0).symm rfl

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

lemma sourceKPAdelicConjugateUpper_add (g : SourceKPAdelicProjective K hζ) (x y : 𝔸ᶠ[K]) :
    g⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K (x+y)) * g =
      (g⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K x) * g) *
        (g⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K y) * g) := by
  rw [map_add, sourceKPAdelicUpperLift_add]
  group

def sourceKPAdelicCuspParameters (g : SourceKPAdelicProjective K hζ) : AddSubgroup 𝔸ᶠ[K] where
  carrier := {t | g⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t) * g ∈ sourceKPAdelicDeepCompact K hζ}
  zero_mem' := by
    change g⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K 0) * g ∈ sourceKPAdelicDeepCompact K hζ
    rw [map_zero, sourceKPAdelicUpperLift_zero, mul_one, inv_mul_cancel]
    exact (sourceKPAdelicDeepCompact K hζ).one_mem
  add_mem' := by
    intro x y hx hy
    change g⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K (x+y)) * g ∈ sourceKPAdelicDeepCompact K hζ
    rw [sourceKPAdelicConjugateUpper_add]
    exact (sourceKPAdelicDeepCompact K hζ).mul_mem hx hy
  neg_mem' := by
    intro x hx
    have he : g⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K (-x)) * g =
        (g⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K x) * g)⁻¹ := by
      apply eq_inv_iff_mul_eq_one.mpr
      rw [← sourceKPAdelicConjugateUpper_add, neg_add_cancel, map_zero,
        sourceKPAdelicUpperLift_zero, mul_one, inv_mul_cancel]
    change g⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K (-x)) * g ∈ sourceKPAdelicDeepCompact K hζ
    rw [he]
    exact (sourceKPAdelicDeepCompact K hζ).inv_mem hx

lemma sourceKPAdelicCuspParameters_isOpen (g : SourceKPAdelicProjective K hζ) :
    IsOpen (sourceKPAdelicCuspParameters K hζ g : Set 𝔸ᶠ[K]) :=
  (sourceKPAdelicCuspParameters K hζ g).isOpen_of_mem_nhds
    (sourceKPAdelicFiniteConjugate_eventually_compact K hζ g)

lemma sourceKPAdelicCuspPeriod (g : SourceKPAdelicProjective K hζ) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ x : sourceKPIntegralFiniteRing K,
      g⁻¹ * sourceKPAdelicUpperLift K hζ
        (sourceKPFiniteAddEmbedding K (algebraMap (𝓞 K) 𝔸ᶠ[K] d * (x : 𝔸ᶠ[K]))) * g ∈ sourceKPAdelicDeepCompact K hζ :=
  sourceKPIntegralFinite_open_contains_multiple K (sourceKPAdelicCuspParameters K hζ g)
    (sourceKPAdelicCuspParameters_isOpen K hζ g)

end
end ArtinMatthews

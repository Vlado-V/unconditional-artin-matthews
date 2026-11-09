module

public import ArtinMatthews.SourceKPTranslateCoreGramEnergy
public import ArtinMatthews.SourceKPTranslateGramGenuine
public import ArtinMatthews.SourceKPCompactGenuineH1


set_option backward.privateInPublic true
@[expose] public section

/-! The finite Gram trace acts on the actual completed scalar and genuine forms. -/
namespace ArtinMatthews
open NumberField MeasureTheory ContinuousLinearMap
open scoped NumberField MatrixGroups AdeleRing InnerProductSpace Topology ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (T : Finset (SourceKPFiniteAdeleProjective K hζ))
include T

local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "D" => sourceKPFiniteLevelConjugate K hζ
local notation "J" => sourceKPFiniteTranslateLevel K hζ T
local notation "μA" => sourceKPArchHaar K hζ
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ μA
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "Q" => SourceKPCompactFormCore K hζ
local notation "V" => SourceKPCompactH1 K hζ
local notation "Vχ" => SourceKPCompactGenuineH1 K hζ
local notation "G" => sourceKPCompactGenuineL2Subspace K hζ μA
local notation "e" => sourceKPCompactH1Core K hζ
local notation "m" => sourceKPCompactFormCoreMassLinear K hζ
local notation "j" => sourceKPCompactH1Mass K hζ
local notation "jχ" => sourceKPCompactGenuineH1Mass K hζ
local notation "d[" t "]" => (Subgroup.relIndex (J) (D t) : ℝ)
local notation "A[" t ", " ht ", " u ", " hu "]" =>
  sourceKPTranslateScalarGramL2 K hζ T t ht u hu
local notation "Aχ[" t ", " ht ", " u ", " hu "]" =>
  sourceKPTranslateGenuineGramL2 K hζ T t ht u hu
local notation "C[" t ", " ht ", " u ", " hu "]" =>
  sourceKPTranslateCoreGram K hζ T t ht u hu

private def formCoreGramLinear (t : Gf) (ht : J ≤ D t) (u : Gf) (hu : J ≤ D u) : Q →ₗ[ℂ] Q :=
  let E := sourceKPCompactFormCoreLinearEquiv K hζ
  E.symm.toLinearMap.comp ((C[t, ht, u, hu]).comp E.toLinearMap)

def sourceKPTranslateFormCoreGram (t : Gf) (ht : J ≤ D t) (u : Gf) (hu : J ≤ D u) : Q →L[ℂ] Q := by
  let B := formCoreGramLinear K hζ T t ht u hu
  let A := A[t, ht, u, hu]
  let M := ‖A‖ ^ 2 + d[t] * d[u]
  have hd : 0 ≤ d[t] * d[u] := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hM : 0 ≤ M := add_nonneg (sq_nonneg _) hd
  refine B.mkContinuous (Real.sqrt M) (fun f => ?_)
  apply (sq_le_sq₀ (norm_nonneg (B f))
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg f))).mp
  rw [mul_pow, Real.sq_sqrt hM, sourceKPCompactFormCore_norm_sq, sourceKPCompactFormCore_norm_sq]
  have hm : m (B f) = A (m f) :=
    (sourceKPTranslateScalarGramL2_coreMass K hζ T t ht u hu f.val).symm
  rw [hm]
  have hmass : ‖A (m f)‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖m f‖ ^ 2 := by
    rw [← mul_pow]
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      (A.le_opNorm (m f))
  have henergy : (∫ y, sourceKPCompactCoreEnergy K hζ (B f).val y ∂μY) ≤
      d[t] * d[u] * ∫ y, sourceKPCompactCoreEnergy K hζ f.val y ∂μY :=
    sourceKPTranslateCoreGram_energy_bound K hζ T t ht u hu f.val
  have he : 0 ≤ ∫ y, sourceKPCompactCoreEnergy K hζ f.val y ∂μY :=
    integral_nonneg (sourceKPCompactCoreEnergy_nonneg K hζ f.val)
  rw [mul_add]
  exact add_le_add (hmass.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hd) (sq_nonneg _)))
    (henergy.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (sq_nonneg _)) he))

theorem sourceKPTranslateFormCoreGram_val (t : Gf) (ht : J ≤ D t)
    (u : Gf) (hu : J ≤ D u) (f : Q) :
    (sourceKPTranslateFormCoreGram K hζ T t ht u hu f).val = C[t, ht, u, hu] f.val := rfl

theorem sourceKPTranslateFormCoreGram_mass (t : Gf) (ht : J ≤ D t)
    (u : Gf) (hu : J ≤ D u) (f : Q) :
    m (sourceKPTranslateFormCoreGram K hζ T t ht u hu f) = A[t, ht, u, hu] (m f) :=
  (sourceKPTranslateScalarGramL2_coreMass K hζ T t ht u hu f.val).symm

theorem sourceKPTranslateFormCoreGram_inner (t : Gf) (ht : J ≤ D t)
    (u : Gf) (hu : J ≤ D u) (f g : Q) :
    inner ℂ f (sourceKPTranslateFormCoreGram K hζ T t ht u hu g) =
      inner ℂ (sourceKPTranslateFormCoreGram K hζ T u hu t ht f) g := by
  change sourceKPCompactFormCoreInner K hζ f (sourceKPTranslateFormCoreGram K hζ T t ht u hu g) =
    sourceKPCompactFormCoreInner K hζ (sourceKPTranslateFormCoreGram K hζ T u hu t ht f) g
  rw [sourceKPCompactFormCoreInner, sourceKPCompactFormCoreInner,
    sourceKPTranslateFormCoreGram_mass, sourceKPTranslateFormCoreGram_mass,
    sourceKPTranslateFormCoreGram_val, sourceKPTranslateFormCoreGram_val,
    sourceKPTranslateCoreGram_dirichlet, ← sourceKPTranslateScalarGramL2_adjoint K hζ T t ht u hu]
  exact congrArg (· + sourceKPCompactDirichletCore K hζ (C[u, hu, t, ht] f.val) g.val)
    ((A[t, ht, u, hu]).adjoint_inner_left (m g) (m f)).symm

def sourceKPTranslateScalarGramH1 (t : Gf) (ht : J ≤ D t) (u : Gf) (hu : J ≤ D u) :
    V →L[ℂ] V :=
  ((e).toContinuousLinearMap.comp (sourceKPTranslateFormCoreGram K hζ T t ht u hu)).fromCompletion

theorem sourceKPTranslateScalarGramH1_core (t : Gf) (ht : J ≤ D t)
    (u : Gf) (hu : J ≤ D u) (f : Q) :
    sourceKPTranslateScalarGramH1 K hζ T t ht u hu (e f) =
      e (sourceKPTranslateFormCoreGram K hζ T t ht u hu f) :=
  ((e).toContinuousLinearMap.comp (sourceKPTranslateFormCoreGram K hζ T t ht u hu)).fromCompletion_apply_coe f

theorem sourceKPTranslateScalarGramH1_mass (t : Gf) (ht : J ≤ D t)
    (u : Gf) (hu : J ≤ D u) (f : V) :
    j (sourceKPTranslateScalarGramH1 K hζ T t ht u hu f) = A[t, ht, u, hu] (j f) := by
  let B := sourceKPTranslateScalarGramH1 K hζ T t ht u hu
  let A := A[t, ht, u, hu]
  refine (sourceKPCompactH1Core_denseRange K hζ).induction_on
    (p := fun g : V => j (B g) = A (j g)) f
    (isClosed_eq ((j).continuous.comp B.continuous) (A.continuous.comp (j).continuous)) ?_
  intro g
  rw [sourceKPTranslateScalarGramH1_core, sourceKPCompactH1Mass_core, sourceKPCompactH1Mass_core]
  exact sourceKPTranslateFormCoreGram_mass K hζ T t ht u hu g

theorem sourceKPTranslateScalarGramH1_inner (t : Gf) (ht : J ≤ D t)
    (u : Gf) (hu : J ≤ D u) (f g : V) :
    inner ℂ f (sourceKPTranslateScalarGramH1 K hζ T t ht u hu g) =
      inner ℂ (sourceKPTranslateScalarGramH1 K hζ T u hu t ht f) g := by
  let B := sourceKPTranslateScalarGramH1 K hζ T t ht u hu
  let B' := sourceKPTranslateScalarGramH1 K hζ T u hu t ht
  have hclosed (g : V) : IsClosed {f : V | inner ℂ f (B g) = inner ℂ (B' f) g} :=
    isClosed_eq (continuous_id.inner continuous_const) (B'.continuous.inner continuous_const)
  refine (sourceKPCompactH1Core_denseRange K hζ).induction_on
    (p := fun f : V => inner ℂ f (B g) = inner ℂ (B' f) g) f (hclosed g) ?_
  intro f
  refine (sourceKPCompactH1Core_denseRange K hζ).induction_on
    (p := fun g : V => inner ℂ (e f) (B g) = inner ℂ (B' (e f)) g) g
    (isClosed_eq (continuous_const.inner B.continuous) (continuous_const.inner continuous_id)) ?_
  intro g
  rw [sourceKPTranslateScalarGramH1_core, sourceKPTranslateScalarGramH1_core,
    LinearIsometry.inner_map_map, LinearIsometry.inner_map_map]
  exact sourceKPTranslateFormCoreGram_inner K hζ T t ht u hu f g

def sourceKPTranslateGenuineGramH1 (t : Gf) (ht : J ≤ D t)
    (u : Gf) (hu : J ≤ D u) : Vχ →L[ℂ] Vχ :=
  ((sourceKPTranslateScalarGramH1 K hζ T t ht u hu).comp (sourceKPCompactGenuineH1 K hζ).subtypeL).codRestrict
    (sourceKPCompactGenuineH1 K hζ) (fun f => by
      change j (sourceKPTranslateScalarGramH1 K hζ T t ht u hu f.val) ∈ G
      rw [sourceKPTranslateScalarGramH1_mass]
      exact sourceKPTranslateScalarGramL2_mem_genuine K hζ T t ht u hu f.prop)

theorem sourceKPTranslateGenuineGramH1_val (t : Gf) (ht : J ≤ D t)
    (u : Gf) (hu : J ≤ D u) (f : Vχ) :
    (sourceKPTranslateGenuineGramH1 K hζ T t ht u hu f).val =
      sourceKPTranslateScalarGramH1 K hζ T t ht u hu f.val := rfl

theorem sourceKPTranslateGenuineGramH1_mass (t : Gf) (ht : J ≤ D t)
    (u : Gf) (hu : J ≤ D u) (f : Vχ) :
    jχ (sourceKPTranslateGenuineGramH1 K hζ T t ht u hu f) =
      Aχ[t, ht, u, hu] (jχ f) := by
  apply Subtype.ext
  rw [sourceKPTranslateGenuineGramL2_val]
  exact sourceKPTranslateScalarGramH1_mass K hζ T t ht u hu f.val

theorem sourceKPTranslateGenuineGramH1_adjoint (t : Gf) (ht : J ≤ D t)
    (u : Gf) (hu : J ≤ D u) :
    (sourceKPTranslateGenuineGramH1 K hζ T t ht u hu).adjoint =
      sourceKPTranslateGenuineGramH1 K hζ T u hu t ht := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  exact (sourceKPTranslateScalarGramH1_inner K hζ T t ht u hu f.val g.val).symm

end
end ArtinMatthews

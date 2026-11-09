module

public import ArtinMatthews.SourceKPTranslateCoreGramMass
public import ArtinMatthews.SourceKPCubicCoreMass


set_option backward.privateInPublic true
@[expose] public section

/-! The literal trace and its Haar adjoint retain the actual cubic character. -/
namespace ArtinMatthews
open NumberField MeasureTheory Filter
open scoped NumberField MatrixGroups AdeleRing InnerProductSpace ContDiff
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (T : Finset (SourceKPFiniteAdeleProjective K hζ))
include T

local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "D" => sourceKPFiniteLevelConjugate K hζ
local notation "J" => sourceKPFiniteTranslateLevel K hζ T
local notation "YJ" => SourceKPTranslateAutomorphicCompactLevel K hζ T
local notation "μA" => sourceKPArchHaar K hζ
local notation "LY" => SourceKPAutomorphicL2 K hζ μA
local notation "C2" => sourceKPCompactC2Core K hζ
local notation "G" => sourceKPCompactGenuineL2Subspace K hζ μA
local notation "H" => SourceKPGenuineAutomorphicL2 K hζ
local notation "m" => sourceKPCompactCoreMass K hζ 2
local notation "Z" => rootsOfUnity 3 K

theorem sourceKPTranslateCoreGram_center (t : Gf) (ht : J ≤ D t)
    (u : Gf) (hu : J ≤ D u) (z : Z) (f : C2) :
    sourceKPTranslateCoreGram K hζ T t ht u hu (sourceKPCubicCorePullback K hζ 2 z f) =
      sourceKPCubicCorePullback K hζ 2 z (sourceKPTranslateCoreGram K hζ T t ht u hu f) := by
  let π := sourceKPTranslateAutomorphicCompactMap K hζ T u hu
  let p := sourceKPCubicCorePullback K hζ 2 z
  have he : (p f).val ∘ π = fun x : YJ => (f.val ∘ π) (z⁻¹ • x) := by
    funext x
    change (p f).val (π x) = f.val (π (z⁻¹ • x))
    rw [sourceKPCubicCorePullback_apply]
    exact congrArg f.val (sourceKPTranslateAutomorphicCompactMap_center K hζ T u hu z⁻¹ x).symm
  apply Subtype.ext
  funext y
  rw [sourceKPCubicCorePullback_apply,sourceKPTranslateCoreGram_val,sourceKPTranslateCoreGram_val,
    sourceKPTranslateCompactTrace_center]
  exact congrFun (congrArg (sourceKPTranslateCompactTrace K hζ T t ht) he) y

theorem sourceKPTranslateScalarGramL2_center (t : Gf) (ht : J ≤ D t)
    (u : Gf) (hu : J ≤ D u) (z : Z) (f : LY) :
    sourceKPTranslateScalarGramL2 K hζ T t ht u hu
        (sourceKPCompactCubicL2Representation K hζ μA z f) =
      sourceKPCompactCubicL2Representation K hζ μA z
        (sourceKPTranslateScalarGramL2 K hζ T t ht u hu f) := by
  let A := sourceKPTranslateScalarGramL2 K hζ T t ht u hu
  let U := sourceKPCompactCubicL2Representation K hζ μA z
  let C := sourceKPTranslateCoreGram K hζ T t ht u hu
  let P := sourceKPCubicCorePullback K hζ 2 z
  refine (sourceKPCompactCoreMass_denseRange K hζ).induction_on
    (p := fun g : LY => A (U g) = U (A g)) f
    (isClosed_eq (A.continuous.comp U.continuous) (U.continuous.comp A.continuous)) ?_
  intro g
  calc
    A (U (m g)) = A (m (P g)) := congrArg A (sourceKPCubicCoreMass_pullback K hζ 2 z g).symm
    _ = m (C (P g)) := sourceKPTranslateScalarGramL2_coreMass K hζ T t ht u hu (P g)
    _ = m (P (C g)) := congrArg m (sourceKPTranslateCoreGram_center K hζ T t ht u hu z g)
    _ = U (m (C g)) := sourceKPCubicCoreMass_pullback K hζ 2 z (C g)
    _ = U (A (m g)) := congrArg U (sourceKPTranslateScalarGramL2_coreMass K hζ T t ht u hu g).symm

theorem sourceKPTranslateScalarGramL2_mem_genuine (t : Gf) (ht : J ≤ D t)
    (u : Gf) (hu : J ≤ D u) {f : LY} (hf : f ∈ G) :
    sourceKPTranslateScalarGramL2 K hζ T t ht u hu f ∈ G := by
  let A := sourceKPTranslateScalarGramL2 K hζ T t ht u hu
  have hχ := (sourceKPCompactGenuineL2Subspace_mem K hζ μA f).mp hf
  apply (sourceKPCompactGenuineL2Subspace_mem K hζ μA (A f)).mpr
  intro z
  rw [← sourceKPTranslateScalarGramL2_center K hζ T t ht u hu z f, hχ z, map_smul]

theorem sourceKPTranslateGenuineGramL2_val (t : Gf) (ht : J ≤ D t)
    (u : Gf) (hu : J ≤ D u) (g : H) :
    (sourceKPTranslateGenuineGramL2 K hζ T t ht u hu g).val =
      sourceKPTranslateScalarGramL2 K hζ T t ht u hu g.val := by
  let A := sourceKPTranslateScalarGramL2 K hζ T t ht u hu
  let B : H := ⟨A g.val,sourceKPTranslateScalarGramL2_mem_genuine K hζ T t ht u hu g.prop⟩
  have he : sourceKPTranslateGenuineGramL2 K hζ T t ht u hu g = B := by
    apply ext_inner_left ℂ
    intro f
    rw [← sourceKPTranslateGenuineGramL2_inner]
    exact sourceKPTranslateScalarGramL2_inner K hζ T t ht u hu f.val g.val
  exact congrArg Subtype.val he

end
end ArtinMatthews

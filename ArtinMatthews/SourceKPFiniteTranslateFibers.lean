module

public import ArtinMatthews.SourceKPFiniteTranslateIndex


set_option backward.privateInPublic true
@[expose] public section

/-! Actual right translation from the common finite level, with its exact finite fibers. -/
namespace ArtinMatthews
open NumberField Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "Kf" => sourceKPFiniteLevelSubgroup K hζ
local notation "F" => SourceKPFiniteLevelFiber K hζ
local notation "D" => sourceKPFiniteLevelConjugate K hζ

theorem sourceKPFiniteLevelConjugate_one : D (1 : Gf) = Kf := by
  ext x
  simp [sourceKPFiniteLevelConjugate]

theorem sourceKPFiniteTranslateLevel_le_conjugate_one (T : Finset Gf) :
    sourceKPFiniteTranslateLevel K hζ T ≤ D 1 := by
  rw [sourceKPFiniteLevelConjugate_one]
  exact sourceKPFiniteTranslateLevel_le K hζ T

def SourceKPTranslateFiniteLevelFiber (T : Finset Gf) : Type :=
  Gf ⧸ sourceKPFiniteTranslateLevel K hζ T

private def rightTranslateConjugateEquiv (t : Gf) : (Gf ⧸ D t) ≃ F := by
  change (Gf ⧸ D t) ≃ Gf ⧸ Kf
  refine Quotient.congr (Equiv.mulRight t) ?_
  intro b c
  simp only [QuotientGroup.leftRel_apply]
  change b⁻¹ * c ∈ D t ↔ (b * t)⁻¹ * (c * t) ∈ Kf
  rw [sourceKPFiniteLevelConjugate, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, _root_.mul_inv_rev]
  simp only [mul_assoc]

variable (T : Finset (SourceKPFiniteAdeleProjective K hζ))
include T

local notation "J" => sourceKPFiniteTranslateLevel K hζ T
local notation "FJ" => SourceKPTranslateFiniteLevelFiber K hζ T

instance sourceKPTranslateFiniteLevelFiber_mulAction : MulAction Gf FJ :=
  inferInstanceAs (MulAction Gf (Gf ⧸ J))

def sourceKPFiniteRightTranslateProductEquiv (t : Gf) (h : J ≤ D t) :
    FJ ≃ F × ((D t) ⧸ (J).subgroupOf (D t)) :=
  (Subgroup.quotientEquivProdOfLE h).trans
    (Equiv.prodCongr (rightTranslateConjugateEquiv K hζ t) (Equiv.refl _))

def sourceKPFiniteRightTranslateMap (t : Gf) (h : J ≤ D t) (x : FJ) : F :=
  (sourceKPFiniteRightTranslateProductEquiv K hζ T t h x).1

theorem sourceKPFiniteRightTranslateMap_mk (t : Gf) (h : J ≤ D t) (b : Gf) :
    sourceKPFiniteRightTranslateMap K hζ T t h (QuotientGroup.mk b) = (QuotientGroup.mk (b * t) : F) :=
  rfl

theorem sourceKPFiniteRightTranslateMap_smul (t : Gf) (h : J ≤ D t) (g : Gf) (x : FJ) :
    sourceKPFiniteRightTranslateMap K hζ T t h (g • x) =
      g • sourceKPFiniteRightTranslateMap K hζ T t h x := by
  induction x using Quotient.inductionOn with
  | _ b =>
    change sourceKPFiniteRightTranslateMap K hζ T t h (QuotientGroup.mk (g * b)) =
      g • sourceKPFiniteRightTranslateMap K hζ T t h (QuotientGroup.mk b)
    rw [sourceKPFiniteRightTranslateMap_mk, sourceKPFiniteRightTranslateMap_mk]
    change (QuotientGroup.mk ((g * b) * t) : F) = QuotientGroup.mk (g * (b * t))
    rw [mul_assoc]

theorem sourceKPFiniteRightTranslateMap_surjective (t : Gf) (h : J ≤ D t) :
    Function.Surjective (sourceKPFiniteRightTranslateMap K hζ T t h) := by
  intro b
  let e := sourceKPFiniteRightTranslateProductEquiv K hζ T t h
  exact ⟨e.symm (b, QuotientGroup.mk 1), congrArg Prod.fst (e.apply_symm_apply _)⟩

def sourceKPFiniteRightTranslateFiberEquiv (t : Gf) (h : J ≤ D t) (b : F) :
    {x : FJ // sourceKPFiniteRightTranslateMap K hζ T t h x = b} ≃
      (D t) ⧸ (J).subgroupOf (D t) := by
  let e := sourceKPFiniteRightTranslateProductEquiv K hζ T t h
  refine ⟨fun x => (e x.val).2,
    fun c => ⟨e.symm (b,c), congrArg Prod.fst (e.apply_symm_apply _)⟩, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    apply e.injective
    rw [Equiv.apply_symm_apply]
    exact Prod.ext x.prop.symm rfl
  · intro c
    change (e (e.symm (b,c))).2 = c
    rw [Equiv.apply_symm_apply]

theorem sourceKPFiniteRightTranslateFiber_card (t : Gf) (h : J ≤ D t) (b : F) :
    Nat.card {x : FJ // sourceKPFiniteRightTranslateMap K hζ T t h x = b} =
      (J).relIndex (D t) :=
  Nat.card_congr (sourceKPFiniteRightTranslateFiberEquiv K hζ T t h b)

theorem sourceKPFiniteRightTranslateFiber_finite (t : Gf) (h : J ≤ D t) (b : F) :
    Finite {x : FJ // sourceKPFiniteRightTranslateMap K hζ T t h x = b} := by
  let : ((J).subgroupOf (D t)).FiniteIndex :=
    Subgroup.isFiniteRelIndex_iff_finiteIndex.mp
      (sourceKPFiniteTranslateLevel_finiteRelIndex_conjugate K hζ T t)
  exact Finite.of_equiv _ (sourceKPFiniteRightTranslateFiberEquiv K hζ T t h b).symm

end
end ArtinMatthews

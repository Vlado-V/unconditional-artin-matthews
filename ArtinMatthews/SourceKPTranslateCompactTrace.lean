module

public import ArtinMatthews.SourceKPTranslateCompactCenter


set_option backward.privateInPublic true
@[expose] public section

/-! The finite trace uses the entire finite coset fiber of a representative. It
therefore retains the multiplicities at points with rational archimedean isotropy. -/
namespace ArtinMatthews
open NumberField Matrix Topology
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "D" => sourceKPFiniteLevelConjugate K hζ
local notation "F" => SourceKPFiniteLevelFiber K hζ
local notation "U" => SourceKPArchUpperHalfSpace K
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ

def sourceKPBaseUpperMap : U × F → Y :=
  fun x => sourceKPUpperToCompact K hζ x.2 x.1

theorem sourceKPBaseUpperMap_isOpenQuotientMap :
    IsOpenQuotientMap (sourceKPBaseUpperMap K hζ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y
    obtain ⟨b,p,h⟩ := sourceKPUpperToCompact_cover K hζ y
    exact ⟨(p,b),h⟩
  · apply continuous_prod_of_discrete_right.mpr
    exact sourceKPUpperToCompact_continuous K hζ
  · intro W hW
    have he : sourceKPBaseUpperMap K hζ '' W =
        ⋃ b : F, sourceKPUpperToCompact K hζ b '' ((fun p : U => (p,b)) ⁻¹' W) := by
      ext y
      constructor
      · rintro ⟨⟨p,b⟩,hp,rfl⟩
        exact Set.mem_iUnion.mpr ⟨b,p,hp,rfl⟩
      · intro hy
        obtain ⟨b,p,hp,rfl⟩ := Set.mem_iUnion.mp hy
        exact ⟨(p,b),hp,rfl⟩
    rw [he]
    exact isOpen_iUnion fun b => sourceKPUpperToCompact_isOpenMap K hζ b _
      (hW.preimage (continuous_id.prodMk continuous_const))

variable (T : Finset (SourceKPFiniteAdeleProjective K hζ))
include T

local notation "J" => sourceKPFiniteTranslateLevel K hζ T
local notation "FJ" => SourceKPTranslateFiniteLevelFiber K hζ T
local notation "YJ" => SourceKPTranslateAutomorphicCompactLevel K hζ T

instance sourceKPFiniteRightTranslateFiber_fintype (t : Gf) (ht : J ≤ D t) (b : F) :
    Fintype {c : FJ // sourceKPFiniteRightTranslateMap K hζ T t ht c = b} :=
  letI := sourceKPFiniteRightTranslateFiber_finite K hζ T t ht b
  Fintype.ofFinite _

local notation "q" => sourceKPTranslateUpperMk K hζ T
local notation "L[" t ", " ht ", " b "]" =>
  {c : FJ // sourceKPFiniteRightTranslateMap K hζ T t ht c = b}

def sourceKPFiniteRightTranslateFiberSmulEquiv (t : Gf) (ht : J ≤ D t) (g : Gf) (b : F) :
    L[t, ht, b] ≃ L[t, ht, (g • b)] :=
  (MulAction.toPerm g).subtypeEquiv (fun c => by
    change sourceKPFiniteRightTranslateMap K hζ T t ht c = b ↔
      sourceKPFiniteRightTranslateMap K hζ T t ht (g • c) = g • b
    rw [sourceKPFiniteRightTranslateMap_smul]
    exact ⟨congrArg (g • ·), fun h => (MulAction.toPerm g).injective h⟩)

private theorem trace_rational {M : Type*} [AddCommMonoid M]
    (t : Gf) (ht : J ≤ D t) (v : YJ → M)
    (p₁ p₂ : U) (b₁ b₂ : F)
    (he : sourceKPUpperToCompact K hζ b₁ p₁ = sourceKPUpperToCompact K hζ b₂ p₂) :
    (∑ c : L[t, ht, b₁], v (q (p₁,c.val))) = ∑ c : L[t, ht, b₂], v (q (p₂,c.val)) := by
  obtain ⟨γ,hb,hp⟩ := (sourceKPUpperToCompact_eq_iff_rational K hζ b₁ b₂ p₁ p₂).mp he
  change sourceKPRationalFiniteMap K hζ γ • b₂ = b₁ at hb
  subst b₁
  let e := sourceKPFiniteRightTranslateFiberSmulEquiv K hζ T t ht
    (sourceKPRationalFiniteMap K hζ γ) b₂
  symm
  apply Fintype.sum_equiv e
  intro c
  apply congrArg v
  symm
  apply Quotient.sound
  exact MulAction.mem_orbit_iff.mpr ⟨γ,Prod.ext hp rfl⟩

def sourceKPTranslateCompactTrace {M : Type*} [AddCommMonoid M]
    (t : Gf) (ht : J ≤ D t) (v : YJ → M) (y : Y) : M :=
  let x := Classical.choose ((sourceKPBaseUpperMap_isOpenQuotientMap K hζ).surjective y)
  letI : Fintype L[t, ht, x.2] := sourceKPFiniteRightTranslateFiber_fintype K hζ T t ht x.2
  ∑ c : L[t, ht, x.2], v (q (x.1,c.val))

theorem sourceKPTranslateCompactTrace_upper {M : Type*} [AddCommMonoid M]
    (t : Gf) (ht : J ≤ D t) (v : YJ → M) (b : F) (p : U) :
    sourceKPTranslateCompactTrace K hζ T t ht v (sourceKPUpperToCompact K hζ b p) =
      ∑ c : L[t, ht, b], v (q (p,c.val)) := by
  unfold sourceKPTranslateCompactTrace
  exact trace_rational K hζ T t ht v _ _ _ _
    (Classical.choose_spec ((sourceKPBaseUpperMap_isOpenQuotientMap K hζ).surjective
      (sourceKPUpperToCompact K hζ b p)))

theorem sourceKPTranslateCompactTrace_continuous {M : Type*} [AddCommMonoid M]
    [TopologicalSpace M] [ContinuousAdd M] (t : Gf) (ht : J ≤ D t) (v : YJ → M) (hv : Continuous v) :
    Continuous (sourceKPTranslateCompactTrace K hζ T t ht v) := by
  apply (sourceKPBaseUpperMap_isOpenQuotientMap K hζ).continuous_comp_iff.mp
  apply continuous_prod_of_discrete_right.mpr
  intro b
  change Continuous (fun p : U =>
    sourceKPTranslateCompactTrace K hζ T t ht v (sourceKPUpperToCompact K hζ b p))
  simp only [sourceKPTranslateCompactTrace_upper]
  exact continuous_finsetSum _ fun c _ => hv.comp
    ((sourceKPTranslateUpperMk_isOpenQuotientMap K hζ T).continuous.comp
      (continuous_id.prodMk continuous_const))

theorem sourceKPTranslateCompactTrace_center {M : Type*} [AddCommMonoid M]
    (t : Gf) (ht : J ≤ D t) (v : YJ → M) (z : rootsOfUnity 3 K) (y : Y) :
    sourceKPTranslateCompactTrace K hζ T t ht v (z • y) =
      sourceKPTranslateCompactTrace K hζ T t ht (fun x => v (z • x)) y := by
  obtain ⟨b,p,rfl⟩ := sourceKPUpperToCompact_cover K hζ y
  rw [sourceKPCubicCenter_upperToCompact, sourceKPTranslateCompactTrace_upper,
    sourceKPTranslateCompactTrace_upper]
  let e := sourceKPFiniteRightTranslateFiberSmulEquiv K hζ T t ht
    (sourceKPFiniteAdeleProjectiveCenter K hζ z) b
  symm
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

end
end ArtinMatthews

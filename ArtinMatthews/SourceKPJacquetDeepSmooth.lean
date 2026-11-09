module

public import ArtinMatthews.SourceKPJacquetDeepConjugates
public import ArtinMatthews.SourceKPLocalWildJacquetFactor
public import ArtinMatthews.SourceKPLocalCompactRestriction


set_option backward.privateInPublic true
@[expose] public section

/-! The actual deep level gives the per-vector smoothness of the
stable Jacquet map, including on algebraic sums of right translates. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic SourcePhysical
open scoped NumberField SourcePhysical Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

local notation "G" => SourceFiniteKP2Projective K hζ P
local notation "J" => sourceKPLocalCompactDeepCoverLevel K hζ P
local notation "B₀" => SourceFiniteKPProjectiveBorel K hζ P

section SmoothSubspace

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (SourceFiniteKPProjectiveBorel K hζ P) V)

local notation "I₀" => sourceAlgebraicInducedSpace B₀ ρ
local notation "R₀" => sourceAlgebraicInducedRepresentation B₀ ρ

/-- Fixation by a finite intersection of conjugates of the actual split deep level. -/
def SourceKPJacquetDeepFixed (f : I₀) : Prop :=
  ∃ F : Finset G, ∀ k : G, (∀ a ∈ F, a⁻¹ * k * a ∈ J) → ∀ g : G, f.val (g * k) = f.val g

theorem sourceKPJacquet_deepFixed_of_deep_right (f : I₀)
    (hf : ∀ k ∈ J, ∀ g : G, f.val (g * k) = f.val g) :
    SourceKPJacquetDeepFixed K hζ P ρ f := by
  refine ⟨{1}, fun k hk g => hf k ?_ g⟩
  simpa only [inv_one, one_mul, mul_one] using hk 1 (Finset.mem_singleton_self 1)

def sourceKPJacquetDeepFixedSubspace : Submodule ℂ I₀ where
  carrier := {f | SourceKPJacquetDeepFixed K hζ P ρ f}
  zero_mem' := ⟨∅, fun _ _ _ => rfl⟩
  add_mem' := by
    intro f₁ f₂
    rintro ⟨F₁, h₁⟩ ⟨F₂, h₂⟩
    refine ⟨F₁ ∪ F₂, fun k hk g => ?_⟩
    change f₁.val (g * k) + f₂.val (g * k) = f₁.val g + f₂.val g
    rw [h₁ k (fun a ha => hk a (Finset.mem_union_left F₂ ha)) g,
      h₂ k (fun a ha => hk a (Finset.mem_union_right F₁ ha)) g]
  smul_mem' := by
    intro c f
    rintro ⟨F, hF⟩
    refine ⟨F, fun k hk g => ?_⟩
    change c • f.val (g * k) = c • f.val g
    rw [hF k hk g]

theorem sourceKPLocalCompactFixedSpace_le_jacquetDeepFixed :
    sourceKPLocalCompactFixedSpace K hζ P ρ ≤ sourceKPJacquetDeepFixedSubspace K hζ P ρ := by
  intro f hf
  apply sourceKPJacquet_deepFixed_of_deep_right K hζ P ρ f
  rintro _ ⟨j, hj, rfl⟩ g
  exact hf g ⟨j, hj⟩

theorem sourceKPJacquetDeepFixedSubspace_invariant (a : G) (f : I₀)
    (hf : f ∈ sourceKPJacquetDeepFixedSubspace K hζ P ρ) :
    R₀ a f ∈ sourceKPJacquetDeepFixedSubspace K hζ P ρ := by
  obtain ⟨F, hF⟩ := hf
  refine ⟨F.image (a * ·), fun k hk g => ?_⟩
  have hkin : ∀ b ∈ F, b⁻¹ * (a⁻¹ * k * a) * b ∈ J := by
    intro b hb
    have h := hk (a * b) (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
    simpa only [mul_inv_rev, mul_assoc] using h
  change f.val ((g * k) * a) = f.val (g * a)
  have he : (g * k) * a = (g * a) * (a⁻¹ * k * a) := by group
  rw [he, hF _ hkin (g * a)]

theorem sourceKPJacquet_span_right_translates_le_deepFixed (S : Set I₀)
    (hS : S ⊆ sourceKPLocalCompactFixedSpace K hζ P ρ) :
    Submodule.span ℂ {f : I₀ | ∃ a : G, ∃ v ∈ S, f = R₀ a v} ≤
      sourceKPJacquetDeepFixedSubspace K hζ P ρ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, v, hv, rfl⟩
  exact sourceKPJacquetDeepFixedSubspace_invariant K hζ P ρ a v
    ((sourceKPLocalCompactFixedSpace_le_jacquetDeepFixed K hζ P ρ) (hS hv))

theorem sourceKPJacquet_rootSmooth_of_deepFixed (C : Submodule ℂ I₀)
    (hDeep : C ≤ sourceKPJacquetDeepFixedSubspace K hζ P ρ) :
    SourceKPJacquetRootSmooth K hζ P ρ C := by
  intro f
  obtain ⟨F, hF⟩ := hDeep f.property
  obtain ⟨M, hM⟩ := sourceKPJacquet_conjugate_roots_deep_ball K hζ P F
  exact ⟨M, fun t ht g => ⟨hF _ (fun a ha => (hM t ht a ha).1) g,
    hF _ (fun a ha => (hM t ht a ha).2) g⟩⟩

end SmoothSubspace

section ActualFactor

variable {A : Type*} [Finite A] (v : A → SourceKPAdelicTorusInducedSpace K hζ (-1 / 6 : ℂ))
local notation "L" => P.adicCompletion K
local notation "W" => sourceKPLocalCompactSeedOrbit K hζ P (-1 / 6 : ℂ) v
local notation "ρ" => sourceKPLocalCompactSeedOrbitRepresentation K hζ P (-1 / 6 : ℂ) v
local notation "I₀" => sourceAlgebraicInducedSpace B₀ ρ
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P

local instance sourceKPJacquetDeepSmoothValueAddCommGroup : AddCommGroup W := Submodule.addCommGroup _

theorem sourceKPLocalWildJacquet_whittaker_factors_of_deepFixed (C : Submodule ℂ I₀)
    (hC : ∀ (g : G) (f : I₀), f ∈ C → sourceAlgebraicInducedRepresentation B₀ ρ g f ∈ C)
    (hDeep : C ≤ sourceKPJacquetDeepFixedSubspace K hζ P ρ) (ℓ : C →ₗ[ℂ] ℂ)
    (hℓ : ∀ (x : L) (f : C),
      ℓ (sourceKPJacquetRight K hζ P ρ C hC (l₀ (sourceGL2Upper x)) f) =
        localFiniteCharacter K P x * ℓ f) :
    SourceKPJacquetFactors (X := C) (Y := W)
      (sourceKPLocalWildJacquetMap K hζ P v C (sourceKPJacquet_rootSmooth_of_deepFixed K hζ P ρ C hDeep)) ℓ :=
  sourceKPLocalWildJacquet_whittaker_factors K hζ P v C hC
    (sourceKPJacquet_rootSmooth_of_deepFixed K hζ P ρ C hDeep) ℓ hℓ

end ActualFactor
end
end ArtinMatthews

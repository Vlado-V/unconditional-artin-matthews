module

public import ArtinMatthews.SourceKPAdelicBorel
public import ArtinMatthews.SourceKPAdelicInducedTorus


set_option backward.privateInPublic true
@[expose] public section

/-! Normalized algebraic principal series on the actual c=2 adelic
projective cover. The modular half-power is separate from the genuine
torus character. Evaluation at the identity of the inducing torus
gives the exact rational-Borel scalar function used in the Eisenstein
sum. Smoothness and summability are separate analytic requirements. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicBorelModularHalf : sourceKPAdelicCoveringBorel K hζ →* ℂ :=
  (Units.coeHom ℂ).comp ((sourceKPIdeleComplexNorm K (1/2 : ℂ)).comp
    ((sourceKPAdelicTorusIdele K hζ).comp (sourceKPAdelicBorelTorusProjection K hζ)))

def sourceKPAdelicNormalizedBorelRepresentation (s : ℂ) :
    Representation ℂ (sourceKPAdelicCoveringBorel K hζ) (SourceKPAdelicTorusInducedSpace K hζ s) where
  toFun b := sourceKPAdelicBorelModularHalf K hζ b •
    sourceKPAdelicTorusInducedRepresentation K hζ s (sourceKPAdelicBorelTorusProjection K hζ b)
  map_one' := by rw [map_one, map_one, map_one, one_smul]
  map_mul' b c := by
    change sourceKPAdelicBorelModularHalf K hζ (b*c) •
      sourceKPAdelicTorusInducedRepresentation K hζ s
        (sourceKPAdelicBorelTorusProjection K hζ (b*c)) = _
    rw [map_mul, map_mul, map_mul]
    exact (smul_mul_smul_comm _ _ _ _).symm

abbrev SourceKPAdelicPrincipalSeries (s : ℂ) :=
  sourceAlgebraicInducedSpace (sourceKPAdelicCoveringBorel K hζ)
    (sourceKPAdelicNormalizedBorelRepresentation K hζ s)

def sourceKPAdelicPrincipalSeriesRepresentation (s : ℂ) :
    Representation ℂ (SourceKPAdelicProjective K hζ) (SourceKPAdelicPrincipalSeries K hζ s) :=
  sourceAlgebraicInducedRepresentation (sourceKPAdelicCoveringBorel K hζ)
    (sourceKPAdelicNormalizedBorelRepresentation K hζ s)

def sourceKPAdelicBorelCenter (z : rootsOfUnity 3 K) : sourceKPAdelicCoveringBorel K hζ :=
  sourceKPAdelicBorelTorusInclusion K hζ (sourceKPAdelicTorusInducingCenter K hζ z).val

theorem sourceKPAdelicBorelCenter_val (z : rootsOfUnity 3 K) :
    (sourceKPAdelicBorelCenter K hζ z).val = sourceKPAdelicProjectiveCenter K hζ z :=
  sourceKPAdelicTorusInducingCenter_val K hζ z

theorem sourceKPAdelicTorusIdele_center (z : rootsOfUnity 3 K) :
    sourceKPAdelicTorusIdele K hζ (sourceKPAdelicTorusInducingCenter K hζ z).val = 1 := by
  apply sourceKPProjectiveDiagonalHom_injective 𝔸[K]
  rw [← sourceKPAdelicTorusIdele_projection, sourceKPAdelicTorusInducingCenter_val,
    sourceKPAdelicProjectiveCenter_projection_one, map_one]

theorem sourceKPAdelicBorelModularHalf_center (z : rootsOfUnity 3 K) :
    sourceKPAdelicBorelModularHalf K hζ (sourceKPAdelicBorelCenter K hζ z) = 1 := by
  change ((sourceKPIdeleComplexNorm K (1/2 : ℂ)
    (sourceKPAdelicTorusIdele K hζ
      (sourceKPAdelicBorelTorusProjection K hζ
        (sourceKPAdelicBorelTorusInclusion K hζ (sourceKPAdelicTorusInducingCenter K hζ z).val)))) : ℂ) = 1
  rw [sourceKPAdelicBorelTorusProjection_inclusion, sourceKPAdelicTorusIdele_center,
    map_one, Units.val_one]

theorem sourceKPAdelicNormalizedBorelRepresentation_center (s : ℂ) (z : rootsOfUnity 3 K)
    (v : SourceKPAdelicTorusInducedSpace K hζ s) :
    sourceKPAdelicNormalizedBorelRepresentation K hζ s (sourceKPAdelicBorelCenter K hζ z) v =
      (sourceKPAdelicCentralComplex K hζ z : ℂ) • v := by
  change sourceKPAdelicBorelModularHalf K hζ (sourceKPAdelicBorelCenter K hζ z) •
    sourceKPAdelicTorusInducedRepresentation K hζ s
      (sourceKPAdelicBorelTorusProjection K hζ (sourceKPAdelicBorelCenter K hζ z)) v = _
  rw [sourceKPAdelicBorelModularHalf_center, one_smul]
  change sourceKPAdelicTorusInducedRepresentation K hζ s
    (sourceKPAdelicBorelTorusProjection K hζ
      (sourceKPAdelicBorelTorusInclusion K hζ (sourceKPAdelicTorusInducingCenter K hζ z).val)) v = _
  rw [sourceKPAdelicBorelTorusProjection_inclusion,
    sourceKPAdelicTorusInducedRepresentation_center]

def sourceKPAdelicRationalTorusLift (a : Kˣ) : sourceKPAdelicCoveringTorus K hζ :=
  (sourceKPAdelicRationalCubeToInducing K hζ (sourceKPAdelicRationalCubeFromRational K hζ a)).val

theorem sourceKPAdelicRationalTorusLift_val (a : Kˣ) :
    (sourceKPAdelicRationalTorusLift K hζ a).val =
      sourceKPAdelicProjectiveRationalLift K hζ (sourceKPProjectiveDiagonalHom K a) := rfl

theorem sourceKPAdelicTorusIdele_rational (a : Kˣ) :
    sourceKPAdelicTorusIdele K hζ (sourceKPAdelicRationalTorusLift K hζ a) =
      IdeleGroup.unitEmbedding (𝓞 K) K a := by
  apply sourceKPProjectiveDiagonalHom_injective 𝔸[K]
  rw [← sourceKPAdelicTorusIdele_projection, sourceKPAdelicRationalTorusLift_val,
    sourceKPAdelicProjectiveRationalLift_diagonal, sourceKPAdelicProjectiveDiagonalLift_projection]

theorem sourceKPAdelicRationalBorelLift_coordinates
    (b : sourceKPRationalBorel K) (x : K) (a : Kˣ)
    (hb : b.val = ProjGenLinGroup.mk (sourceKPUpperMatrix K x) * sourceKPProjectiveDiagonalHom K a) :
    sourceKPAdelicRationalBorelLift K hζ b =
      sourceKPAdelicBorelCoordinatesEquiv K hζ
        (algebraMap K 𝔸[K] x, sourceKPAdelicRationalTorusLift K hζ a) := by
  apply Subtype.ext
  change sourceKPAdelicProjectiveRationalLift K hζ b.val =
    sourceKPAdelicUpperLift K hζ (algebraMap K 𝔸[K] x) *
      (sourceKPAdelicRationalTorusLift K hζ a).val
  rw [hb, map_mul, sourceKPAdelicRationalTorusLift_val,
    sourceKPAdelicUpperLift_rational, sourceKPUpperMatrix_field]

theorem sourceKPAdelicBorelModularHalf_rational (b : sourceKPRationalBorel K) :
    sourceKPAdelicBorelModularHalf K hζ (sourceKPAdelicRationalBorelLift K hζ b) = 1 := by
  have hb : b.val ∈ sourceKPRingBorel K := by
    rw [sourceKPRingBorel_field]
    exact b.property
  obtain ⟨x, a, ha⟩ := (sourceKPRingBorel_mem_iff K b.val).mp hb
  rw [sourceKPAdelicRationalBorelLift_coordinates K hζ b x a ha]
  change ((sourceKPIdeleComplexNorm K (1/2 : ℂ)
    (sourceKPAdelicTorusIdele K hζ
      (sourceKPAdelicBorelTorusProjection K hζ
        (sourceKPAdelicBorelCoordinatesEquiv K hζ
          (algebraMap K 𝔸[K] x, sourceKPAdelicRationalTorusLift K hζ a))))) : ℂ) = 1
  rw [sourceKPAdelicBorelTorusProjection_coordinates, sourceKPAdelicTorusIdele_rational,
    sourceKPIdeleComplexNorm_principal, Units.val_one]

theorem sourceKPAdelicTorusInducedRepresentation_rational_one
    (s : ℂ) (a : Kˣ) (v : SourceKPAdelicTorusInducedSpace K hζ s) :
    (sourceKPAdelicTorusInducedRepresentation K hζ s
      (sourceKPAdelicRationalTorusLift K hζ a) v).val 1 = v.val 1 := by
  change v.val (1 * sourceKPAdelicRationalTorusLift K hζ a) = v.val 1
  rw [one_mul]
  simpa only [mul_one, sourceKPAdelicRationalTorusLift] using
    sourceKPAdelicTorusInducedSpace_rational K hζ s a v 1

theorem sourceKPAdelicNormalizedBorelRepresentation_rational_one
    (s : ℂ) (b : sourceKPRationalBorel K) (v : SourceKPAdelicTorusInducedSpace K hζ s) :
    (sourceKPAdelicNormalizedBorelRepresentation K hζ s
      (sourceKPAdelicRationalBorelLift K hζ b) v).val 1 = v.val 1 := by
  have hb : b.val ∈ sourceKPRingBorel K := by
    rw [sourceKPRingBorel_field]
    exact b.property
  obtain ⟨x, a, ha⟩ := (sourceKPRingBorel_mem_iff K b.val).mp hb
  change sourceKPAdelicBorelModularHalf K hζ (sourceKPAdelicRationalBorelLift K hζ b) *
      (sourceKPAdelicTorusInducedRepresentation K hζ s
        (sourceKPAdelicBorelTorusProjection K hζ (sourceKPAdelicRationalBorelLift K hζ b)) v).val 1 = v.val 1
  rw [sourceKPAdelicBorelModularHalf_rational, one_mul,
    sourceKPAdelicRationalBorelLift_coordinates K hζ b x a ha,
    sourceKPAdelicBorelTorusProjection_coordinates,
    sourceKPAdelicTorusInducedRepresentation_rational_one]

def sourceKPAdelicPrincipalSeriesScalar (s : ℂ) (f : SourceKPAdelicPrincipalSeries K hζ s) :
    SourceKPRationalBorelFunction K hζ :=
  ⟨fun g => (f.val g).val 1, by
    intro b hb g
    let b₀ : sourceKPRationalBorel K := ⟨b,hb⟩
    change (f.val ((sourceKPAdelicRationalBorelLift K hζ b₀).val * g)).val 1 = _
    rw [sourceAlgebraicInducedSpace_covariant,
      sourceKPAdelicNormalizedBorelRepresentation_rational_one]⟩

theorem sourceKPAdelicPrincipalSeriesScalar_center (s : ℂ)
    (f : SourceKPAdelicPrincipalSeries K hζ s) (z : rootsOfUnity 3 K)
    (g : SourceKPAdelicProjective K hζ) :
    (sourceKPAdelicPrincipalSeriesScalar K hζ s f).val
      (sourceKPAdelicProjectiveCenter K hζ z * g) =
      (sourceKPAdelicCentralComplex K hζ z : ℂ) *
        (sourceKPAdelicPrincipalSeriesScalar K hζ s f).val g := by
  change (f.val (sourceKPAdelicProjectiveCenter K hζ z * g)).val 1 = _
  rw [← sourceKPAdelicBorelCenter_val, sourceAlgebraicInducedSpace_covariant,
    sourceKPAdelicNormalizedBorelRepresentation_center]
  rfl

def sourceKPAdelicEisensteinSum (s : ℂ) (f : SourceKPAdelicPrincipalSeries K hζ s)
    (g : SourceKPAdelicProjective K hζ) : ℂ :=
  sourceKPAdelicRationalSum K hζ (sourceKPAdelicPrincipalSeriesScalar K hζ s f) g

def sourceKPAdelicEisensteinConverges (s : ℂ) (f : SourceKPAdelicPrincipalSeries K hζ s)
    (g : SourceKPAdelicProjective K hζ) : Prop :=
  Summable (sourceKPAdelicRationalSummand K hζ (sourceKPAdelicPrincipalSeriesScalar K hζ s f) g)

theorem sourceKPAdelicEisensteinSum_rational (s : ℂ) (f : SourceKPAdelicPrincipalSeries K hζ s)
    (g : SourceKPAdelicProjective K hζ) (hg : sourceKPAdelicEisensteinConverges K hζ s f g)
    (γ : PGL(2, K)) :
    sourceKPAdelicEisensteinSum K hζ s f (sourceKPAdelicProjectiveRationalLift K hζ γ * g) =
      sourceKPAdelicEisensteinSum K hζ s f g :=
  (sourceKPAdelicRationalSum_hasSum_translate K hζ (sourceKPAdelicPrincipalSeriesScalar K hζ s f)
    γ g hg.hasSum).tsum_eq

theorem sourceKPAdelicEisensteinSum_weyl (s : ℂ) (f : SourceKPAdelicPrincipalSeries K hζ s)
    (g : SourceKPAdelicProjective K hζ) (hg : sourceKPAdelicEisensteinConverges K hζ s f g) :
    sourceKPAdelicEisensteinSum K hζ s f (sourceKPAdelicProjectiveWeyl K hζ * g) =
      sourceKPAdelicEisensteinSum K hζ s f g :=
  sourceKPAdelicEisensteinSum_rational K hζ s f g hg
    (ProjGenLinGroup.mk (sourceKPWeylMatrix K))

theorem sourceKPAdelicEisensteinSum_bruhat (s : ℂ) (f : SourceKPAdelicPrincipalSeries K hζ s)
    (g : SourceKPAdelicProjective K hζ) (hg : sourceKPAdelicEisensteinConverges K hζ s f g) :
    sourceKPAdelicEisensteinSum K hζ s f g = (f.val g).val 1 +
      ∑' x : K, (f.val (sourceKPAdelicProjectiveWeyl K hζ *
        sourceKPAdelicUpperLift K hζ (algebraMap K 𝔸[K] x) * g)).val 1 :=
  sourceKPAdelicRationalSum_canonical_bruhat K hζ (sourceKPAdelicPrincipalSeriesScalar K hζ s f) g hg

theorem sourceKPAdelicEisensteinSum_center (s : ℂ) (f : SourceKPAdelicPrincipalSeries K hζ s)
    (z : rootsOfUnity 3 K) (g : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicEisensteinSum K hζ s f (sourceKPAdelicProjectiveCenter K hζ z * g) =
      (sourceKPAdelicCentralComplex K hζ z : ℂ) * sourceKPAdelicEisensteinSum K hζ s f g :=
  sourceKPAdelicRationalSum_genuine K hζ (sourceKPAdelicPrincipalSeriesScalar K hζ s f)
    (sourceKPAdelicPrincipalSeriesScalar_center K hζ s f) z g

end
end ArtinMatthews

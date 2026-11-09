module

public import ArtinMatthews.SourceKPArchRadialFlow
public import ArtinMatthews.SourceKPAdelicHighHeightFinite
public import ArtinMatthews.SourceKPAdelicCuspOverlap


set_option backward.privateInPublic true
@[expose] public section

/-! The actual high cusp is the rational upper-Borel quotient of its high representatives. -/
namespace ArtinMatthews
open NumberField Matrix Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPFiniteLevelHeight_rationalBorel (γ : PGL(2,K))
    (hγ : γ ∈ sourceKPRationalBorel K) (x : SourceKPFiniteLevelSpace K hζ) :
    sourceKPFiniteLevelHeight K hζ (γ • x) = sourceKPFiniteLevelHeight K hζ x := by
  obtain ⟨q,rfl⟩ := sourceKPFiniteLevelMk_surjective K hζ x
  rw [← sourceKPFiniteLevelMk_rational, sourceKPFiniteLevelHeight_mk,
    sourceKPFiniteLevelHeight_mk, sourceKPAdelicCoverHeight_left_rationalBorel K hζ γ hγ]

theorem sourceKPFiniteLevelHeight_high_overlap (γ : PGL(2,K))
    (x : SourceKPFiniteLevelSpace K hζ) (hx : 1 < sourceKPFiniteLevelHeight K hζ x)
    (hγx : 1 < sourceKPFiniteLevelHeight K hζ (γ • x)) : γ ∈ sourceKPRationalBorel K := by
  obtain ⟨q,rfl⟩ := sourceKPFiniteLevelMk_surjective K hζ x
  apply sourceKPAdelicCoverHeight_high_overlap K hζ q γ hx
  simpa only [← sourceKPFiniteLevelMk_rational, sourceKPFiniteLevelHeight_mk] using hγx

theorem sourceKPFiniteLevelHeight_cusp_separation (γ : PGL(2,K))
    (hγ : γ ∉ sourceKPRationalBorel K) (x : SourceKPFiniteLevelSpace K hζ) :
    sourceKPFiniteLevelHeight K hζ x * sourceKPFiniteLevelHeight K hζ (γ • x) ≤ 1 := by
  obtain ⟨q,rfl⟩ := sourceKPFiniteLevelMk_surjective K hζ x
  simpa only [← sourceKPFiniteLevelMk_rational, sourceKPFiniteLevelHeight_mk] using
    sourceKPAdelicCoverHeight_cusp_separation K hζ q γ hγ

theorem sourceKPFiniteLevelOrbitHeight_eq_height_of_high
    (x : SourceKPFiniteLevelSpace K hζ) (hx : 1 < sourceKPFiniteLevelHeight K hζ x) :
    sourceKPFiniteLevelOrbitHeight K hζ x = sourceKPFiniteLevelHeight K hζ x := by
  apply le_antisymm ?_ (sourceKPFiniteLevelHeight_le_orbit K hζ x)
  rw [sourceKPFiniteLevelOrbitHeight_eq_iSup]
  change sSup (Set.range (fun γ : PGL(2,K) => sourceKPFiniteLevelHeight K hζ (γ • x))) ≤ _
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨γ,rfl⟩
  by_cases hγ : γ ∈ sourceKPRationalBorel K
  · exact (sourceKPFiniteLevelHeight_rationalBorel K hζ γ hγ x).le
  · have hb := sourceKPFiniteLevelHeight_cusp_separation K hζ γ hγ x
    have hp := sourceKPFiniteLevelHeight_pos K hζ x
    have hba : sourceKPFiniteLevelHeight K hζ (γ • x) ≤ 1 / sourceKPFiniteLevelHeight K hζ x := by
      apply (le_div_iff₀ hp).mpr
      simpa only [mul_comm] using hb
    exact (hba.trans ((div_lt_one hp).mpr hx).le).trans hx.le

abbrev SourceKPHighCuspFinite (T : ℝ) :=
  {x : SourceKPFiniteLevelSpace K hζ // T < sourceKPFiniteLevelHeight K hζ x}

abbrev SourceKPHighCuspAutomorphic (T : ℝ) :=
  {x : SourceKPAutomorphicLevel K hζ // T < sourceKPAutomorphicOrbitHeight K hζ x}

instance sourceKPHighCuspFinite_action (T : ℝ) :
    MulAction (sourceKPRationalBorel K) (SourceKPHighCuspFinite K hζ T) where
  smul b x := ⟨b.val • x.val, by
    rw [sourceKPFiniteLevelHeight_rationalBorel K hζ b.val b.property]
    exact x.property⟩
  one_smul x := Subtype.ext (one_smul (PGL(2,K)) x.val)
  mul_smul b c x := Subtype.ext (mul_smul b.val c.val x.val)

instance sourceKPHighCuspFinite_continuousConst (T : ℝ) :
    ContinuousConstSMul (sourceKPRationalBorel K) (SourceKPHighCuspFinite K hζ T) :=
  ⟨fun b => ((sourceKPFiniteLevel_rational_continuous K hζ b.val).comp
    continuous_subtype_val).subtype_mk _⟩

abbrev SourceKPHighCuspBorelQuotient (T : ℝ) :=
  Quotient (MulAction.orbitRel (sourceKPRationalBorel K) (SourceKPHighCuspFinite K hζ T))

def sourceKPHighCuspProjection (T : ℝ) (x : SourceKPHighCuspFinite K hζ T) :
    SourceKPHighCuspAutomorphic K hζ T :=
  ⟨Quotient.mk _ x.val, by
    rw [sourceKPAutomorphicOrbitHeight_of_finite]
    exact x.property.trans_le (sourceKPFiniteLevelHeight_le_orbit K hζ x.val)⟩

def sourceKPHighCuspQuotientMap (T : ℝ) :
    SourceKPHighCuspBorelQuotient K hζ T → SourceKPHighCuspAutomorphic K hζ T :=
  Quotient.lift (sourceKPHighCuspProjection K hζ T) (by
    intro x y hxy
    obtain ⟨b,hb⟩ := MulAction.mem_orbit_iff.mp hxy
    apply Subtype.ext
    apply Quotient.sound
    apply MulAction.mem_orbit_iff.mpr
    exact ⟨b.val, congrArg Subtype.val hb⟩)

theorem sourceKPHighCuspQuotientMap_mk (T : ℝ) (x : SourceKPHighCuspFinite K hζ T) :
    sourceKPHighCuspQuotientMap K hζ T (Quotient.mk _ x) =
      sourceKPHighCuspProjection K hζ T x := rfl

theorem sourceKPHighCuspQuotientMap_continuous (T : ℝ) :
    Continuous (sourceKPHighCuspQuotientMap K hζ T) := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  exact (continuous_quotient_mk'.comp continuous_subtype_val).subtype_mk _

theorem sourceKPHighCuspQuotientMap_surjective (T : ℝ) :
    Function.Surjective (sourceKPHighCuspQuotientMap K hζ T) := by
  intro q
  obtain ⟨g,hg⟩ := sourceKPAutomorphicLevelMk_surjective K hζ q.val
  let x := sourceKPFiniteLevelMk K hζ g
  have hqx : (Quotient.mk _ x : SourceKPAutomorphicLevel K hζ) = q.val := hg
  have hsup : T < sSup (Set.range (fun γ : PGL(2,K) => sourceKPFiniteLevelHeight K hζ (γ • x))) := by
    have h := q.property
    rw [← hqx, sourceKPAutomorphicOrbitHeight_of_finite,
      sourceKPFiniteLevelOrbitHeight_eq_iSup] at h
    exact h
  obtain ⟨a,⟨γ,rfl⟩,hγ⟩ := exists_lt_of_lt_csSup (Set.range_nonempty _) hsup
  let y : SourceKPHighCuspFinite K hζ T := ⟨γ • x,hγ⟩
  refine ⟨Quotient.mk _ y, ?_⟩
  apply Subtype.ext
  change (Quotient.mk _ (γ • x) : SourceKPAutomorphicLevel K hζ) = q.val
  rw [← hqx]
  exact Quotient.sound (MulAction.mem_orbit_iff.mpr ⟨γ,rfl⟩)

theorem sourceKPHighCuspQuotientMap_injective (T : ℝ) (hT : 1 < T) :
    Function.Injective (sourceKPHighCuspQuotientMap K hζ T) := by
  intro a b
  induction a using Quotient.inductionOn with
  | _ x =>
    induction b using Quotient.inductionOn with
    | _ y =>
      intro he
      have hxy : (Quotient.mk _ x.val : SourceKPAutomorphicLevel K hζ) = Quotient.mk _ y.val :=
        congrArg Subtype.val he
      obtain ⟨γ,hγ⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact hxy)
      have hγB : γ ∈ sourceKPRationalBorel K := by
        apply sourceKPFiniteLevelHeight_high_overlap K hζ γ y.val (hT.trans y.property)
        rw [hγ]
        exact hT.trans x.property
      apply Quotient.sound
      apply MulAction.mem_orbit_iff.mpr
      refine ⟨⟨γ,hγB⟩, ?_⟩
      exact Subtype.ext hγ

theorem sourceKPHighCuspQuotientMap_isOpen (T : ℝ) :
    IsOpenMap (sourceKPHighCuspQuotientMap K hζ T) := by
  have hU : IsOpen {x : SourceKPFiniteLevelSpace K hζ | T < sourceKPFiniteLevelHeight K hζ x} :=
    isOpen_lt continuous_const (sourceKPFiniteLevelHeight_continuous K hζ)
  have hraw : IsOpenMap (sourceKPHighCuspProjection K hζ T) := by
    apply IsOpenMap.subtype_mk
    exact isOpenMap_quotient_mk'_mul.comp hU.isOpenMap_subtype_val
  exact IsOpenMap.of_comp continuous_quotient_mk' Quotient.mk_surjective hraw

def sourceKPHighCuspHomeomorph (T : ℝ) (hT : 1 < T) :
    SourceKPHighCuspBorelQuotient K hζ T ≃ₜ SourceKPHighCuspAutomorphic K hζ T :=
  (Equiv.ofBijective (sourceKPHighCuspQuotientMap K hζ T)
    ⟨sourceKPHighCuspQuotientMap_injective K hζ T hT,
      sourceKPHighCuspQuotientMap_surjective K hζ T⟩).toHomeomorphOfContinuousOpen
    (sourceKPHighCuspQuotientMap_continuous K hζ T) (sourceKPHighCuspQuotientMap_isOpen K hζ T)

end
end ArtinMatthews

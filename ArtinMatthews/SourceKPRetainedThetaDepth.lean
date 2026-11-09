module

public import ArtinMatthews.SourceKPRetainedDepthCutoff
public import ArtinMatthews.SourceReflectionLocalThetaCharacter


set_option backward.privateInPublic true
@[expose] public section

/-! An actual ball depth places each retained cutoff inside the original
local higher-unit subgroup of the theta multiplier. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain SourcePhysical SourceReflection StandardAdelic
open RayClass QuadraticWeil VaryingKummerAnalytic Topology
open scoped NumberField SourcePhysical Classical

noncomputable section

variable (K : Type) [Field K] [NumberField K]

private theorem unit_open_contains_ball (P : HeightOneSpectrum (𝓞 K))
    (U : Set (P.adicCompletion K)ˣ) (hU : IsOpen U) (h1 : 1 ∈ U) :
    ∃ M : ℕ, ∀ t : (P.adicCompletion K)ˣ,
      ((t:P.adicCompletion K)-1) ∈ sourceLocalBall K P (-(M:ℤ)) → t ∈ U := by
  let L := P.adicCompletion K
  let W := (Units.val : Lˣ → L) '' U
  have hW : IsOpen W := (IsOpenUnits.isOpenEmbedding_unitsVal (M := L)).isOpenMap U hU
  let E := (fun x : L => 1+x) ⁻¹' W
  have hE : IsOpen E := hW.preimage (continuous_const.add continuous_id)
  have h0 : (0:L) ∈ E := ⟨1,h1,by simp⟩
  obtain ⟨n,hn⟩ := sourceLocalBall_subset_of_mem_nhds_zero K P (hE.mem_nhds h0)
  let M := (-n).toNat
  refine ⟨M,fun t ht => ?_⟩
  have hM : -(M:ℤ) ≤ n := by
    dsimp [M]
    omega
  obtain ⟨u,hu,he⟩ := hn (ht.trans (WithZero.exp_le_exp.mpr hM))
  have hut : u = t := Units.ext (he.trans (by ring))
  exact hut ▸ hu

def sourceKPRetainedModulusDepth (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n : FiniteModulus K) (P : S) : ℕ :=
  Classical.choose (unit_open_contains_ball K P.val (localHigherUnitGroup P.val (n P.val) : Set _)
    (isOpen_localHigherUnitGroup P.val (n P.val)) (localHigherUnitGroup P.val (n P.val)).one_mem)

theorem sourceKPRetainedModulusDepth_mem (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n : FiniteModulus K) (u : SFiniteUnits K S)
    (h : ∀ P : S, ((u P : P.val.adicCompletion K)-1) ∈
      sourceLocalBall K P.val (-(sourceKPRetainedModulusDepth K S n P:ℤ))) :
    u ∈ sourceReflectionDeepUnits K S n := by
  apply (sourceReflectionDeepUnits_mem_iff K S n u).mpr
  intro P
  exact Classical.choose_spec (unit_open_contains_ball K P.val
    (localHigherUnitGroup P.val (n P.val) : Set _) (isOpen_localHigherUnitGroup P.val (n P.val))
    (localHigherUnitGroup P.val (n P.val)).one_mem) (u P) (h P)

theorem sourceKPRetainedThetaFactor_eq_one {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    {J : Ideal (𝓞 K)} (hJ : J ≠ ⊥) (η : EvenIdealRayCharacter K J)
    (w : SFiniteUnits K (sourceHilbertSet K S₀))
    (h : ∀ P : sourceHilbertSet K S₀, ((w P : P.val.adicCompletion K)-1) ∈
      sourceLocalBall K P.val (-(sourceKPRetainedModulusDepth K (sourceHilbertSet K S₀)
        (sourceReflectionThetaModulus K S₀ hJ) P:ℤ))) :
    letI : IsTotallyComplex K := source_isTotallyComplex K hζ
    sourceReflectionLocalThetaCharacter K S₀ hJ hζ hS η w = 1 := by
  letI : IsTotallyComplex K := source_isTotallyComplex K hζ
  exact sourceReflectionLocalThetaCharacter_deep K S₀ hJ hζ hS η w
    (sourceKPRetainedModulusDepth_mem K (sourceHilbertSet K S₀) (sourceReflectionThetaModulus K S₀ hJ) w h)

end
end ArtinMatthews

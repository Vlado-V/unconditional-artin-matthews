module

public import ArtinMatthews.SLocalWholePowerClasses
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalTopology


set_option backward.privateInPublic true
@[expose] public section

/-! Arithmetic isolation of the actual diagonal S-unit group in the
literal product of S-local units.  Finite local-unit conditions force
an S-unit into the ordinary integer lattice, which separates it at 1. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

def sWholeMixed (y : SWholeUnits K S) : NumberField.mixedEmbedding.mixedSpace K :=
  NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K
    (fun w : InfinitePlace K => (y.1 w : w.Completion))

theorem continuous_sWholeMixed : Continuous (sWholeMixed K S) := by
  rw [show sWholeMixed K S = fun y =>
    (fun w : {w : InfinitePlace K // w.IsReal} =>
        InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (y.1 w : w.val.Completion),
     fun w : {w : InfinitePlace K // w.IsComplex} =>
        InfinitePlace.Completion.extensionEmbedding w.val (y.1 w : w.val.Completion)) by
    funext y
    exact InfiniteAdeleRing.ringEquiv_mixedSpace_apply K _]
  apply Continuous.prodMk
  · apply continuous_pi
    intro w
    exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).continuous.comp
      (Units.continuous_val.comp ((continuous_apply w.val).comp continuous_fst))
  · apply continuous_pi
    intro w
    exact (InfinitePlace.Completion.isometry_extensionEmbedding w.val).continuous.comp
      (Units.continuous_val.comp ((continuous_apply w.val).comp continuous_fst))

theorem sWholeMixed_diagonal (u : Kˣ) :
    sWholeMixed K S (sWholeDiagonal K S u) = NumberField.mixedEmbedding K (u : K) :=
  (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp K (x := (u : K))).symm

theorem sWholeMixed_one : sWholeMixed K S 1 = NumberField.mixedEmbedding K (1 : K) := by
  rw [← map_one (sWholeDiagonal K S), sWholeMixed_diagonal, Units.val_one]

theorem sUnit_integer_of_localUnits (u : SUnitGroup (K := K) S)
    (hu : ∀ v : S, (sWholeDiagonal K S (u : Kˣ)).2 v ∈ (v.val.adicCompletionIntegers K).units) :
    ∃ x : 𝓞 K, algebraMap (𝓞 K) K x = (u : Kˣ) := by
  apply HeightOneSpectrum.mem_integers_of_valuation_le_one K
  intro v
  by_cases hv : v ∈ S
  · have h := (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp
      (hu ⟨v, hv⟩))
    change Valued.v (((u : Kˣ) : K) : v.adicCompletion K) = 1 at h
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
    exact h.le
  · exact (u.property v hv).le

theorem exists_sWholeUnit_open_isolation : ∃ V : Set (SWholeUnits K S),
    IsOpen V ∧ 1 ∈ V ∧ ∀ u : SUnitGroup (K := K) S,
      sWholeDiagonal K S (u : Kˣ) ∈ V → sWholeDiagonal K S (u : Kˣ) = 1 := by
  let z : NumberField.mixedEmbedding.integerLattice K :=
    ⟨NumberField.mixedEmbedding K (1 : K), IdeleGroup.mixedEmbedding_one_mem_integerLattice⟩
  have hz : IsOpen ({z} : Set (NumberField.mixedEmbedding.integerLattice K)) := isOpen_discrete _
  rw [isOpen_induced_iff] at hz
  obtain ⟨U, hU, heU⟩ := hz
  have hzU : z.val ∈ U := by
    change z ∈ Subtype.val ⁻¹' U
    rw [heU]
    exact Set.mem_singleton z
  let W : Set (SWholeUnits K S) := ⋂ v : S,
    (fun y : SWholeUnits K S => y.2 v) ⁻¹' (v.val.adicCompletionIntegers K).units
  have hW : IsOpen W := by
    apply isOpen_iInter_of_finite
    intro v
    exact (isOpen_finiteLocalUnits K v.val).preimage ((continuous_apply v).comp continuous_snd)
  have h1W : (1 : SWholeUnits K S) ∈ W := by
    apply Set.mem_iInter.mpr
    intro v
    exact (v.val.adicCompletionIntegers K).units.one_mem
  refine ⟨(sWholeMixed K S) ⁻¹' U ∩ W, (hU.preimage (continuous_sWholeMixed K S)).inter hW,
    ⟨?_, h1W⟩, ?_⟩
  · change sWholeMixed K S 1 ∈ U
    rw [sWholeMixed_one]
    exact hzU
  · intro u hu
    obtain ⟨x, hx⟩ := sUnit_integer_of_localUnits K S u (Set.mem_iInter.mp hu.2)
    let y : NumberField.mixedEmbedding.integerLattice K :=
      ⟨NumberField.mixedEmbedding K ((u : Kˣ) : K), by
        change _ ∈ LinearMap.range _
        refine ⟨x, ?_⟩
        change NumberField.mixedEmbedding K (algebraMap (𝓞 K) K x) = _
        rw [hx]⟩
    have hyU : y ∈ Subtype.val ⁻¹' U := by
      change NumberField.mixedEmbedding K ((u : Kˣ) : K) ∈ U
      have ht : sWholeMixed K S (sWholeDiagonal K S (u : Kˣ)) ∈ U := hu.1
      rwa [sWholeMixed_diagonal] at ht
    rw [heU] at hyU
    have hyz : y = z := Set.mem_singleton_iff.mp hyU
    have he : (u : Kˣ) = 1 := Units.ext
      (NumberField.mixedEmbedding_injective K (congrArg Subtype.val hyz))
    rw [he, map_one]

end
end ArtinMatthews.SourcePhysical

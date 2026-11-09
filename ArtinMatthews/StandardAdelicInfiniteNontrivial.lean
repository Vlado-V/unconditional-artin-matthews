module

public import ArtinMatthews.StandardAdelicCharacter


set_option backward.privateInPublic true
@[expose] public section

/-! Every archimedean local restriction of the actual standard adelic
character is nontrivial, with the real/complex trace multiplicities kept. -/
namespace ArtinMatthews.StandardAdelic

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open IsDedekindDomain
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField BigOperators Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

theorem archTrace_single_real (v : InfinitePlace K) (hv : IsReal v) (x : v.Completion) :
    archTrace K (Pi.single v x) = extensionEmbeddingOfIsReal hv x := by
  change (∑ w : {w : InfinitePlace K // IsReal w}, extensionEmbeddingOfIsReal w.property (Pi.single v x w.val)) +
    (∑ w : {w : InfinitePlace K // IsComplex w}, 2 * (extensionEmbedding w.val (Pi.single v x w.val)).re) = _
  have hr : (∑ w : {w : InfinitePlace K // IsReal w}, extensionEmbeddingOfIsReal w.property (Pi.single v x w.val)) =
      extensionEmbeddingOfIsReal hv x := by
    rw [Finset.sum_eq_single (⟨v,hv⟩ : {w : InfinitePlace K // IsReal w})]
    · rw [Pi.single_eq_same]
    · intro w _ hw
      have he : w.val ≠ v := fun h => hw (Subtype.ext h)
      rw [Pi.single_eq_of_ne he, map_zero]
    · simp
  have hc : (∑ w : {w : InfinitePlace K // IsComplex w}, 2 * (extensionEmbedding w.val (Pi.single v x w.val)).re) = 0 := by
    apply Finset.sum_eq_zero
    intro w _
    have he : w.val ≠ v := by
      intro he
      apply (not_isReal_iff_isComplex.mpr w.property)
      rw [he]
      exact hv
    rw [Pi.single_eq_of_ne he, map_zero, Complex.zero_re, mul_zero]
  rw [hr,hc,add_zero]

theorem archTrace_single_complex (v : InfinitePlace K) (hv : IsComplex v) (x : v.Completion) :
    archTrace K (Pi.single v x) = 2 * (extensionEmbedding v x).re := by
  change (∑ w : {w : InfinitePlace K // IsReal w}, extensionEmbeddingOfIsReal w.property (Pi.single v x w.val)) +
    (∑ w : {w : InfinitePlace K // IsComplex w}, 2 * (extensionEmbedding w.val (Pi.single v x w.val)).re) = _
  have hr : (∑ w : {w : InfinitePlace K // IsReal w}, extensionEmbeddingOfIsReal w.property (Pi.single v x w.val)) = 0 := by
    apply Finset.sum_eq_zero
    intro w _
    have he : w.val ≠ v := by
      intro he
      apply (not_isReal_iff_isComplex.mpr hv)
      rw [← he]
      exact w.property
    rw [Pi.single_eq_of_ne he, map_zero]
  have hc : (∑ w : {w : InfinitePlace K // IsComplex w}, 2 * (extensionEmbedding w.val (Pi.single v x w.val)).re) =
      2 * (extensionEmbedding v x).re := by
    rw [Finset.sum_eq_single (⟨v,hv⟩ : {w : InfinitePlace K // IsComplex w})]
    · rw [Pi.single_eq_same]
    · intro w _ hw
      have he : w.val ≠ v := fun h => hw (Subtype.ext h)
      rw [Pi.single_eq_of_ne he, map_zero, Complex.zero_re, mul_zero]
    · simp
  rw [hr,hc,zero_add]

def localInfiniteCharacter (v : InfinitePlace K) : AddChar v.Completion ℂ :=
  Characters.Construction.localAdditiveCharacter K (character K) (.inl v)

theorem localInfiniteCharacter_single (v : InfinitePlace K) (x : v.Completion) :
    localInfiniteCharacter K v x = archCharacter K (Pi.single v x) := character_arch K _

theorem archCharacter_ne_one_of_trace_half (x : InfiniteAdeleRing K) (hx : archTrace K x = 1/2) :
    archCharacter K x ≠ 1 := by
  change Complex.exp ((archTrace K x : ℂ) * (2*(Real.pi : ℂ)*Complex.I)) ≠ 1
  rw [hx]
  rw [show ((1/2 : ℝ) : ℂ)*(2*(Real.pi : ℂ)*Complex.I) = (Real.pi : ℂ)*Complex.I by push_cast; ring,
    Complex.exp_pi_mul_I]
  norm_num

theorem localInfiniteCharacter_nontrivial (v : InfinitePlace K) :
    ∃ x : v.Completion, localInfiniteCharacter K v x ≠ 1 := by
  by_cases hv : IsReal v
  · refine ⟨(1/2 : v.Completion), ?_⟩
    rw [localInfiniteCharacter_single]
    apply archCharacter_ne_one_of_trace_half
    rw [archTrace_single_real K v hv]
    simp only [map_div₀, map_one, map_ofNat]
  · refine ⟨(1/4 : v.Completion), ?_⟩
    rw [localInfiniteCharacter_single]
    apply archCharacter_ne_one_of_trace_half
    rw [archTrace_single_complex K v (not_isReal_iff_isComplex.mp hv)]
    simp only [map_div₀, map_one, map_ofNat]
    norm_num

theorem character_local_nontrivial (v : ArchimedeanAdeles.Construction.Places K)
    (hfinite : ∀ P : HeightOneSpectrum (𝓞 K), ∃ x : P.adicCompletion K, localFiniteCharacter K P x ≠ 1) :
    ∃ x : ArchimedeanAdeles.Construction.Completion K v,
      Characters.Construction.localAdditiveCharacter K (character K) v x ≠ 1 := by
  cases v with
  | inl v => exact localInfiniteCharacter_nontrivial K v
  | inr v => exact hfinite v

end
end ArtinMatthews.StandardAdelic

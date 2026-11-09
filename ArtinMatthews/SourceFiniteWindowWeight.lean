module

public import ArtinMatthews.SourceFiniteWindowStep
public import ArtinMatthews.SourceKPCoupledWindowBase


set_option backward.privateInPublic true
@[expose] public section

/-! Finite products of local integrable weights on the actual adelic window. -/

namespace ArtinMatthews

open NumberField IsDedekindDomain MeasureTheory SourcePhysical
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField AdeleRing BigOperators Classical

noncomputable section

variable (K : Type) [Field K] [NumberField K]

local instance windowWeightFiniteMeasurable : MeasurableSpace 𝔸ᶠ[K] := borel 𝔸ᶠ[K]
local instance windowWeightFiniteBorel : BorelSpace 𝔸ᶠ[K] := ⟨rfl⟩
local instance windowWeightCompletionMeasurable (P : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (P.adicCompletion K) := borel _
local instance windowWeightCompletionBorel (P : HeightOneSpectrum (𝓞 K)) :
    BorelSpace (P.adicCompletion K) := ⟨rfl⟩

theorem sourceKPFiniteWindow_integrableOn_place {E : Type*} [NormedAddCommGroup E]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (P : HeightOneSpectrum (𝓞 K))
    (f : 𝔸ᶠ[K] → E) :
    IntegrableOn f (sourceKPFiniteWindow K S) (sourceKPFiniteStandardHaar K) ↔
      Integrable (fun p : P.adicCompletion K × sourceKPFinitePlaceRemainder K P =>
        f (sourceKPFiniteAdditiveSingle K P p.1 + p.2.val))
        (((sourceJacquetHaar K P).restrict
          (if P ∈ S then Set.univ else (P.adicCompletionIntegers K : Set _))).prod
          ((sourceKPFinitePlaceRemainderStandardHaar K P).restrict
            (sourceKPFiniteWindowRemainderSet K P S))) := by
  let e := (sourceKPFinitePlaceSplit K P).toHomeomorph.toMeasurableEquiv.symm
  let μ := sourceJacquetHaar K P
  let ν := sourceKPFinitePlaceRemainderStandardHaar K P
  let : μ.IsAddHaarMeasure := sourceJacquetHaar_isAddHaar K P
  have hm : sourceKPFiniteStandardHaar K = Measure.map e (μ.prod ν) :=
    sourceKPFiniteStandardHaar_place_split K P
  have hp : e ⁻¹' sourceKPFiniteWindow K S =
      (if P ∈ S then Set.univ else (P.adicCompletionIntegers K : Set _)) ×ˢ
        sourceKPFiniteWindowRemainderSet K P S := by
    ext p
    change sourceKPFiniteAdditiveSingle K P p.1 + p.2.val ∈ sourceKPFiniteWindow K S ↔ _
    rw [sourceKPFiniteWindow_single_add]
    by_cases hP : P ∈ S <;> simp [hP, sourceKPFiniteWindowRemainderSet]
  have hi : IntegrableOn f (sourceKPFiniteWindow K S) (Measure.map e (μ.prod ν)) ↔
      IntegrableOn (f ∘ e) (e ⁻¹' sourceKPFiniteWindow K S) (μ.prod ν) :=
    integrableOn_map_equiv e
  have he : (f ∘ e) = (fun p : P.adicCompletion K × sourceKPFinitePlaceRemainder K P =>
      f (sourceKPFiniteAdditiveSingle K P p.1 + p.2.val)) := by
    funext p
    obtain ⟨x, r⟩ := p
    change f ((sourceKPFinitePlaceSplit K P).symm (x, r)) = _
    rw [sourceKPFinitePlaceSplit_symm_apply]
  rw [← hm, hp] at hi
  simpa only [he, IntegrableOn, ← Measure.prod_restrict, μ, ν] using hi

theorem sourceKPFiniteWindow_prod_integrableOn
    (F : (P : HeightOneSpectrum (𝓞 K)) → P.adicCompletion K → ℝ)
    (hF : ∀ P, Integrable (F P) (sourceJacquetHaar K P))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IntegrableOn (fun x : 𝔸ᶠ[K] => ∏ P ∈ S, F P (x P))
      (sourceKPFiniteWindow K S) (sourceKPFiniteStandardHaar K) := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, sourceKPCoupledWindow_empty K]
    exact integrableOn_const (IntegralAdeles.Construction.isCompact_finiteIntegralRing K).measure_ne_top
  | @insert P S hPS ih =>
    let L := P.adicCompletion K
    let R := sourceKPFinitePlaceRemainder K P
    let μ := sourceJacquetHaar K P
    let ν := (sourceKPFinitePlaceRemainderStandardHaar K P).restrict
      (sourceKPFiniteWindowRemainderSet K P (insert P S))
    let O : Set L := P.adicCompletionIntegers K
    let f (x : 𝔸ᶠ[K]) := ∏ Q ∈ S, F Q (x Q)
    let : μ.IsAddHaarMeasure := sourceJacquetHaar_isAddHaar K P
    have hR : sourceKPFiniteWindowRemainderSet K P S =
        sourceKPFiniteWindowRemainderSet K P (insert P S) := by
      ext r
      have he := sourceKPFiniteWindow_remainder_erase K (insert P S) P r
      rw [Finset.erase_insert hPS] at he
      exact he
    have hi : Integrable (fun p : L × R => f (sourceKPFiniteAdditiveSingle K P p.1 + p.2.val))
        ((μ.restrict O).prod ν) := by
      have h := (sourceKPFiniteWindow_integrableOn_place K S P f).mp ih
      simpa only [ite_eq_right hPS, hR] using h
    have he (p : L × R) : f (sourceKPFiniteAdditiveSingle K P p.1 + p.2.val) = f p.2.val := by
      apply Finset.prod_congr rfl
      intro Q hQS
      have hQP : Q ≠ P := fun he => hPS (he ▸ hQS)
      change F Q (sourceKPFiniteAdditiveSingle K P p.1 Q + p.2.val Q) = _
      rw [sourceKPFiniteAdditiveSingle_other K P p.1 Q hQP, zero_add]
    have hμ0 : μ.restrict O ≠ 0 := by
      have hO : μ O = 1 := by
        change sourceJacquetHaar K P (P.adicCompletionIntegers K : Set L) = 1
        rw [← sourceLocalBall_zero K P, sourceLocalBall_zero_eq_integerOpen K P,
          sourceJacquetHaar_integers K P]
      exact fun h => one_ne_zero (hO.symm.trans (Measure.restrict_eq_zero.mp h))
    have hr : Integrable (fun r : R => f r.val) ν :=
      (hi.congr (Filter.Eventually.of_forall he)).of_comp_snd hμ0
    apply (sourceKPFiniteWindow_integrableOn_place K (insert P S) P _).mpr
    rw [ite_eq_left (Finset.mem_insert_self P S), Measure.restrict_univ]
    apply ((hF P).mul_prod hr).congr
    filter_upwards with p
    change F P p.1 * f p.2.val =
      ∏ Q ∈ insert P S, F Q ((sourceKPFiniteAdditiveSingle K P p.1 + p.2.val) Q)
    rw [Finset.prod_insert hPS]
    change F P p.1 * f p.2.val =
      F P (sourceKPFiniteAdditiveSingle K P p.1 P + p.2.val P) *
        f (sourceKPFiniteAdditiveSingle K P p.1 + p.2.val)
    have hr0 : p.2.val P = 0 := p.2.property
    rw [sourceKPFiniteAdditiveSingle_same K P p.1, hr0, add_zero, he p]

end
end ArtinMatthews

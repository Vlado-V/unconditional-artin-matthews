module

public import ArtinMatthews.SourceFiniteWindowStep
public import ArtinMatthews.SourceKPExteriorEuler


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open NumberField IsDedekindDomain MeasureTheory Filter
open scoped NumberField AdeleRing Classical BigOperators Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K]

local instance windowEulerFiniteMeasurable : MeasurableSpace 𝔸ᶠ[K] := borel 𝔸ᶠ[K]
local instance windowEulerFiniteBorel : BorelSpace 𝔸ᶠ[K] := ⟨rfl⟩
local instance windowEulerCompletionMeasurable (P : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (P.adicCompletion K) := borel _
local instance windowEulerCompletionBorel (P : HeightOneSpectrum (𝓞 K)) :
    BorelSpace (P.adicCompletion K) := ⟨rfl⟩

def sourceKPFiniteWindowIntegral (f : 𝔸ᶠ[K] → ℂ)
    (T : Finset (HeightOneSpectrum (𝓞 K))) : ℂ :=
  ∫ y in sourceKPFiniteWindow K T, f y ∂sourceKPFiniteStandardHaar K

theorem sourceKPFiniteWindowIntegral_finite_product
    (S : Finset (HeightOneSpectrum (𝓞 K))) (f : 𝔸ᶠ[K] → ℂ)
    (c : HeightOneSpectrum (𝓞 K) → ℂ)
    (hstep : ∀ T P, P ∈ T → P ∉ S →
      sourceKPFiniteWindowIntegral K f T =
        c P * sourceKPFiniteWindowIntegral K f (T.erase P))
    (T : Finset (HeightOneSpectrum (𝓞 K))) :
    sourceKPFiniteWindowIntegral K f (S ∪ T) =
      (∏ P ∈ T, if P ∈ S then 1 else c P) * sourceKPFiniteWindowIntegral K f S := by
  induction T using Finset.induction_on with
  | empty => simp only [Finset.union_empty, Finset.prod_empty, one_mul]
  | @insert P T hPT ih =>
      by_cases hPS : P ∈ S
      · have he : S ∪ insert P T = S ∪ T := by
          ext Q
          simp only [Finset.mem_union, Finset.mem_insert]
          aesop
        rw [he, Finset.prod_insert hPT, ite_eq_left hPS, one_mul]
        exact ih
      · have he : (S ∪ insert P T).erase P = S ∪ T := by
          ext Q
          simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_insert]
          aesop
        rw [hstep (S ∪ insert P T) P (by simp) hPS, he, ih,
          Finset.prod_insert hPT, ite_eq_right hPS]
        exact (mul_assoc _ _ _).symm

theorem sourceKPFiniteWindowIntegral_eq_product_limit
    (S : Finset (HeightOneSpectrum (𝓞 K))) (f : 𝔸ᶠ[K] → ℂ)
    (hf : Integrable f (sourceKPFiniteStandardHaar K))
    (c : HeightOneSpectrum (𝓞 K) → ℂ) (C : ℂ)
    (hprod : HasProd (fun P => if P ∈ S then 1 else c P) C)
    (hstep : ∀ T P, P ∈ T → P ∉ S →
      sourceKPFiniteWindowIntegral K f T =
        c P * sourceKPFiniteWindowIntegral K f (T.erase P)) :
    (∫ y, f y ∂sourceKPFiniteStandardHaar K) = C * sourceKPFiniteWindowIntegral K f S := by
  have hUnion : Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 K)) => S ∪ T) atTop atTop := by
    apply tendsto_atTop.2
    intro U
    filter_upwards [eventually_ge_atTop U] with T hT
    exact hT.trans Finset.subset_union_right
  have hI := (sourceKPFiniteWindow_integral_tendsto K (sourceKPFiniteStandardHaar K) f hf).comp hUnion
  have hP : Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 K)) =>
      ∏ P ∈ T, if P ∈ S then 1 else c P) atTop (𝓝 C) := hprod
  have hC := hP.mul_const (sourceKPFiniteWindowIntegral K f S)
  have he : (fun T : Finset (HeightOneSpectrum (𝓞 K)) =>
      sourceKPFiniteWindowIntegral K f (S ∪ T)) =
      (fun T => (∏ P ∈ T, if P ∈ S then 1 else c P) * sourceKPFiniteWindowIntegral K f S) :=
    funext (sourceKPFiniteWindowIntegral_finite_product K S f c hstep)
  change Tendsto (fun T => sourceKPFiniteWindowIntegral K f (S ∪ T)) atTop
    (𝓝 (∫ y, f y ∂sourceKPFiniteStandardHaar K)) at hI
  rw [he] at hI
  exact tendsto_nhds_unique hI hC

theorem sourceKPUnramifiedScatteringFactor_hasProd_all
    (S : Finset (ProbePrime K)) {s : ℂ} (hs : 1 / 6 < s.re) :
    HasProd (fun P : ProbePrime K => if P ∈ S then 1 else sourceKPUnramifiedScatteringFactor P s)
      (sourceKPExteriorScattering S s) := by
  have h : HasProd (((↑S : Set (ProbePrime K))ᶜ).mulIndicator
      (fun P => sourceKPUnramifiedScatteringFactor P s)) (sourceKPExteriorScattering S s) :=
    hasProd_subtype_iff_mulIndicator.mp (sourceKPExteriorScattering_hasProd S hs)
  apply h.congr_fun
  intro P
  by_cases hP : P ∈ S <;> simp [Set.mulIndicator, hP]

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPFiniteIntertwiner_eq_euler_of_local_integrals
    (S : Finset (ProbePrime K)) {s : ℂ} (hs : 1 / 6 < s.re)
    (hbound : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1)
    (g : SourceKPFiniteAdeleProjective K hζ)
    (hlocal : ∀ T P, P ∈ T → P ∉ S →
      ∀ r : sourceKPFinitePlaceRemainder K P, r.val ∈ sourceKPFiniteWindow K T →
      (∫ x : P.adicCompletion K,
        sourceKPFiniteIntertwiningKernel K hζ s g (sourceKPFiniteAdditiveSingle K P x + r.val)
        ∂sourceJacquetHaar K P) =
      sourceKPUnramifiedScatteringFactor P s *
        ∫ x : P.adicCompletion K in (P.adicCompletionIntegers K : Set _),
          sourceKPFiniteIntertwiningKernel K hζ s g (sourceKPFiniteAdditiveSingle K P x + r.val)
          ∂sourceJacquetHaar K P) :
    sourceKPFiniteIntertwiner K hζ s g =
      sourceKPExteriorScattering S s *
        sourceKPFiniteWindowIntegral K (sourceKPFiniteIntertwiningKernel K hζ s g) S := by
  have hf := sourceKPFiniteIntertwiningKernel_integrable K hζ hbound g
  apply sourceKPFiniteWindowIntegral_eq_product_limit K S _ hf
    (fun P => sourceKPUnramifiedScatteringFactor P s) _
    (sourceKPUnramifiedScatteringFactor_hasProd_all K S hs)
  intro T P hPT hPS
  exact sourceKPFiniteWindow_integral_step K T P hPT _ hf _ (hlocal T P hPT hPS)

end
end ArtinMatthews

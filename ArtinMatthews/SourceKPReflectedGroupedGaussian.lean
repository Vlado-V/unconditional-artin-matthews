module

public import ArtinMatthews.SourceReflectionFiniteGaussianScaled
public import ArtinMatthews.SourceSLocalGroupedQuotientIntegral
public import ArtinMatthews.SourceSLocalQuotientSheet


set_option backward.privateInPublic true
@[expose] public section

/-! Keep the finite local tensor sum grouped in the actual pointwise
orbit. Its finite absolute sheet mass justifies flattening under the
quotient integral before applying the reflected Gaussian. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain MeasureTheory SourcePhysical SourceReflection
open scoped NumberField Classical BigOperators ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 12) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "U" => SWholeUnits K S
local notation "N" => SNormOne K S
local notation "Γ" => sNormOneSixthSubgroup K S
local notation "Q" => SNormOneSixthQuotient K S
local notation "sc" => sLocalPositiveScaling K hζ S
local notation "qmk" => sNormOneSixthQuotientMap K S

variable (v : InfinitePlace K) {δ : ℝ} {X V : Type*} [Fintype X] [Fintype V]
variable (f : Finset (SourceExteriorPrime K S₀)) (d : SourcePrimeExponents K S₀)
local notation "I" => SourceReflectionSupportedTermIndex K S₀ f d
local notation "Idx" => SourceReflectionTermIndex K S₀ f
local notation "ν" => sourceSLocalNormalizedSheetMeasure K hζ S v
local notation "μ" => sNormOneQuotientMeasure K S ν
private def groupedTermLength (i : Idx) : ℝ :=
  sourceReflectionTermLength K S₀ i.1.val i.2.1 i.2.2.val

local notation "L" => groupedTermLength K S₀ f
local notation "w" => fun (_ : Idx) (_ : U) => (1 : ℂ)

theorem sourceReflectionGroupedGaussian_of_hasSum
    (D : V → SourceThetaRotatedTensor K (sourceHilbertSet K S₀) hζ v δ)
    (C₀ A₀ : ℝ) (r : ℕ) (hδ : 0 ≤ δ) {σ : ℝ} (hσ : 1/2 < σ)
    (a : X → V → Idx → ℂ) {M : ℝ} (hM : 0 < M)
    (ha : ∀ x l i, ‖a x l i‖ ≤ M * sourceReflectionDirichletTerm K S₀ f 0 i)
    (u : X → ℝ → Idx → U)
    (hu : ∀ x t, 0 < t → ∀ i, sLocalNorm K S (u x t i) = L i * t)
    (G : U → ℂ) (hG : sourceSLocalSixthInvariant S G)
    (hs : ∀ t, 0 < t → ∀ n : N, HasSum (fun p : (I × X) × Γ =>
      ∑ l : V, sourceReflectionRotatedTerm K S₀ hζ v D f (fun _ => l) (a p.1.2 l) w
        p.1.1.val (((n * p.2.val : N) : U) * u p.1.2 t p.1.1.val))
      (G ((n : U)*sc t)))
    {R : ℝ} (hR : 0 < R) :
    sourceThetaGaussianProfile C₀ A₀ r (-1) (sourceSLocalQuotientSheetProfile S hζ ν G hG) R =
      ∑' i : I × (X × V), a i.2.1 i.2.2 i.1.val *
        sourceThetaGaussianProfile C₀ A₀ r (-1)
          ((D i.2.2).weightedSheet 0 (fun _ => 1)) (L i.1.val * R) := by
  let : Countable Idx := sourceReflectionTermIndex_countable K S₀ f
  let : Measure.IsHaarMeasure ν := sourceSLocalNormalizedSheetMeasure_isHaar K hζ S v
  let term (i : I × X) (l : V) :=
    sourceReflectionRotatedTerm K S₀ hζ v D f (fun _ => l) (a i.2 l) w i.1.val
  let U₁ (t : ℝ) (i : I × X) := u i.2 t i.1.val
  let j (x : X × V) (_ : Idx) := x.2
  let A (x : X × V) := a x.1 x.2
  let W (_ : X × V) := w
  let U₂ (x : X × V) := u x.1
  let e : (I × X) × V ≃ I × (X × V) := Equiv.prodAssoc I X V
  have hmass t ht := sourceReflectionRotatedOrbit_supportedFiniteMass_scaled
    K S₀ hζ v D f d hδ hσ j A hM (fun x => ha x.1 x.2) W
    (fun _ _ _ => norm_one.le) U₂ (fun x => hu x.1) t ht
  let H (t : ℝ) := ∫ q, ∑' i : I × (X × V),
    sourceSLocalTensorOrbit S
      (sourceReflectionRotatedTerm K S₀ hζ v D f (j i.2) (A i.2) (W i.2) i.1.val)
      (U₂ i.2 t i.1.val) q ∂μ
  have hsheet t (ht : 0 < t) : sourceSLocalQuotientSheetProfile S hζ ν G hG t = H t := by
    have hmeas (i : I × X) (l : V) : Measurable (fun n : N => term i l ((n : U)*U₁ t i)) :=
      sourceReflectionRotatedTerm_scaled_measurable K S₀ hζ v D f (fun _ => l) (a i.2 l)
        w (fun _ => measurable_const) i.1.val (U₁ t i)
    have hmass' : (∑' p : (I × X) × V,
        ∫⁻ n : N, ‖term p.1 p.2 ((n : U)*U₁ t p.1)‖ₑ ∂ν) < ⊤ := by
      let F (p : I × (X × V)) :=
        ∫⁻ n : N, ‖term (p.1,p.2.1) p.2.2 ((n : U)*U₁ t (p.1,p.2.1))‖ₑ ∂ν
      calc
        _ = ∑' p, F p := e.tsum_eq F
        _ < ⊤ := hmass t ht
    have hpoint (n : N) : HasSum (fun p : (I × X) × Γ =>
        ∑ l : V, term p.1 l (((n * p.2.val : N) : U) * U₁ t p.1))
        (sourceSLocalQuotientSheetFunction S hζ G hG t (qmk n)) :=
      hs t ht n
    have he := (sourceSLocalGroupedOrbit_quotient_integral_eq_flattened S ν term (U₁ t)
      (sourceSLocalQuotientSheetFunction S hζ G hG t) hpoint hmeas hmass').2
    unfold sourceSLocalQuotientSheetProfile
    rw [he]
    apply integral_congr_ae
    filter_upwards with q
    exact e.tsum_eq (fun p : I × (X × V) =>
      sourceSLocalTensorOrbit S (term (p.1,p.2.1) p.2.2) (U₁ t (p.1,p.2.1)) q)
  have hGaussian : sourceThetaGaussianProfile C₀ A₀ r (-1)
      (sourceSLocalQuotientSheetProfile S hζ ν G hG) R = sourceThetaGaussianProfile C₀ A₀ r (-1) H R := by
    unfold sourceThetaGaussianProfile mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have hp : 0 < R * t ^ (-1 : ℝ) := mul_pos hR (Real.rpow_pos_of_pos ht _)
    dsimp only
    rw [hsheet _ hp]
  rw [hGaussian]
  exact sourceReflectionRotatedOrbit_supportedFiniteGaussian_scaled K S₀ hζ v D f d C₀ A₀ r
    hδ hσ j A hM (fun x => ha x.1 x.2) W (fun _ _ => measurable_const)
    (fun _ _ _ => norm_one.le) U₂ (fun x => hu x.1) hR

end
end ArtinMatthews.SourceEulerAssembly

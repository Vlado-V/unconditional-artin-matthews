module

public import ArtinMatthews.SourceSLocalAdditiveProbeBinding


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain
open MeasureTheory Set StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

omit [IsTotallyComplex K] in
theorem sourceSLocalCompletionCharacter_continuous :
    Continuous (sourceSLocalCompletionCharacter K S) := by
  change Continuous (fun x : SLocalAdditiveCompletionSpace K S =>
    archCharacter K x.1 * ∏ p : S, localFiniteCharacter K p.val (x.2 p))
  refine ((archCharacter_continuous K).comp continuous_fst).mul
    (continuous_finsetProd _ fun p _ => ?_)
  exact (localFiniteCharacter_continuous K p.val).comp ((continuous_apply p).comp continuous_snd)

theorem sourceSLocalCompletionProbe_continuous : Continuous (sourceSLocalCompletionProbe K S) := by
  let e := sourceSLocalCompletionHomeomorph K S
  let f := sourceSLocalAdditiveProbe K S
  have he : Continuous (e : SLocalAdditiveCompletionSpace K S → SLocalAdditiveSpace K S) :=
    e.continuous
  have h : Continuous (f ∘ e) := (sourceSLocalAdditiveProbe_continuous K S).comp he
  have hEq : sourceSLocalCompletionProbe K S = f ∘ e :=
    funext (sourceSLocalCompletionProbe_eq_coordinate K S)
  exact hEq.symm ▸ h

theorem sourceSLocalCompletionProbe_zero :
    sourceSLocalCompletionProbe K S 0 = 0 := by
  by_contra h
  have hmem : (0 : SLocalAdditiveCompletionSpace K S) ∈ tsupport (sourceSLocalCompletionProbe K S) :=
    subset_tsupport _ h
  exact (sourceSLocalCompletionProbe_support_away_zero K S hmem).1 (Classical.arbitrary _) rfl

theorem sourceSLocalCompletionProbe_integral_zero :
    (∫ x, sourceSLocalCompletionProbe K S x ∂sourceSLocalCompletionMeasure K S) = 0 := by
  have h : sourceSLocalCompletionCharacter K S 0 = 1 := by
    rw [sourceSLocalCompletionCharacter_eq_coordinate, map_zero, AddChar.map_zero_eq_one]
  simpa only [sourceSLocalCompletionFourier, mul_zero, neg_zero, h, one_mul]
    using sourceSLocalCompletionProbe_fourier_zero K S

/-- The Bochner Fourier integral is absolutely integrable at every additive frequency. -/
theorem sourceSLocalCompletionProbe_fourierKernel_integrable
    (y : SLocalAdditiveCompletionSpace K S) :
    Integrable (fun x => sourceSLocalCompletionCharacter K S (-(x * y)) *
      sourceSLocalCompletionProbe K S x) (sourceSLocalCompletionMeasure K S) := by
  let (w : InfinitePlace K) : SecondCountableTopology w.Completion :=
    (isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).toHomeomorph.isEmbedding.secondCountableTopology
  have hm : Continuous (fun x => sourceSLocalCompletionCharacter K S (-(x * y)) *
      sourceSLocalCompletionProbe K S x) :=
    ((sourceSLocalCompletionCharacter_continuous K S).comp
      (continuous_id.mul continuous_const).neg).mul (sourceSLocalCompletionProbe_continuous K S)
  apply (sourceSLocalCompletionProbe_integrable K S).mono hm.measurable.aestronglyMeasurable
  filter_upwards with x
  change ‖sourceSLocalCompletionCharacter K S (-(x * y)) * sourceSLocalCompletionProbe K S x‖ ≤ _
  have hPhase : ‖sourceSLocalCompletionCharacter K S (-(x * y))‖ = 1 :=
    (congrArg norm (sourceSLocalCompletionCharacter_eq_coordinate K S (-(x * y)))).trans
      (sourceSLocalAdditiveCharacter_unitary K S _)
  rw [norm_mul, hPhase, one_mul]

theorem sourceSLocalCompletionProbe_fourier_tsupport_finite
    {y : SLocalAdditiveCompletionSpace K S}
    (hy : y ∈ tsupport (sourceSLocalCompletionFourier K S (sourceSLocalCompletionProbe K S)))
    (p : S) : y.2 p ∈ sourceLocalBall K p.val ((sourceDifferentExponent K p.val : ℤ) + 1) := by
  let B := sourceLocalBall K p.val ((sourceDifferentExponent K p.val : ℤ) + 1)
  let e : SLocalAdditiveCompletionSpace K S → p.val.adicCompletion K := fun x => x.2 p
  have hc : Continuous e := (continuous_apply p).comp continuous_snd
  have hs : Function.support (sourceSLocalCompletionFourier K S (sourceSLocalCompletionProbe K S)) ⊆
      e ⁻¹' B := by
    intro x hx
    by_contra hn
    have hp : sourceLocalFourier K p.val (sourceLocalUnitTest K p.val) (x.2 p) = 0 :=
      sourceLocalUnitTestFourier_eq_zero_outside K p.val (x.2 p) hn
    apply hx
    rw [sourceSLocalCompletionProbe_fourier_factors,
      Finset.prod_eq_zero (Finset.mem_univ p) hp, mul_zero]
  exact closure_minimal hs ((sourceLocalBall_isCompact K p.val _).isClosed.preimage hc) hy

end
end ArtinMatthews.SourcePhysical

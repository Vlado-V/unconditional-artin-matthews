module

public import ArtinMatthews.SourceSLocalAdditiveCompletion
public import ArtinMatthews.SourceSLocalProbeMellin


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain
open ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField Classical BigOperators SchwartzMap
noncomputable section

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "CPlaces" => {v : InfinitePlace K // IsComplex v}

/-- The actual full additive Fourier integral with all places and constants retained. -/
theorem sourceSLocalCompletionProbe_fourier_factors (y : SLocalAdditiveCompletionSpace K S) :
    sourceSLocalCompletionFourier K S (sourceSLocalCompletionProbe K S) y =
      (∏ w : InfinitePlace K, sourceProbeArchFourier
        (ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w) (y.1 w))) *
        ∏ p : S, sourceLocalFourier K p.val (sourceLocalUnitTest K p.val) (y.2 p) := by
  rw [sourceSLocalCompletionProbe_fourier_eq_coordinate, sourceSLocalAdditiveProbe_fourier_tensor]
  simp_rw [← sourceProbeArchFourier_apply]
  let e : InfinitePlace K ≃ CPlaces :=
    ⟨fun w => ⟨w, IsTotallyComplex.isComplex w⟩, Subtype.val, fun _ => rfl, fun _ => rfl⟩
  have h := e.prod_comp (fun w : CPlaces => sourceProbeArchFourier
    (ringEquivComplexOfIsComplex w.property (y.1 w.val)))
  exact congrArg (fun a : ℂ => a *
    ∏ p : S, sourceLocalFourier K p.val (sourceLocalUnitTest K p.val) (y.2 p)) h.symm

/-- Forget only the units wrappers, keeping all the literal additive coordinates. -/
def sourceSLocalUnitAdditivePoint (x : SWholeUnits K S) : SLocalAdditiveCompletionSpace K S :=
  (fun w => (x.1 w : w.Completion), fun p => (x.2 p : p.val.adicCompletion K))

omit [IsTotallyComplex K] in
theorem sourceSLocalUnitAdditivePoint_mul (x y : SWholeUnits K S) :
    sourceSLocalUnitAdditivePoint K S (x * y) =
      sourceSLocalUnitAdditivePoint K S x * sourceSLocalUnitAdditivePoint K S y := rfl

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

/-- On the S-local units the additive Fourier integral is exactly the named probe factors. -/
theorem sourceSLocalCompletionProbe_fourier_units (x : SWholeUnits K S) :
    sourceSLocalCompletionFourier K S (sourceSLocalCompletionProbe K S)
        (sourceSLocalUnitAdditivePoint K S x) =
      (∏ w : InfinitePlace K, sourceProbeArchFactor K hζ w (x.1 w)) *
        ∏ p : S, sourceProbeFiniteFactor K S p (x.2 p) := by
  rw [sourceSLocalCompletionProbe_fourier_factors]
  rfl

/-- Splitting off the chosen place recovers the literal multiplicative Mellin input. -/
theorem sourceSLocalCompletionProbe_fourier_eq_probeTensor (v : InfinitePlace K)
    (x : SWholeUnits K S) :
    sourceSLocalCompletionFourier K S (sourceSLocalCompletionProbe K S)
        (sourceSLocalUnitAdditivePoint K S x) =
      sourceSLocalProbeFourierTensor K hζ S v x := by
  rw [sourceSLocalCompletionProbe_fourier_units]
  change (∏ w : InfinitePlace K, sourceProbeArchFactor K hζ w (x.1 w)) *
      (∏ p : S, sourceProbeFiniteFactor K S p (x.2 p)) =
    sourceProbeArchFactor K hζ v (x.1 v) *
      ((∏ w : {w : InfinitePlace K // w ≠ v}, sourceProbeArchFactor K hζ w.val (x.1 w.val)) *
        (∏ p : S, sourceProbeFiniteFactor K S p (x.2 p)))
  rw [Fintype.prod_eq_mul_prod_subtype_ne (fun w : InfinitePlace K =>
    sourceProbeArchFactor K hζ w (x.1 w)) v, mul_assoc]

theorem sourceSLocalAdditiveProbe_fourier_eq_probeTensor (v : InfinitePlace K)
    (x : SWholeUnits K S) :
    sourceSLocalAdditiveFourier K S (sourceSLocalAdditiveProbe K S)
      (sourceSLocalCompletionRingEquiv K S (sourceSLocalUnitAdditivePoint K S x)) =
        sourceSLocalProbeFourierTensor K hζ S v x :=
  (sourceSLocalCompletionProbe_fourier_eq_coordinate K S _).symm.trans
    (sourceSLocalCompletionProbe_fourier_eq_probeTensor K S hζ v x)

end
end ArtinMatthews.SourcePhysical

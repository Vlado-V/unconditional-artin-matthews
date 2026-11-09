module

public import ArtinMatthews.SourcePoissonActualQuotientUnfold
public import ArtinMatthews.SourceFrequencyPoissonArgument
public import ArtinMatthews.SourceSLocalAdditiveProbeBinding


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators MeasureTheory
open VaryingKummerAnalytic QuadraticWeil SourcePhysical
open scoped NumberField Classical ENNReal BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "S" => sourceHilbertSet F S₀
local notation "I" => SourcePoissonPhysicalOrbitIndex F S₀
local notation "U" => sourceFrequencyRepresentative F hζ S₀

def sourcePoissonActualOrbitArgument (X : ℝ) (p : I) : SWholeUnits F S :=
  let a := p.2
  sourceFrequencyPoissonArgument F hζ S₀ X a.2.2.1 (a.1.val + 3 • a.2.1) p.1 a.2.2.2

theorem sourcePoissonActualOrbitArgument_norm {X : ℝ} (hX : 0 < X) (p : I) :
    sLocalNorm F S (sourcePoissonActualOrbitArgument F S₀ hζ X p) =
      sourcePoissonOrbitScale F S₀ X (U p.1) p.2 := by
  unfold sourcePoissonActualOrbitArgument
  dsimp only
  rw [sourceFrequencyPoissonArgument_norm F hζ S₀ X hX, sourcePoissonOrbitScale,
    sourcePoissonActualFrequencyNorm_eq, sourcePrimeExponentNorm_squarefree_cube,
    Nat.cast_mul, Nat.cast_pow]

variable [IsTotallyComplex F] (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J) (v : InfinitePlace F)
local notation "Γ" => sNormOneSixthSubgroup F S
local notation "D" => sNormOneFundamentalSet F S
local notation "ν" => sourceSLocalNormalizedSheetMeasure F hζ S v
local notation "μ" => sourceSLocalProbeQuotientMeasure F hζ S v
local notation "Q" => SNormOneSixthQuotient F S
local notation "amp" => sourcePoissonOrbitAmplitude F S₀ hζ hS η
local notation "FourierW₀" => sourceSLocalCompletionFourier F S (sourceSLocalCompletionProbe F S)

def sourcePoissonLiteralQuotientSeries (X Y Z : ℝ) : Q → ℂ :=
  sourcePoissonActualQuotientSeries F S₀ hζ hS η v X Y Z (sourcePoissonActualOrbitArgument F S₀ hζ X)

/-- The actual quotient integral uses the literal physical Fourier arguments. -/
theorem sourcePoissonLiteralQuotient_unfold {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    Integrable (sourcePoissonLiteralQuotientSeries F S₀ hζ hS η v X Y Z) μ ∧
      (∫ t, sourcePoissonLiteralQuotientSeries F S₀ hζ hS η v X Y Z t ∂μ) =
        sourcePoissonActualOrbitSeries F S₀ hζ hS η v X Y Z :=
  sourcePoissonActualQuotient_unfold F S₀ hζ hS η v hX hY hZ (sourcePoissonActualOrbitArgument F S₀ hζ X)
    (sourcePoissonActualOrbitArgument_norm F S₀ hζ hX)

/-- The joint dual series on norm-one representatives, with the actual additive transform. -/
def sourcePoissonLiteralFourierSeries (X Y Z : ℝ) (x : SNormOne F S) : ℂ :=
  ∑' p : I × Γ, amp X Y Z (U p.1.1) p.1.2 *
    FourierW₀ (sourceSLocalUnitAdditivePoint F S
      ((x : SWholeUnits F S) * p.2.val.val * sourcePoissonActualOrbitArgument F S₀ hζ X p.1))

theorem sourcePoissonLiteralFourierSeries_eq_translates (X Y Z : ℝ) (x : SNormOne F S) :
    sourcePoissonLiteralFourierSeries F S₀ hζ hS η X Y Z x =
      ∑' p : I × Γ, amp X Y Z (U p.1.1) p.1.2 *
        sourceSLocalProbeOrbitTranslate F hζ S v (sourcePoissonActualOrbitArgument F S₀ hζ X p.1) p.2 x := by
  unfold sourcePoissonLiteralFourierSeries
  apply tsum_congr
  intro p
  rw [sourceSLocalCompletionProbe_fourier_eq_probeTensor F S hζ v,
    sourceSLocalProbeOrbitTranslate_value]

theorem sourcePoissonLiteralFourierSeries_ae_summable {X Y Z : ℝ}
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    ∀ᵐ x : SNormOne F S ∂(ν).restrict D, Summable (fun p : I × Γ => ‖amp X Y Z (U p.1.1) p.1.2 *
      FourierW₀ (sourceSLocalUnitAdditivePoint F S
        ((x : SWholeUnits F S) * p.2.val.val * sourcePoissonActualOrbitArgument F S₀ hζ X p.1))‖) := by
  filter_upwards [sourcePoissonActualQuotient_ae_summable F S₀ hζ hS η v hX hY hZ (sourcePoissonActualOrbitArgument F S₀ hζ X)
    (sourcePoissonActualOrbitArgument_norm F S₀ hζ hX)] with x hx
  refine hx.congr fun p => ?_
  rw [sourceSLocalCompletionProbe_fourier_eq_probeTensor F S hζ v,
    sourceSLocalProbeOrbitTranslate_value]

theorem sourcePoissonLiteralFourierSeries_ae_quotient {X Y Z : ℝ}
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    ∀ᵐ x : SNormOne F S ∂(ν).restrict D,
      sourcePoissonLiteralQuotientSeries F S₀ hζ hS η v X Y Z (sNormOneSixthQuotientMap F S x) =
        sourcePoissonLiteralFourierSeries F S₀ hζ hS η X Y Z x := by
  filter_upwards [sourcePoissonActualQuotient_ae_mk F S₀ hζ hS η v hX hY hZ (sourcePoissonActualOrbitArgument F S₀ hζ X)
    (sourcePoissonActualOrbitArgument_norm F S₀ hζ hX)] with x hx
  exact hx.trans (sourcePoissonLiteralFourierSeries_eq_translates F S₀ hζ hS η v X Y Z x).symm

/-- The literal dual series integrates to the already constructed physical orbit sum. -/
theorem sourcePoissonLiteralFundamentalIntegral {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    Integrable (sourcePoissonLiteralFourierSeries F S₀ hζ hS η X Y Z) ((ν).restrict D) ∧
      (∫ x in D, sourcePoissonLiteralFourierSeries F S₀ hζ hS η X Y Z x ∂ν) =
        sourcePoissonActualOrbitSeries F S₀ hζ hS η v X Y Z := by
  have h := sourcePoissonActualQuotient_fundamentalIntegral F S₀ hζ hS η v hX hY hZ (sourcePoissonActualOrbitArgument F S₀ hζ X)
    (sourcePoissonActualOrbitArgument_norm F S₀ hζ hX)
  have he := sourcePoissonLiteralFourierSeries_eq_translates F S₀ hζ hS η v X Y Z
  exact ⟨h.1.congr (Filter.Eventually.of_forall fun x => (he x).symm),
    (integral_congr_ae (Filter.Eventually.of_forall he)).trans h.2⟩

end
end ArtinMatthews.SourceEulerAssembly

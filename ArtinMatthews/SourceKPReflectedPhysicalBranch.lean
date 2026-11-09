module

public import ArtinMatthews.SourceKPPhysicalBranch
public import ArtinMatthews.SourceSLocalReflectionScale


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite branch rotates on the true norm-one quotient,
with the original Gaussian Mellin normalization and denominator. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain QuadraticWeil VaryingKummerAnalytic
open SourcePhysical SourceReflection SourceEulerAssembly
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 12) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "Whole" => SWholeUnits K S
local notation "E" => SourcePrimeExponents K S₀
local notation "PE" => SourceExteriorPrime K S₀
local notation "gen" => sourcePrimeExponentUnit K hζ S₀
local notation "angle" => sourceKPOrientedHorizontal K hζ
local notation "bessel" => (fun _ : InfinitePlace K => 4*Real.pi)
local notation "rep" => sourceExteriorUnitSixthRepresentative S
local notation "Weight" => sourceKPPhysicalRowWeight K hζ S₀
local notation "Mask" => sourceKPPositivePhysicalActiveMask K S₀
local notation "arg" => sourceKPSLocalReflectionArgument K S
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "ω" => fun b => sourceKPReflectionProductPhase K hζ b angle (sourceKPAllInfinitePlaces K)

attribute [local instance] positiveTwistLabelFintype
variable {J : Ideal (𝓞 K)}

def sourceKPReflectedPhysicalBranchValue
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    {T : ℝ} (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (e : E) (u : ExteriorUnitSixthClasses S) (active : Finset PE) (b : Kˣ) (x : Whole) : ℂ :=
  let q₀ := sourceKPPositiveSeedData_q₀ K hζ S₀ p
  let t := one_le_two.trans hT.le
  Weight hS η hJ (rep u) (arg b*x⁻¹) * (sourceKPCuspResidualFourierValue K hζ 1 t q₀)⁻¹ *
    sourceKPReflectedResidualFiniteValue K hζ S b angle t
      (sourceKPPositivePhysicalTranslate K hζ S₀ e p.R p.M q₀)
      (sourceKPPositivePhysicalTranslateWeight K hζ S₀ e p.R p.M (Mask e active)) x

theorem sourceKPReflectedPhysicalBranchValue_hasSum
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    {T : ℝ} (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (e : E) (u : ExteriorUnitSixthClasses S) (active : Finset PE) (b : Kˣ) (x : Whole) :
    let q₀ := sourceKPPositiveSeedData_q₀ K hζ S₀ p
    let t := one_le_two.trans hT.le
    let t₀ := sourceKPPositivePhysicalTranslate K hζ S₀ e p.R p.M q₀
    let a := sourceKPPositivePhysicalTranslateWeight K hζ S₀ e p.R p.M (Mask e active)
    HasSum (fun m : Kˣ =>
      (Weight hS η hJ (rep u) (arg b*x⁻¹) * (sourceKPCuspResidualFourierValue K hζ 1 t q₀)⁻¹) *
        ∑ i : SourceReflectionPositiveTwistLabels K S₀ e × SourceKPRetainedSeedIndex K S p.R p.M,
          a i * sourceKPPhysicalResidualBesselTerm K hζ S (fun v => !(angle v)) t
            (sourceKPReflectedHorizontalFiber K hζ S b (t₀ i) x) m x)
      (sourceKPReflectedPhysicalBranchValue K hζ S₀ hS η hJ hT p e u active b x) := by
  dsimp only
  apply HasSum.mul_left
  exact sourceKPReflectedResidualFiniteValue_hasSum K hζ S b angle _ _ _ x

theorem sourceKPPositivePhysicalBranchValue_reflection
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    {T : ℝ} (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (e : E) (u : ExteriorUnitSixthClasses S) (active : Finset PE) (b : Kˣ) (x : Whole) :
    sourceKPPositivePhysicalBranchValue K hζ S₀ hS η hJ hT p e u active x =
      ω b * sourceKPReflectedPhysicalBranchValue K hζ S₀ hS η hJ hT p e u active b (arg b*x⁻¹) := by
  have hω : ω b ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [sourceKPReflectionProductPhase_norm]
    exact one_ne_zero
  unfold sourceKPPositivePhysicalBranchValue sourceKPPositivePhysicalFiniteValue
    sourceKPReflectedPhysicalBranchValue sourceKPReflectedResidualFiniteValue
  dsimp only
  rw [sourceKPSLocalReflectionArgument_involution K S b x]
  field_simp [hω]

theorem sourceKPReflectedPhysicalBranchValue_invariant
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (hcut : principalAngularCutoff K J ⊆ S)
    {T : ℝ} (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (e : E) (u : ExteriorUnitSixthClasses S) (active : Finset PE) (b : Kˣ) :
    sourceSLocalSixthInvariant S (sourceKPReflectedPhysicalBranchValue K hζ S₀ hS η hJ hT p e u active b) := by
  have hω : ω b ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [sourceKPReflectionProductPhase_norm]
    exact one_ne_zero
  exact sourceSLocalSixthInvariant_of_signed_reflection S
    (sourceKPPositivePhysicalBranchValue K hζ S₀ hS η hJ hT p e u active) _ (arg b) (ω b) hω
    (sourceKPPositivePhysicalBranchValue_invariant K hζ S₀ hS η hJ hcut hT p e u active)
    (sourceKPPositivePhysicalBranchValue_reflection K hζ S₀ hS η hJ hT p e u active b)

theorem sourceKPPhysicalBranch_gaussian_reflection
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (hcut : principalAngularCutoff K J ⊆ S) (v : InfinitePlace K)
    {T : ℝ} (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (e : E) (u : ExteriorUnitSixthClasses S) (f : Finset PE) (d : E) {Z : ℝ} (hZ : 0 < Z) :
    let active := f ∪ d.support
    let b := gen (sourceReflectionActiveExponents K S₀ f+d)
    let F := sourceKPPositivePhysicalBranchValue K hζ S₀ hS η hJ hT p e u active
    let G := sourceKPReflectedPhysicalBranchValue K hζ S₀ hS η hJ hT p e u active b
    let hF := sourceKPPositivePhysicalBranchValue_invariant K hζ S₀ hS η hJ hcut hT p e u active
    let hG := sourceKPReflectedPhysicalBranchValue_invariant K hζ S₀ hS η hJ hcut hT p e u active b
    let ν := sourceSLocalNormalizedSheetMeasure K hζ S v
    let C₀ := sourceThetaMellinConstant K S bessel p.cutoff
    let A₀ := sourceThetaMellinScale K bessel
    let r := Fintype.card (InfinitePlace K)
    sourceThetaGaussianProfile C₀ A₀ r 1 (sourceSLocalQuotientSheetProfile S hζ ν F hF) (1/Z) =
      ω b * sourceThetaGaussianProfile C₀ A₀ r (-1) (sourceSLocalQuotientSheetProfile S hζ ν G hG)
        (sourceReflectionTermScale K S₀ Z f d)⁻¹ := by
  let active := f ∪ d.support
  let b := gen (sourceReflectionActiveExponents K S₀ f+d)
  let F := sourceKPPositivePhysicalBranchValue K hζ S₀ hS η hJ hT p e u active
  let G := sourceKPReflectedPhysicalBranchValue K hζ S₀ hS η hJ hT p e u active b
  let hF := sourceKPPositivePhysicalBranchValue_invariant K hζ S₀ hS η hJ hcut hT p e u active
  let hG := sourceKPReflectedPhysicalBranchValue_invariant K hζ S₀ hS η hJ hcut hT p e u active b
  let ν := sourceSLocalNormalizedSheetMeasure K hζ S v
  let C₀ := sourceThetaMellinConstant K S bessel p.cutoff
  let A₀ := sourceThetaMellinScale K bessel
  let r := Fintype.card (InfinitePlace K)
  let : MeasureTheory.Measure.IsHaarMeasure ν := sourceSLocalNormalizedSheetMeasure_isHaar K hζ S v
  have he (x : Whole) : F x = ω b * G (arg b*x⁻¹) :=
    sourceKPPositivePhysicalBranchValue_reflection K hζ S₀ hS η hJ hT p e u active b x
  have h := sourceSLocalQuotientGaussian_reflection S hζ ν F G hF hG (arg b) (ω b)
    he C₀ A₀ r (inv_pos.mpr hZ)
  have hscale : sLocalNorm K S (arg b) / Z⁻¹ = (sourceReflectionTermScale K S₀ Z f d)⁻¹ :=
    sourceSLocalReflectionTermScale_inv K hζ S₀ Z f d
  rw [hscale] at h
  simpa only [one_div] using h

end
end ArtinMatthews

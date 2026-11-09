module

public import ArtinMatthews.SourceKPPhysicalBranchSum
public import ArtinMatthews.SourceKPPositivePhysicalBranchQuotient


set_option backward.privateInPublic true
@[expose] public section

/-! The Gaussian of the genuine positive coefficient row splits over
the same finite branches used by the signed physical reflection. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain QuadraticWeil MeasureTheory
open VaryingKummerAnalytic SourcePhysical SourceReflection AllowedGenerators SourceEulerAssembly
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 12) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "PE" => SourceExteriorPrime K S₀
local notation "bessel" => (fun _ : InfinitePlace K => 4 * Real.pi)

variable {J : Ideal (𝓞 K)}
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (hcut : principalAngularCutoff K J ⊆ sourceHilbertSet K S₀) (v : InfinitePlace K)
    {T : ℝ} (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)

include hS hJ hcut hT

local notation "ν" => sourceSLocalNormalizedSheetMeasure K hζ S v
local notation "μ" => sNormOneQuotientMeasure K S ν
local notation "B[" e "," u "," g "]" =>
  sourceKPPositivePhysicalBranchValue K hζ S₀ hS η hJ hT p e u g
local notation "hB[" e "," u "," g "]" =>
  sourceKPPositivePhysicalBranchValue_invariant K hζ S₀ hS η hJ hcut hT p e u g
local notation "Q[" e "," u "," g "]" =>
  sourceSLocalQuotientSheetFunction S hζ B[e,u,g] hB[e,u,g]
local notation "P[" e "," u "," g "]" =>
  sourceSLocalQuotientSheetProfile S hζ ν B[e,u,g] hB[e,u,g]
local notation "F[" e "," u "]" => sourceKPPositivePhysicalRowValue K hζ S₀ hS η hJ hT p e u
local notation "C₀" => sourceThetaMellinConstant K S bessel p.cutoff
local notation "A₀" => sourceThetaMellinScale K bessel
local notation "r" => Fintype.card (InfinitePlace K)
local notation "Klog" => sourceThetaGaussianLogKernel C₀ A₀ r

/-- The literal forward Gaussian at the reciprocal source scale. -/
def sourceKPPositivePhysicalBranchGaussian (Z : ℝ) (e : E) (u : ExteriorUnitSixthClasses S)
    (g : Finset PE) : ℂ :=
  sourceThetaGaussianProfile C₀ A₀ r 1 P[e,u,g] (1 / Z)

private theorem positivePhysicalRow_profile_sum
    (e : E) (u : ExteriorUnitSixthClasses S) (hF : sourceSLocalSixthInvariant S F[e,u])
    {t : ℝ} (ht : 0 < t) :
    sourceSLocalQuotientSheetProfile S hζ ν F[e,u] hF t =
      ∑ g ∈ e.support.powerset, P[e,u,g] t := by
  unfold sourceSLocalQuotientSheetProfile
  calc
    _ = ∫ q, (∑ g ∈ e.support.powerset, Q[e,u,g] t q) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun q => by
        obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
        let qn := sNormOneSixthQuotientMap K S n
        change sourceSLocalQuotientSheetFunction S hζ F[e,u] hF t qn =
          ∑ g ∈ e.support.powerset, Q[e,u,g] t qn
        simp only [qn, sourceSLocalQuotientSheetFunction_mk]
        exact sourceKPPositivePhysicalRowValue_sum_branches K hζ S₀ hS η hJ hT p e u _
    _ = _ := integral_finsetSum _ (fun g _ =>
      (sourceKPPositivePhysicalBranch_quotient K hζ S₀ hS η hJ hcut v hT p e u g ht).1)

theorem sourceKPPositivePhysicalBranchGaussian_sum {Z : ℝ} (hZ : 0 < Z)
    (e : E) (u : ExteriorUnitSixthClasses S) :
    reflectionCoefficientRow K hζ S₀ hS η (sourceReflectionCanonicalRow K S₀ hζ e u) Z =
      ∑ g ∈ e.support.powerset, sourceKPPositivePhysicalBranchGaussian K hζ S₀ hS η hJ hcut v hT p Z e u g := by
  obtain ⟨hF,h⟩ := sourceKPPositivePhysicalRow_gaussian K hζ S₀ hS η hJ hcut v hT p e u
  rw [← h Z hZ, sourceThetaGaussianSmoothing, ← sourceThetaGaussianProfile_forward C₀ A₀ r
    (sourceSLocalQuotientSheetProfile S hζ ν F[e,u] hF) (1 / Z)]
  let x := Real.log (1 / Z)
  have hx : Real.exp x = 1 / Z := Real.exp_log (one_div_pos.mpr hZ)
  unfold sourceKPPositivePhysicalBranchGaussian
  rw [← hx]
  simp only [sourceThetaGaussianProfile_exp, sourceThetaGaussianLogSmooth]
  calc
    _ = ∫ y : ℝ, ∑ g ∈ e.support.powerset, Klog y * P[e,u,g] (Real.exp (x + 1 * y)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        change Klog y * sourceSLocalQuotientSheetProfile S hζ ν F[e,u] hF (Real.exp (x + 1 * y)) =
          ∑ g ∈ e.support.powerset, Klog y * P[e,u,g] (Real.exp (x + 1 * y))
        rw [positivePhysicalRow_profile_sum K hζ S₀ hS η hJ hcut v hT p e u hF
          (Real.exp_pos (x + 1 * y)), Finset.mul_sum]
    _ = _ := integral_finsetSum _ (fun g _ =>
      sourceKPPositivePhysicalBranch_log_integrable K hζ S₀ hS η hJ hcut v hT p e u g x)

theorem sourceKPPositivePhysicalBranchGaussian_eq_zero (Z : ℝ)
    (e : E) (u : ExteriorUnitSixthClasses S) (g : Finset PE)
    (hg : g ∈ e.support.powerset) (hbad : g ∉ sourceReflectionActiveChoices K S₀ e) :
    sourceKPPositivePhysicalBranchGaussian K hζ S₀ hS η hJ hcut v hT p Z e u g = 0 := by
  have hz (t : ℝ) : P[e,u,g] t = 0 := by
    unfold sourceSLocalQuotientSheetProfile
    calc
      _ = ∫ _q : SNormOneSixthQuotient K S, (0 : ℂ) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun q => by
          obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
          change Q[e,u,g] t (sNormOneSixthQuotientMap K S n) = 0
          rw [sourceSLocalQuotientSheetFunction_mk]
          exact sourceKPPositivePhysicalBranchValue_eq_zero K hζ S₀ hS η hJ hcut hT p e u g hg hbad _
      _ = 0 := integral_zero _ _
  unfold sourceKPPositivePhysicalBranchGaussian sourceThetaGaussianProfile mellin
  simp only [hz, mul_zero, smul_zero, integral_zero]

end
end ArtinMatthews

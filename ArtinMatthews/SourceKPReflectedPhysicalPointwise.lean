module

public import ArtinMatthews.SourceKPReflectedPhysicalSupport
public import ArtinMatthews.SourceKPReflectedC1PhaseTransport
public import ArtinMatthews.SourceKPAdelicOutgoingRetainedDiagonalSubstitution


set_option backward.privateInPublic true
@[expose] public section

/-! Join the actual signed finite coefficient to the retained tensor at
the original reflected numerator. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain QuadraticWeil VaryingKummerAnalytic
open SourcePhysical SourceReflection SourceEulerAssembly AllowedGenerators
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] {ζ : K}
variable (hζ : IsPrimitiveRoot ζ 12) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

local notation "S" => sourceHilbertSet K S₀
local notation "Whole" => SWholeUnits K S
local notation "E" => SourcePrimeExponents K S₀
local notation "Pr" => SourceExteriorPrime K S₀
local notation "D" => sWholeDiagonal K S
local notation "gen" => sourcePrimeExponentUnit K hζ S₀
local notation "active" => sourceReflectionActiveExponents K S₀
local notation "b₀" => fun f d => gen (active f + d)
local notation "rep" => sourceExteriorUnitSixthRepresentative S
local notation "arg" => sourceKPSLocalReflectionArgument K S
local notation "ω" => fun b =>
  sourceKPReflectionProductPhase K hζ b (sourceKPOrientedHorizontal K hζ) (sourceKPAllInfinitePlaces K)
local notation "C₁" => sourceKPCuspResidualFourierValue K hζ (1 : Kˣ)
local notation "L" => sourceKPLocalCompactProductLift K hζ S
local notation "σ" => sourceKPTraceJacquetFrequencyAt K
local notation "Ω" => sourceKPTameUniformizerCharacter K hζ
local notation "pre" => sourceKPAdelicOutgoingReflectedRetainedPrefix K hζ S₀
local notation "lift" => sourceKPAdelicOutgoingRetainedJacquetBasisLift K hζ
local notation "profile" => sourceKPAdelicOutgoingRetainedJacquetBasisDiagonalProfile K hζ
local notation "weyl" => sourceKPReflectedC1WeylPhase K hζ S₀
local notation "phase" => sourceKPReflectedC1ExteriorPhase K hζ S₀

variable {J : Ideal (𝓞 K)}

theorem sourceKPReflectedPhysicalBranchTerm_retainedTensor
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    {T : ℝ} (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (h d : E) (f : Finset Pr) (hf : f ∈ sourceReflectionActiveChoices K S₀ h)
    (u : ExteriorUnitSixthClasses S) (m : Kˣ) (x : Whole)
    (hs : 0 < (1 / 6 : ℂ).re) :
    let b := b₀ f d
    let z := D m*x
    let t := one_le_two.trans hT.le
    let q₀ := sourceKPPositiveSeedData_q₀ K hζ S₀ p
    let Seed := SourceKPRetainedSeedIndex K S p.R p.M
    let Basis := SourceKPAdelicOutgoingRetainedJacquetLabel K hζ hs S
    ω b * sourceKPReflectedPhysicalBranchTerm K hζ S₀ hS η hJ hT p
      (h+d) u (f∪d.support) b m x =
    sourceKPPhysicalNegativePhase K hζ S₀ hS η hJ (rep u) b (D m) *
      (C₁ t q₀)⁻¹ * sourceKPAllowedClassGate K hζ S₀ (arg b*x⁻¹) *
      (sourceKPPhysicalRowFiniteCharacter K hζ S₀ hS η hJ (rep u) z : ℂ) *
      weyl b z *
      sourceReflectionSignedExteriorProduct K S₀ hζ hS (h+d) (f∪d.support) (m / b^2) *
      (∏ P : S, (Ω P.val (σ P.val m) (z.2 P) : ℂ)) *
      (∑ k : Seed × Basis,
        sourceKPRetainedSeedWeight K S p.R p.M k.1 *
        C₁ t ((L (fun P => lift P.val hs (k.2 P))).2) *
          ∏ P : S, profile P.val hs (k.2 P) (pre p.R p.M k.1 p.a P) (z.2 P)) *
      sourceKPReflectedArchBesselFactor K S₀ z := by
  let b := b₀ f d
  let z := D m*x
  have hx : (D m)⁻¹*z = x := inv_mul_cancel_left _ _
  have hr := sourceKPAdelicOutgoingReflectedRetainedC1_seed_sum_substituted_tensor
    K hζ S₀ hs hT m z p.R p.M p.a
  rw [hx] at hr
  dsimp only
  rw [sourceKPReflectedPhysicalBranchTerm_weight,
    sourceKPReflectedPhysicalFiniteCoefficient_factor K hζ S₀ hS hJ hT p h d f hf m x]
  unfold sourceKPReflectedC1RetainedSum
  rw [hr]
  have hw := sourceKPReflectedC1Phase_translate K hζ S₀ (h+d) m b x
  change weyl b x * phase (h+d) m b = weyl b z at hw
  rw [hw]
  ring

end
end ArtinMatthews

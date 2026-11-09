module

public import ArtinMatthews.SourceKPReflectedPhysicalTerms
public import ArtinMatthews.SourceKPReflectedC1Factorization
public import ArtinMatthews.SourceReflectionSignedExteriorFrequency
public import ArtinMatthews.SourceReflectionExteriorSupport


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
local notation "gen" => sourcePrimeExponentUnit K hζ S₀
local notation "active" => sourceReflectionActiveExponents K S₀
local notation "b₀" => fun f d => gen (active f + d)
local notation "weyl" => sourceKPReflectedC1WeylPhase K hζ S₀
local notation "phase" => sourceKPReflectedC1ExteriorPhase K hζ S₀


private theorem active_subset (h d : E) (f : Finset Pr)
    (hf : f ∈ sourceReflectionActiveChoices K S₀ h) :
    f ∪ d.support ⊆ (h+d).support := by
  intro P hP
  apply (sourceReflectionExteriorRow_mem K S₀ h d P).mpr
  exact Finset.mem_union.mpr ((Finset.mem_union.mp hP).imp (fun hp => sourceReflectionActiveChoice_subset K S₀ hf hp) id)

variable {J : Ideal (𝓞 K)}

theorem sourceKPReflectedPhysicalFiniteCoefficient_factor
    (hS : standardWeilBadPlaces K ⊆ S) (hJ : J ≠ ⊥)
    {T : ℝ} (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (h d : E) (f : Finset Pr) (hf : f ∈ sourceReflectionActiveChoices K S₀ h)
    (m : Kˣ) (x : Whole) :
    let b := b₀ f d
    sourceKPReflectedPhysicalFiniteCoefficient K hζ S₀ hS hJ hT p (h+d) (f∪d.support) b m x =
      weyl b x * phase (h+d) m b *
        sourceReflectionSignedExteriorProduct K S₀ hζ hS (h+d) (f∪d.support) (m / b^2) *
        sourceKPReflectedC1RetainedSum K hζ S₀ hT m x p.R p.M p.a := by
  let b := b₀ f d
  have he := sourceKPReflectedC1ActiveCoefficient_factor K hζ S₀ hS hT m f d (h+d)
    (active_subset K S₀ h d f hf) x p.R p.M p.a
  change sourceKPReflectedC1ActiveCoefficient K hζ S₀ hT m f d (h+d) x p.R p.M p.a = _
  exact he.trans (by rw [inv_pow, div_eq_mul_inv])

theorem sourceKPReflectedPhysicalBranchTerm_zero_off_supported
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    {T : ℝ} (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (h d : E) (f : Finset Pr) (hf : f ∈ sourceReflectionActiveChoices K S₀ h)
    (hd : sourceReflectionIsSquarefree d) (hhd : Disjoint h.support d.support)
    (u : ExteriorUnitSixthClasses S) (m : Kˣ) (x : Whole)
    (hm : m / (b₀ f d)^2 ∉ Set.range (fun n : SourceReflectionSupportedFrequency K S₀ (b₀ f d) d =>
      n.val.val)) :
    sourceKPReflectedPhysicalBranchTerm K hζ S₀ hS η hJ hT p (h+d) u (f∪d.support) (b₀ f d) m x = 0 := by
  have hfd : Disjoint f d.support :=
    Finset.disjoint_of_subset_left (sourceReflectionActiveChoice_subset K S₀ hf) hhd
  have hz := sourceReflectionSignedExteriorProduct_eq_zero_off_frequency_range K S₀ hζ hS
    h d f hd hhd hfd (m / (b₀ f d)^2) hm
  unfold sourceKPReflectedPhysicalBranchTerm
  rw [sourceKPReflectedPhysicalFiniteCoefficient_factor K hζ S₀ hS hJ hT p h d f hf m x, hz]
  simp only [mul_zero, zero_mul]


theorem sourceKPReflectedPhysicalBranchTerm_hasSum_supported
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    {T : ℝ} (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (h d : E) (f : Finset Pr) (hf : f ∈ sourceReflectionActiveChoices K S₀ h)
    (hd : sourceReflectionIsSquarefree d) (hhd : Disjoint h.support d.support)
    (u : ExteriorUnitSixthClasses S) (x : Whole) :
    let b := b₀ f d
    HasSum (fun i : SourceReflectionSupportedTermIndex K S₀ f d ×
        (ExteriorUnitSixthClasses S × sNormOneSixthSubgroup K S) =>
      sourceKPReflectedPhysicalBranchTerm K hζ S₀ hS η hJ hT p
        (h+d) u (f∪d.support) b (sourceKPReflectedNumerator K hζ S₀ f d i.1 i.2.1 i.2.2) x)
      (sourceKPReflectedPhysicalBranchValue K hζ S₀ hS η hJ hT p (h+d) u (f∪d.support) b x) := by
  dsimp only
  exact sourceKPReflectedNumerator_hasSum K hζ S₀ f d
    (A := fun m => sourceKPReflectedPhysicalBranchTerm K hζ S₀ hS η hJ hT p
      (h+d) u (f∪d.support) (b₀ f d) m x)
    (sourceKPReflectedPhysicalBranchTerm_hasSum K hζ S₀ hS η hJ hT p
      (h+d) u (f∪d.support) (b₀ f d) x)
    (fun m hm => sourceKPReflectedPhysicalBranchTerm_zero_off_supported K hζ S₀ hS η hJ hT
      p h d f hf hd hhd u m x hm)

end
end ArtinMatthews

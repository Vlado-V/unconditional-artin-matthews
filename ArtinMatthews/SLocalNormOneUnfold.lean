module

public import ArtinMatthews.SLocalNormOneHaar
public import ArtinMatthews.QuotientPeriodization


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine norm-one source quotient has the exact unfolding law
for the diagonal sixth-power periodization, with its induced Haar
normalization and integrability derived. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

def sNormOnePeriodize (f : SNormOne K S → ℂ) : SNormOneSixthQuotient K S → ℂ :=
  quotientPeriodize (sNormOneSixthSubgroup K S) f

@[simp] theorem sNormOnePeriodize_mk (f : SNormOne K S → ℂ) (x : SNormOne K S) :
    sNormOnePeriodize K S f (sNormOneSixthQuotientMap K S x) =
      ∑' a : (sNormOneSixthSubgroup K S).op, f (a • x) := rfl

theorem sNormOnePeriodize_unfold (ν : Measure (SNormOne K S)) [ν.IsHaarMeasure]
    (f : SNormOne K S → ℂ) (hfm : Measurable f) (hfi : Integrable f ν) :
    Integrable (sNormOnePeriodize K S f) (sNormOneQuotientMeasure K S ν) ∧
      (∫ y, sNormOnePeriodize K S f y ∂sNormOneQuotientMeasure K S ν) = ∫ x, f x ∂ν := by
  let : Countable (sNormOneSixthSubgroup K S) := sNormOneSixthSubgroup_countable K S
  exact quotientPeriodize_unfold (sNormOneSixthSubgroup K S) ν
    (sNormOneFundamentalDomain K S ν) f hfm hfi

end
end ArtinMatthews.SourcePhysical

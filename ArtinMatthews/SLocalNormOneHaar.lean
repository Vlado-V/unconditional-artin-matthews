module

public import ArtinMatthews.SLocalNormOneLocalCompact
public import ArtinMatthews.CompactQuotientSection
public import ArtinMatthews.CompactQuotientBorel


set_option backward.privateInPublic true
@[expose] public section

/-! The physical quotient measure is obtained from Haar measure on the
actual norm-one group by restricting to a proved bounded fundamental
domain and pushing down. Its normalization is inherited from that Haar
measure, not replaced by probability normalization. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

scoped instance sourceNormOneMeasurableSpace : MeasurableSpace (SNormOne K S) := borel _

scoped instance sourceNormOneBorelSpace : BorelSpace (SNormOne K S) := ⟨rfl⟩

theorem sNormOneSixthQuotient_borel : BorelSpace (SNormOneSixthQuotient K S) := by
  let : DiscreteTopology (sNormOneSixthSubgroup K S) := sNormOneSixthSubgroup_discrete K S
  exact compact_cover_quotient_borel (sNormOneSixthSubgroup K S) (sNormOneCover K S)
    (sNormOneCover_isCompact K S) (sNormOneCover_quotient K S)

theorem exists_sNormOneFundamentalSet : ∃ D : Set (SNormOne K S),
    MeasurableSet D ∧ D ⊆ sNormOneCover K S ∧ Set.InjOn (sNormOneSixthQuotientMap K S) D ∧
      sNormOneSixthQuotientMap K S '' D = Set.univ := by
  let : DiscreteTopology (sNormOneSixthSubgroup K S) := sNormOneSixthSubgroup_discrete K S
  let : BorelSpace (SNormOneSixthQuotient K S) := sNormOneSixthQuotient_borel K S
  exact exists_compact_measurable_quotient_section (sNormOneSixthSubgroup K S)
    (sNormOneCover K S) (sNormOneCover_isCompact K S) (sNormOneCover_quotient K S)

def sNormOneFundamentalSet : Set (SNormOne K S) := (exists_sNormOneFundamentalSet K S).choose

theorem sNormOneFundamentalSet_spec :
    MeasurableSet (sNormOneFundamentalSet K S) ∧ sNormOneFundamentalSet K S ⊆ sNormOneCover K S ∧
      Set.InjOn (sNormOneSixthQuotientMap K S) (sNormOneFundamentalSet K S) ∧
      sNormOneSixthQuotientMap K S '' sNormOneFundamentalSet K S = Set.univ :=
  (exists_sNormOneFundamentalSet K S).choose_spec

theorem sNormOneFundamentalDomain (ν : Measure (SNormOne K S)) :
    IsFundamentalDomain (sNormOneSixthSubgroup K S).op (sNormOneFundamentalSet K S) ν := by
  obtain ⟨hm, _, hi, hq⟩ := sNormOneFundamentalSet_spec K S
  exact isFundamentalDomain_of_quotient_section (sNormOneSixthSubgroup K S)
    (sNormOneFundamentalSet K S) hm hi hq ν

def sNormOneQuotientMeasure (ν : Measure (SNormOne K S)) : Measure (SNormOneSixthQuotient K S) :=
  (ν.restrict (sNormOneFundamentalSet K S)).map (sNormOneSixthQuotientMap K S)

theorem sNormOneQuotientMeasure_apply (ν : Measure (SNormOne K S))
    {A : Set (SNormOneSixthQuotient K S)} (hA : MeasurableSet A) :
    sNormOneQuotientMeasure K S ν A =
      ν ((sNormOneSixthQuotientMap K S) ⁻¹' A ∩ sNormOneFundamentalSet K S) :=
  measure_map_restrict_apply (G := (sNormOneSixthSubgroup K S).op) ν (sNormOneFundamentalSet K S) hA

theorem sNormOneQuotientMeasure_finite (ν : Measure (SNormOne K S)) [ν.IsHaarMeasure] :
    IsFiniteMeasure (sNormOneQuotientMeasure K S ν) := by
  constructor
  rw [sNormOneQuotientMeasure_apply K S ν MeasurableSet.univ, Set.preimage_univ, Set.univ_inter]
  exact (measure_mono (sNormOneFundamentalSet_spec K S).2.1).trans_lt
    (sNormOneCover_isCompact K S).measure_lt_top

theorem sNormOneQuotientMeasure_normalized (ν : Measure (SNormOne K S)) [ν.IsHaarMeasure] :
    QuotientMeasureEqMeasurePreimage (G := (sNormOneSixthSubgroup K S).op) ν
      (sNormOneQuotientMeasure K S ν) := by
  let : Countable (sNormOneSixthSubgroup K S) := sNormOneSixthSubgroup_countable K S
  exact (sNormOneFundamentalDomain K S ν).quotientMeasureEqMeasurePreimage_quotientMeasure

theorem sNormOneQuotientMeasure_isHaar (ν : Measure (SNormOne K S)) [ν.IsHaarMeasure] :
    (sNormOneQuotientMeasure K S ν).IsHaarMeasure := by
  let : LocallyCompactSpace (SNormOne K S) := sNormOne_locallyCompact K S
  let : PolishSpace (SNormOne K S) := sNormOne_polish K S
  let : SecondCountableTopology (SNormOneSixthQuotient K S) := sNormOneSixthQuotient_secondCountable K S
  let : T2Space (SNormOneSixthQuotient K S) := sNormOneSixthQuotient_t2 K S
  let : BorelSpace (SNormOneSixthQuotient K S) := sNormOneSixthQuotient_borel K S
  let : Countable (sNormOneSixthSubgroup K S) := sNormOneSixthSubgroup_countable K S
  let : HasFundamentalDomain (sNormOneSixthSubgroup K S).op (SNormOne K S) ν :=
    ⟨⟨sNormOneFundamentalSet K S, sNormOneFundamentalDomain K S ν⟩⟩
  let : IsFiniteMeasure (sNormOneQuotientMeasure K S ν) := sNormOneQuotientMeasure_finite K S ν
  let : QuotientMeasureEqMeasurePreimage (G := (sNormOneSixthSubgroup K S).op) ν
      (sNormOneQuotientMeasure K S ν) := sNormOneQuotientMeasure_normalized K S ν
  exact QuotientMeasureEqMeasurePreimage.haarMeasure_quotient ν

def sNormOneHaar : Measure (SNormOne K S) := by
  let : LocallyCompactSpace (SNormOne K S) := sNormOne_locallyCompact K S
  exact Measure.haar

theorem sNormOneHaar_isHaar : (sNormOneHaar K S).IsHaarMeasure := by
  unfold sNormOneHaar
  infer_instance

theorem sNormOneQuotient_integral (ν : Measure (SNormOne K S))
    (f : SNormOneSixthQuotient K S → ℂ) (hf : Integrable f (sNormOneQuotientMeasure K S ν)) :
    (∫ q, f q ∂sNormOneQuotientMeasure K S ν) =
      ∫ x in sNormOneFundamentalSet K S, f (sNormOneSixthQuotientMap K S x) ∂ν :=
  integral_map measurable_quotient_mk''.aemeasurable hf.aestronglyMeasurable

end
end ArtinMatthews.SourcePhysical

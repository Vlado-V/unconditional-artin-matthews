module

public import ArtinMatthews.SourceAdelicRationalTopology
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Topology.Separation.CompletelyRegular


set_option backward.privateInPublic true
@[expose] public section

/-! The half-open Minkowski domain times the integral finite adeles is
an actual measurable fundamental domain for rational translations. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField AdeleRing Topology Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

local instance : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance : BorelSpace 𝔸[K] := ⟨rfl⟩
local instance : MeasurableSpace 𝔸ᶠ[K] := borel 𝔸ᶠ[K]
local instance : BorelSpace 𝔸ᶠ[K] := ⟨rfl⟩

def sourceKPAdelicFundamentalDomain : Set 𝔸[K] :=
  {a | InfiniteAdeleRing.ringEquiv_mixedSpace K a.1 ∈
      ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis K) ∧
    a.2 ∈ IntegralAdeles.Construction.finiteIntegralRing K}

theorem sourceKPAdelicFundamentalDomain_measurable :
    MeasurableSet (sourceKPAdelicFundamentalDomain K) := by
  have hc : Continuous (fun a : 𝔸[K] => InfiniteAdeleRing.ringEquiv_mixedSpace K a.1) :=
    (ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph K).continuous.comp continuous_fst
  have hI : Measurable (fun a : 𝔸[K] => InfiniteAdeleRing.ringEquiv_mixedSpace K a.1) := hc.measurable
  have hF : Measurable (fun a : 𝔸[K] => a.2) :=
    (show Continuous (fun a : 𝔸[K] => a.2) from continuous_snd).measurable
  exact ((ZSpan.fundamentalDomain_measurableSet (mixedEmbedding.latticeBasis K)).preimage hI).inter
    ((IntegralAdeles.Construction.isOpen_finiteIntegralRing K).measurableSet.preimage hF)

theorem sourceKPAdelicFundamentalDomain_subset_compact :
    sourceKPAdelicFundamentalDomain K ⊆ CompactQuotient.Construction.adelicCompactRepresentatives K := by
  intro a ha
  exact (CompactQuotient.Construction.mem_adelicCompactRepresentatives K a).mpr
    ⟨ZSpan.fundamentalDomain_subset_parallelepiped (mixedEmbedding.latticeBasis K) ha.1, ha.2⟩

theorem sourceKPIntegerMixedFundamentalRemainder (x : mixedEmbedding.mixedSpace K) :
    ∃ r : 𝓞 K, x - mixedEmbedding K (algebraMap (𝓞 K) K r) ∈
      ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis K) := by
  let b := mixedEmbedding.latticeBasis K
  have hmem : (ZSpan.floor b x).val ∈ mixedEmbedding.integerLattice K := by
    rw [← mixedEmbedding.span_latticeBasis K]
    exact (ZSpan.floor b x).property
  obtain ⟨r, hr⟩ := hmem
  refine ⟨r, ?_⟩
  change mixedEmbedding K (algebraMap (𝓞 K) K r) = (ZSpan.floor b x).val at hr
  rw [hr]
  exact ZSpan.fract_mem_fundamentalDomain b x

theorem sourceKPAdelicFundamentalDomain_exists (a : 𝔸[K]) :
    ∃ q : K, a - algebraMap K 𝔸[K] q ∈ sourceKPAdelicFundamentalDomain K := by
  obtain ⟨q, hq⟩ := CompactQuotient.Construction.exists_rational_finite_integral_remainder K a.2
  obtain ⟨r, hr⟩ := sourceKPIntegerMixedFundamentalRemainder K
    (InfiniteAdeleRing.ringEquiv_mixedSpace K (a - algebraMap K 𝔸[K] q).1)
  refine ⟨q + algebraMap (𝓞 K) K r, ?_, ?_⟩
  · change InfiniteAdeleRing.ringEquiv_mixedSpace K
      (a.1 - algebraMap K (InfiniteAdeleRing K) (q + algebraMap (𝓞 K) K r)) ∈ _
    change InfiniteAdeleRing.ringEquiv_mixedSpace K
      (a.1 - algebraMap K (InfiniteAdeleRing K) q) - mixedEmbedding K (algebraMap (𝓞 K) K r) ∈ _ at hr
    rw [map_add, sub_add_eq_sub_sub, map_sub, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
    exact hr
  · have hh := (IntegralAdeles.Construction.finiteIntegralRing K).sub_mem hq
      (IntegralAdeles.Construction.algebraMap_mem_finiteIntegralRing K r)
    simpa only [map_add, Prod.snd_sub, Prod.snd_add, sub_add_eq_sub_sub,
      IsScalarTower.algebraMap_apply] using! hh

theorem sourceKPAdelicFundamentalDomain_rational_difference {a b : 𝔸[K]}
    (ha : a ∈ sourceKPAdelicFundamentalDomain K) (hb : b ∈ sourceKPAdelicFundamentalDomain K)
    (q : K) (he : b - a = algebraMap K 𝔸[K] q) : q = 0 := by
  have hfin : algebraMap K 𝔸ᶠ[K] q ∈ IntegralAdeles.Construction.finiteIntegralRing K := by
    have h := (IntegralAdeles.Construction.finiteIntegralRing K).sub_mem hb.2 ha.2
    have he' := congrArg Prod.snd he
    change b.2 - a.2 = algebraMap K 𝔸ᶠ[K] q at he'
    rwa [he'] at h
  obtain ⟨r, hr⟩ := (IntegralAdeles.Construction.rational_mem_finiteIntegral_iff K q).mp hfin
  have hz : mixedEmbedding K q ∈ Submodule.span ℤ (Set.range (mixedEmbedding.latticeBasis K)) := by
    rw [mixedEmbedding.span_latticeBasis]
    exact ⟨r, congrArg (mixedEmbedding K) hr⟩
  have harch : InfiniteAdeleRing.ringEquiv_mixedSpace K b.1 =
      mixedEmbedding K q + InfiniteAdeleRing.ringEquiv_mixedSpace K a.1 := by
    have h := congrArg (fun t : 𝔸[K] => InfiniteAdeleRing.ringEquiv_mixedSpace K t.1) he
    change InfiniteAdeleRing.ringEquiv_mixedSpace K (b.1 - a.1) =
      InfiniteAdeleRing.ringEquiv_mixedSpace K (algebraMap K (InfiniteAdeleRing K) q) at h
    rw [map_sub, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp] at h
    exact sub_eq_iff_eq_add.mp h
  have hsame : InfiniteAdeleRing.ringEquiv_mixedSpace K b.1 =
      InfiniteAdeleRing.ringEquiv_mixedSpace K a.1 := by
    calc
      _ = ZSpan.fract (mixedEmbedding.latticeBasis K) (InfiniteAdeleRing.ringEquiv_mixedSpace K b.1) :=
        (ZSpan.fract_eq_self.mpr hb.1).symm
      _ = ZSpan.fract (mixedEmbedding.latticeBasis K)
          (mixedEmbedding K q + InfiniteAdeleRing.ringEquiv_mixedSpace K a.1) := congrArg _ harch
      _ = ZSpan.fract (mixedEmbedding.latticeBasis K) (InfiniteAdeleRing.ringEquiv_mixedSpace K a.1) :=
        ZSpan.fract_zSpan_add _ _ hz
      _ = _ := ZSpan.fract_eq_self.mpr ha.1
  have hm : mixedEmbedding K q = 0 := by
    apply add_right_cancel (b := InfiniteAdeleRing.ringEquiv_mixedSpace K a.1)
    simpa only [zero_add] using harch.symm.trans hsame
  exact (mixedEmbedding_injective K) (by simpa only [map_zero] using hm)

theorem sourceKPAdelicFundamentalDomain_unique (a : 𝔸[K]) :
    ∃! q : K, a - algebraMap K 𝔸[K] q ∈ sourceKPAdelicFundamentalDomain K := by
  obtain ⟨q, hq⟩ := sourceKPAdelicFundamentalDomain_exists K a
  refine ⟨q, hq, ?_⟩
  intro r hr
  have he : (a - algebraMap K 𝔸[K] r) - (a - algebraMap K 𝔸[K] q) =
      algebraMap K 𝔸[K] (q - r) := by rw [map_sub]; abel
  have h := sourceKPAdelicFundamentalDomain_rational_difference K hq hr (q - r) he
  exact (sub_eq_zero.mp h).symm

theorem sourceKPAdelicFundamentalDomain_isFundamental (μ : Measure 𝔸[K]) :
    IsAddFundamentalDomain (sourceKPAdelicRationals K) (sourceKPAdelicFundamentalDomain K) μ := by
  apply IsAddFundamentalDomain.mk' (sourceKPAdelicFundamentalDomain_measurable K).nullMeasurableSet
  intro a
  obtain ⟨q, hq, huniq⟩ := sourceKPAdelicFundamentalDomain_unique K a
  refine ⟨sourceKPRationalAdeleEquiv K (-q), ?_, ?_⟩
  · change algebraMap K 𝔸[K] (-q) + a ∈ sourceKPAdelicFundamentalDomain K
    simpa only [map_neg, sub_eq_add_neg, add_comm] using hq
  · intro u hu
    obtain ⟨r, rfl⟩ := (sourceKPRationalAdeleEquiv K).surjective u
    change algebraMap K 𝔸[K] r + a ∈ sourceKPAdelicFundamentalDomain K at hu
    have hr : a - algebraMap K 𝔸[K] (-r) ∈ sourceKPAdelicFundamentalDomain K := by
      simpa only [map_neg, sub_neg_eq_add, add_comm] using hu
    exact congrArg (sourceKPRationalAdeleEquiv K) (by simpa only [neg_neg] using congrArg Neg.neg (huniq (-r) hr))

end
end ArtinMatthews

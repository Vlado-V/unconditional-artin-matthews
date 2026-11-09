module

public import ArtinMatthews.ProbeHilbertSReciprocity
public import ArtinMatthews.SIntegerPrincipalExterior


set_option backward.privateInPublic true
@[expose] public section

/-! Actual S-units are isotropic for the actual S-Hilbert product.
This is derived from the global Hilbert product formula and tame
triviality outside S. No maximality or self-orthogonality is assumed. -/

namespace ArtinMatthews

open NumberField IsDedekindDomain KummerTheory GlobalClassFieldTheory.Reciprocity
open VaryingKummerAnalytic SIntegerPrincipalization
open scoped NumberField BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]

theorem sUnit_finiteHilbert_eq_one_outside
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : powerResidueExponentFinitePlaces K n ⊆ S)
    (a b : Set.unit (R := 𝓞 K) (↑S : Set (HeightOneSpectrum (𝓞 K))) K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    finitePlaceHilbertSymbol K n hnK hmu v (a : Kˣ) (b : Kˣ) = 1 := by
  apply finitePlaceHilbertSymbol_eq_one_of_valuation_eq_one
  · exact a.property v hv
  · exact b.property v hv
  · have hvn : ¬ v.asIdeal ∣ powerResidueExponentIdeal K n := by
      simpa only [mem_powerResidueExponentFinitePlaces_iff] using
        (show v ∉ powerResidueExponentFinitePlaces K n from fun he => hv (hS he))
    have hnot : ((n : ℕ) : 𝓞 K) ∉ v.asIdeal := by
      intro he
      apply hvn
      rw [powerResidueExponentIdeal, Ideal.dvd_span_singleton]
      exact he
    simpa only [map_natCast] using
      (v.valuation_eq_one_iff_notMem (K := K) (r := ((n : ℕ) : 𝓞 K))).2 hnot

theorem sUnit_hilbertSProduct_eq_one
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : powerResidueExponentFinitePlaces K n ⊆ S)
    (a b : Set.unit (R := 𝓞 K) (↑S : Set (HeightOneSpectrum (𝓞 K))) K) :
    probeHilbertSProduct K n hnK hmu S (a : Kˣ) (b : Kˣ) = 1 := by
  let H := fun v : HeightOneSpectrum (𝓞 K) =>
    finitePlaceHilbertSymbol K n hnK hmu v (a : Kˣ) (b : Kˣ)
  have hsupp : Function.mulSupport H ⊆ (↑S : Set (HeightOneSpectrum (𝓞 K))) := by
    intro v hv
    by_contra hvS
    exact hv (sUnit_finiteHilbert_eq_one_outside K n hnK hmu S hS a b v hvS)
  have hall := hilbertSymbol_allPlaces_product_eq_one K n hnK hmu (a : Kˣ) (b : Kˣ)
  change (∏ v : InfinitePlace K, infinitePlaceHilbertSymbol K n v (a : Kˣ) (b : Kˣ)) *
    ∏ᶠ v, H v = 1 at hall
  rw [finprod_eq_prod_of_mulSupport_subset H hsupp] at hall
  exact hall

theorem sUnit_hilbertSIsotropic
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : powerResidueExponentFinitePlaces K n ⊆ S) :
    ProbeHilbertSIsotropic K n hnK hmu S
      (Set.unit (R := 𝓞 K) (↑S : Set (HeightOneSpectrum (𝓞 K))) K) := by
  intro a ha b hb
  exact sUnit_hilbertSProduct_eq_one K n hnK hmu S hS ⟨a, ha⟩ ⟨b, hb⟩

theorem exists_principal_sIntegers_hilbertSIsotropic
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S ∧
      powerResidueExponentFinitePlaces K n ⊆ S ∧
      IsPrincipalIdealRing (IntegerRing (K := K) S) ∧
      ProbeHilbertSIsotropic K n hnK hmu S
        (Set.unit (R := 𝓞 K) (↑S : Set (HeightOneSpectrum (𝓞 K))) K) := by
  let S := principalizingSet (S₀ ∪ powerResidueExponentFinitePlaces K n)
  have hbase := required_subset_principalizingSet (S₀ ∪ powerResidueExponentFinitePlaces K n)
  have hS : powerResidueExponentFinitePlaces K n ⊆ S :=
    Finset.Subset.trans Finset.subset_union_right hbase
  exact ⟨S, Finset.Subset.trans Finset.subset_union_left hbase, hS,
    principalIntegerRing_isPrincipalIdealRing _, sUnit_hilbertSIsotropic K n hnK hmu S hS⟩

end
end ArtinMatthews

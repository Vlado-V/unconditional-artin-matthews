module

public import ArtinMatthews.ProbeHilbertSReciprocity
public import ArtinMatthews.SIntegerAwayLocalization
public import Mathlib.RingTheory.SimpleRing.Principal
public import ArtinMatthews.SIntegerFinitePrincipalization
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.HilbertProductFormula
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


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

module

public import ArtinMatthews.SIntegerStandardPhase
public import ArtinMatthews.ProbeHilbertSReciprocity
public import ArtinMatthews.AllowedGeneratorBase
public import ArtinMatthews.SLocalPaperHilbertNormalization
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.PNatToNat
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual field-valued allowed prime generators satisfy pairwise
Hilbert reciprocity. Isotropy is discharged from the constructed paper B,
and exterior unit support is derived from literal OS prime ideals.
The paper/CFT transpose remains explicit. -/
namespace ArtinMatthews.SIntegerAllowedReciprocity

open NumberField IsDedekindDomain KummerTheory
open GlobalClassFieldTheory.Reciprocity GlobalClassFieldTheory.GlobalClassFields
open ArtinMatthews ArtinMatthews.AllowedGenerators ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section
variable (K : Type) [Field K] [NumberField K]

omit [NumberField K] in
theorem sourceSixRoots {ζ : K} (hζ : IsPrimitiveRoot ζ 12) : (primitiveRoots 6 K).Nonempty :=
  sLocalPrimitiveRoots K 6 (sourceHilbertRootSix_isPrimitive K hζ)

theorem allowedHilbertS_isotropic {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ProbeHilbertSIsotropic K 6 (by norm_num) (sourceSixRoots K hζ)
      (sourceHilbertSet K S₀) (allowedSubgroup K hζ S₀) := by
  intro a ha b hb
  have hi := chosenB_isotropic K hζ S₀
    (sLocalRingGlobalClassMap K 6 (sourceHilbertSet K S₀) b) hb
    (sLocalRingGlobalClassMap K 6 (sourceHilbertSet K S₀) a) ha
  rw [paperSourceHilbertForm_global_eq_SProduct K hζ (sourceHilbertSet K S₀) b a] at hi
  apply (nthRootsSubgroupEquivRootsOfUnity K 6).injective
  exact hi.trans (map_one (nthRootsSubgroupEquivRootsOfUnity K 6)).symm

theorem sourceSix_unit_valuation (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ sourceHilbertSet K S₀) :
    v.valuation K (6 : K) = 1 := by
  apply valuation_natCast_eq_one_of_not_mem_sUnitKummerNormSupport (K := K) 6 ∅ (w := v)
  intro hm
  exact hv (normSupport_subset_sourceHilbertSet K S₀ 6 (Or.inr (Or.inr rfl)) hm)

theorem sourceHilbert_pair_product {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P Q : HeightOneSpectrum (𝓞 K)) (hPQ : P ≠ Q)
    (hP : P ∉ sourceHilbertSet K S₀) (hQ : Q ∉ sourceHilbertSet K S₀)
    (a b : Kˣ) (ha : a ∈ allowedSubgroup K hζ S₀) (hb : b ∈ allowedSubgroup K hζ S₀)
    (hout : ∀ v, v ∉ sourceHilbertSet K S₀ → v ≠ P → v ≠ Q →
      v.valuation K (a : K) = 1 ∧ v.valuation K (b : K) = 1) :
    finitePlaceHilbertSymbol K 6 (by norm_num) (sourceSixRoots K hζ) P a b *
      finitePlaceHilbertSymbol K 6 (by norm_num) (sourceSixRoots K hζ) Q a b = 1 := by
  let S := sourceHilbertSet K S₀
  let H := fun v : HeightOneSpectrum (𝓞 K) =>
    finitePlaceHilbertSymbol K 6 (by norm_num) (sourceSixRoots K hζ) v a b
  have hsupp : Function.mulSupport H ⊆ ((insert P (insert Q S) : Finset _) : Set _) := by
    intro v hv
    change H v ≠ 1 at hv
    change v ∈ insert P (insert Q S)
    by_contra hnot
    have hvP : v ≠ P := by intro he; apply hnot; simp only [he, Finset.mem_insert_self]
    have hvQ : v ≠ Q := by
      intro he
      apply hnot
      exact Finset.mem_insert.mpr (Or.inr (by rw [he]; exact Finset.mem_insert_self _ _))
    have hvS : v ∉ S := by
      intro he
      exact hnot (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr he))))
    obtain ⟨hav, hbv⟩ := hout v hvS hvP hvQ
    exact hv (finitePlaceHilbertSymbol_eq_one_of_valuation_eq_one K 6 (by norm_num)
      (sourceSixRoots K hζ) a b v hav hbv (sourceSix_unit_valuation K S₀ v hvS))
  have hall := hilbertSymbol_allPlaces_product_eq_one K 6 (by norm_num) (sourceSixRoots K hζ) a b
  change (∏ v : InfinitePlace K, infinitePlaceHilbertSymbol K 6 v a b) * ∏ᶠ v, H v = 1 at hall
  have hPS : P ∉ S := hP
  have hQS : Q ∉ S := hQ
  have hPins : P ∉ insert Q S := by
    intro hm
    rcases Finset.mem_insert.mp hm with he | he
    · exact hPQ he
    · exact hPS he
  rw [finprod_eq_prod_of_mulSupport_subset H hsupp,
    Finset.prod_insert hPins, Finset.prod_insert hQS] at hall
  have hiso := allowedHilbertS_isotropic K hζ S₀ a ha b hb
  unfold probeHilbertSProduct at hiso
  change (∏ v : InfinitePlace K, infinitePlaceHilbertSymbol K 6 v a b) * ∏ v ∈ S, H v = 1 at hiso
  calc
    H P * H Q = (H P * H Q) * 1 := (mul_one _).symm
    _ = (H P * H Q) * ((∏ v : InfinitePlace K, infinitePlaceHilbertSymbol K 6 v a b) *
        ∏ v ∈ S, H v) := by rw [hiso]
    _ = 1 := by simpa only [mul_assoc, mul_left_comm, mul_comm] using hall

theorem sourceHilbert_pair_reciprocity {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P Q : HeightOneSpectrum (𝓞 K)) (hPQ : P ≠ Q)
    (hP : P ∉ sourceHilbertSet K S₀) (hQ : Q ∉ sourceHilbertSet K S₀)
    (a b : Kˣ) (ha : a ∈ allowedSubgroup K hζ S₀) (hb : b ∈ allowedSubgroup K hζ S₀)
    (hout : ∀ v, v ∉ sourceHilbertSet K S₀ → v ≠ P → v ≠ Q →
      v.valuation K (a : K) = 1 ∧ v.valuation K (b : K) = 1) :
    finitePlaceHilbertSymbol K 6 (by norm_num) (sourceSixRoots K hζ) P b a =
      finitePlaceHilbertSymbol K 6 (by norm_num) (sourceSixRoots K hζ) Q a b := by
  have hp := sourceHilbert_pair_product K hζ S₀ P Q hPQ hP hQ a b ha hb hout
  have hsk := finitePlaceHilbertSymbol_skew K 6 (by norm_num) (sourceSixRoots K hζ) P a b
  rw [hsk, inv_mul_eq_one] at hp
  exact hp

theorem sourceAllowedPrime_pair_reciprocity {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P Q : HeightOneSpectrum (𝓞 K)) (hPQ : P ≠ Q)
    (hP : P ∉ sourceHilbertSet K S₀) (hQ : Q ∉ sourceHilbertSet K S₀)
    (a b : PrincipalIntegerRing (sourceHilbertSeed K S₀))
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing (sourceHilbertSeed K S₀))) = Ideal.span {a})
    (hb : Q.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing (sourceHilbertSeed K S₀))) = Ideal.span {b})
    (haB : generatorFieldUnit (sourceHilbertSeed K S₀) P a ha ∈ allowedSubgroup K hζ S₀)
    (hbB : generatorFieldUnit (sourceHilbertSeed K S₀) Q b hb ∈ allowedSubgroup K hζ S₀) :
    finitePlaceHilbertSymbol K 6 (by norm_num) (sourceSixRoots K hζ) P
        (generatorFieldUnit (sourceHilbertSeed K S₀) Q b hb)
        (generatorFieldUnit (sourceHilbertSeed K S₀) P a ha) =
      finitePlaceHilbertSymbol K 6 (by norm_num) (sourceSixRoots K hζ) Q
        (generatorFieldUnit (sourceHilbertSeed K S₀) P a ha)
        (generatorFieldUnit (sourceHilbertSeed K S₀) Q b hb) := by
  apply sourceHilbert_pair_reciprocity K hζ S₀ P Q hPQ hP hQ _ _ haB hbB
  intro v hv hvP hvQ
  exact ⟨exterior_generator_other_valuation (sourceHilbertSeed K S₀) P a ha v hv hvP,
    exterior_generator_other_valuation (sourceHilbertSeed K S₀) Q b hb v hv hvQ⟩

end
end ArtinMatthews.SIntegerAllowedReciprocity

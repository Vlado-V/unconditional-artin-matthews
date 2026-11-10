module

public import ArtinMatthews.SixthPrincipalRowOrbit
public import ArtinMatthews.SixthKummerSharpModulus
public import ArtinMatthews.SixthKummerSharpRows
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Normalization retains every indexing ideal, sharp modulus, and
Kummer character. Finite row aggregation is transported by the explicit
root permutation, not by an assumed probe identity. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain VaryingKummerAnalytic
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable {K : Type} [Field K] [NumberField K]

def exteriorRootProfile (S : Finset (HeightOneSpectrum (𝓞 K))) (r : Kˣ) :
    {p : HeightOneSpectrum (𝓞 K) // p ∉ S} → ℤ :=
  fun p => exteriorPrincipalValuation p.1 r

theorem principalRowIntegralRootChange_profile (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (r : ExteriorIntegralRoot S) :
    exteriorRootProfile S (principalRowIntegralRootChange S hS r).1 = exteriorRootProfile S r.1 := by
  funext p
  exact principalRowRootChange_valuation S hS r.1 p.1 p.2

theorem principalRowIntegralOrbit_profile_tsum (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (i : ExteriorIdealRowIndex S N)
    (W : ({p : HeightOneSpectrum (𝓞 K) // p ∉ S} → ℤ) → ℂ) (F : Kˣ → ℂ) :
    (∑' r : ExteriorIntegralRoot S,
      W (exteriorRootProfile S r.1)*F (exteriorBoundedIdealRowUnit S N i*r.1^6)) =
      ∑' r : ExteriorIntegralRoot S,
        W (exteriorRootProfile S r.1)*F (normalizedExteriorIdealRowUnit S hS N i*r.1^6) := by
  calc
    _ = ∑' r : ExteriorIntegralRoot S,
        W (exteriorRootProfile S (principalRowIntegralRootChange S hS r).1)*
          F (normalizedExteriorIdealRowUnit S hS N i*(principalRowIntegralRootChange S hS r).1^6) := by
      apply tsum_congr
      intro r
      rw [principalRowIntegralRootChange_profile,principalRowIntegralOrbit_reparam]
    _ = _ := (principalRowIntegralRootChange S hS).tsum_eq
      (fun r : ExteriorIntegralRoot S => W (exteriorRootProfile S r.1)*
        F (normalizedExteriorIdealRowUnit S hS N i*r.1^6))

theorem normalizedRow_weighted_profile_orbit_sum (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ)
    (T : Finset (ExteriorIdealRowIndex S N)) (w : ExteriorIdealRowIndex S N → ℂ)
    (W : ExteriorIdealRowIndex S N → ({p : HeightOneSpectrum (𝓞 K) // p ∉ S} → ℤ) → ℂ)
    (F : ExteriorIdealRowIndex S N → Kˣ → ℂ) :
    (∑ i ∈ T, w i * ∑' r : ExteriorIntegralRoot S,
      W i (exteriorRootProfile S r.1)*F i (exteriorBoundedIdealRowUnit S N i*r.1^6)) =
      ∑ i ∈ T, w i * ∑' r : ExteriorIntegralRoot S,
        W i (exteriorRootProfile S r.1)*F i (normalizedExteriorIdealRowUnit S hS N i*r.1^6) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [principalRowIntegralOrbit_profile_tsum]

theorem normalizedExteriorIdealRow_radicalPrimes (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (i : ExteriorIdealRowIndex S N) :
    sixthExteriorRadicalPrimes S (normalizedExteriorIdealRowUnit S hS N i) =
      sixthExteriorRadicalPrimes S (exteriorBoundedIdealRowUnit S N i) := by
  ext p
  rw [mem_sixthExteriorRadicalPrimes,mem_sixthExteriorRadicalPrimes]
  by_cases hp : p ∉ S
  · rw [normalizedExteriorIdealRowUnit_valuation S hS N i p hp]
  · simp only [hp,false_and]

theorem normalizedExteriorIdealRow_sharpIdeal (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (i : ExteriorIdealRowIndex S N) :
    sixthKummerSharpIdeal S (normalizedExteriorIdealRowUnit S hS N i) =
      sixthKummerSharpIdeal S (exteriorBoundedIdealRowUnit S N i) := by
  unfold sixthKummerSharpIdeal sixthExteriorRadicalIdeal
  rw [normalizedExteriorIdealRow_radicalPrimes]

theorem normalizedExteriorIdealRow_radical_norm_le (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (i : ExteriorIdealRowIndex S N) :
    (sixthExteriorRadicalIdeal S (normalizedExteriorIdealRowUnit S hS N i)).absNorm ≤ N := by
  unfold sixthExteriorRadicalIdeal
  rw [normalizedExteriorIdealRow_radicalPrimes]
  exact exteriorBoundedIdealRow_radical_norm_le S hS N i

theorem normalizedPrincipalRow_ideal_norm (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (hN : 1 ≤ N) :
    (normalizedPrincipalRowIndex S hS N hN).1.val.absNorm = 1 := by
  change Ideal.absNorm (1 : Ideal (𝓞 K)) = 1
  exact map_one _

theorem normalizedRow_weighted_orbit_sum (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ)
    (T : Finset (ExteriorIdealRowIndex S N)) (w : ExteriorIdealRowIndex S N → ℂ)
    (F : ExteriorIdealRowIndex S N → Kˣ → ℂ) :
    (∑ i ∈ T, w i * ∑' r : ExteriorIntegralRoot S,
      F i (exteriorBoundedIdealRowUnit S N i*r.1^6)) =
      ∑ i ∈ T, w i * ∑' r : ExteriorIntegralRoot S,
        F i (normalizedExteriorIdealRowUnit S hS N i*r.1^6) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [principalRowIntegralOrbit_tsum S hS N i]

theorem normalizedPrincipalRow_orbit_sum (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (hN : 1 ≤ N) (F : Kˣ → ℂ) :
    (∑' r : ExteriorIntegralRoot S,
      F (exteriorBoundedIdealRowUnit S N (normalizedPrincipalRowIndex S hS N hN)*r.1^6)) =
      ∑' r : ExteriorIntegralRoot S, F (r.1^6) := by
  rw [principalRowIntegralOrbit_tsum S hS N (normalizedPrincipalRowIndex S hS N hN)]
  simp only [normalizedExteriorIdealRowUnit_principal,one_mul]

theorem normalizedExteriorIdealRow_ratio (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (i : ExteriorIdealRowIndex S N) :
    exteriorBoundedIdealRowUnit S N i / normalizedExteriorIdealRowUnit S hS N i =
      ((principalRowNormalizer S hS).root : Kˣ)^6 := by
  change exteriorBoundedIdealRowUnit S N i /
    (exteriorBoundedIdealRowUnit S N i / ((principalRowNormalizer S hS).root : Kˣ)^6) = _
  simp only [div_div_self']

def normalizedRowComparisonParameters (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) : Finset K :=
  sixthUnitRowParameters (exteriorBoundedIdealRowUnits S N ∪ normalizedExteriorIdealRowUnits S hS N)

theorem originalRow_mem_comparison (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (i : ExteriorIdealRowIndex S N) :
    (exteriorBoundedIdealRowUnit S N i : K) ∈ normalizedRowComparisonParameters S hS N :=
  Finset.mem_image.mpr ⟨_,Finset.mem_union_left _ (exteriorBoundedIdealRowUnit_mem S N i),rfl⟩

theorem normalizedRow_mem_comparison (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (i : ExteriorIdealRowIndex S N) :
    (normalizedExteriorIdealRowUnit S hS N i : K) ∈ normalizedRowComparisonParameters S hS N :=
  Finset.mem_image.mpr ⟨_,Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩),rfl⟩

variable [Algebra K ℂ]

theorem normalizedRow_comparison_character {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : exteriorPrincipalizingPrimes K ⊆ S)
    (N : ℕ) (i : ExteriorIdealRowIndex S N) :
    sixthKummerRowCharacter hζ (normalizedRowComparisonParameters S hS N)
      (exteriorBoundedIdealRowUnit S N i : K) (originalRow_mem_comparison S hS N i) (Units.ne_zero _) =
    sixthKummerRowCharacter hζ (normalizedRowComparisonParameters S hS N)
      (normalizedExteriorIdealRowUnit S hS N i : K) (normalizedRow_mem_comparison S hS N i)
      (Units.ne_zero _) := by
  apply (sixthKummerRowCharacter_eq_iff_exists_sixthPower hζ _ _ _ _ _ _ _).mpr
  refine ⟨((principalRowNormalizer S hS).root : Kˣ),?_⟩
  simpa only [Units.val_div_eq_div_val,Units.val_pow_eq_pow_val] using
    (congrArg (fun u : Kˣ => (u : K)) (normalizedExteriorIdealRow_ratio S hS N i)).symm

theorem normalizedPrincipalRow_comparison_character_one {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : exteriorPrincipalizingPrimes K ⊆ S)
    (N : ℕ) (hN : 1 ≤ N) :
    sixthKummerRowCharacter hζ (normalizedRowComparisonParameters S hS N)
      (normalizedExteriorIdealRowUnit S hS N (normalizedPrincipalRowIndex S hS N hN) : K)
      (normalizedRow_mem_comparison S hS N _) (Units.ne_zero _) = 1 := by
  apply (sixthKummerRowCharacter_one_iff_exists_sixthPower hζ _ _ _ _).mpr
  exact ⟨1,by simp only [normalizedExteriorIdealRowUnit_principal,Units.val_one,one_pow]⟩

theorem normalizedOtherRow_comparison_character_ne_one {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : exteriorPrincipalizingPrimes K ⊆ S)
    (N : ℕ) (hN : 1 ≤ N) (i : ExteriorIdealRowIndex S N)
    (hi : i ≠ normalizedPrincipalRowIndex S hS N hN) :
    sixthKummerRowCharacter hζ (normalizedRowComparisonParameters S hS N)
      (normalizedExteriorIdealRowUnit S hS N i : K) (normalizedRow_mem_comparison S hS N i)
      (Units.ne_zero _) ≠ 1 := by
  intro h
  exact normalizedExteriorIdealRow_other_not_sixthPower S hS N hN i hi
    ((sixthKummerRowCharacter_one_iff_exists_sixthPower hζ _ _ _ _).mp h)

variable [NumberField.IsTotallyComplex K]

theorem normalizedRow_comparison_coefficient {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : exteriorPrincipalizingPrimes K ⊆ S)
    (N : ℕ) (i : ExteriorIdealRowIndex S N) :
    (sixthKummerRowRayCharacter hζ (normalizedRowComparisonParameters S hS N)
      (exteriorBoundedIdealRowUnit S N i : K) (originalRow_mem_comparison S hS N i) (Units.ne_zero _)).coefficient =
    (sixthKummerRowRayCharacter hζ (normalizedRowComparisonParameters S hS N)
      (normalizedExteriorIdealRowUnit S hS N i : K) (normalizedRow_mem_comparison S hS N i)
      (Units.ne_zero _)).coefficient := by
  let := sixthKummerRowField_isAbelianGalois hζ (normalizedRowComparisonParameters S hS N)
  exact congrArg (fun χ => (ArtinRay.discriminantDegreeRayCharacter χ).coefficient)
    (normalizedRow_comparison_character hζ S hS N i)

end
end ArtinMatthews

module

public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.PowerResidueReciprocity


set_option backward.privateInPublic true
@[expose] public section

/-! Reciprocity derived from the actual global Hilbert product formula.

The subgroup hypothesis is isotropy for the actual product of the infinite
and S-local symbols. No construction of a complementary isotropic subgroup
is asserted here. The integral statement does not assert an S-integer
standard-character comparison. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField KummerTheory GlobalClassFieldTheory.Reciprocity
open IsDedekindDomain
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped NumberField BigOperators Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

def probeHilbertSProduct (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a b : Kˣ) :
    nthRootsSubgroup K (n : ℕ) :=
  (∏ v : InfinitePlace K, infinitePlaceHilbertSymbol K n v a b) *
    ∏ v ∈ S, finitePlaceHilbertSymbol K n hnK hmu v a b

def ProbeHilbertSIsotropic (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (B : Subgroup Kˣ) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, probeHilbertSProduct K n hnK hmu S a b = 1

theorem probeHilbert_pair_product_integral (n : ℕ+)
    (hnK : ((n : ℕ) : K) ≠ 0) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : powerResidueExponentFinitePlaces K n ⊆ S)
    (B : Subgroup Kˣ) (hB : ProbeHilbertSIsotropic K n hnK hmu S B)
    (P Q : HeightOneSpectrum (𝓞 K)) (hPQ : P ≠ Q) (hP : P ∉ S) (hQ : Q ∉ S)
    (a b : 𝓞 K) (ha : a ≠ 0) (hb : b ≠ 0)
    (haB : nonzeroIntegralFieldUnit K a ha ∈ B)
    (hbB : nonzeroIntegralFieldUnit K b hb ∈ B)
    (hout : ∀ v, v ∉ S → v ≠ P → v ≠ Q → a ∉ v.asIdeal ∧ b ∉ v.asIdeal) :
    finitePlaceHilbertSymbol K n hnK hmu P
        (nonzeroIntegralFieldUnit K a ha) (nonzeroIntegralFieldUnit K b hb) *
      finitePlaceHilbertSymbol K n hnK hmu Q
        (nonzeroIntegralFieldUnit K a ha) (nonzeroIntegralFieldUnit K b hb) = 1 := by
  let H := fun v : HeightOneSpectrum (𝓞 K) => finitePlaceHilbertSymbol K n hnK hmu v
    (nonzeroIntegralFieldUnit K a ha) (nonzeroIntegralFieldUnit K b hb)
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
      apply hnot
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr he)))
    have hvn : v ∉ powerResidueExponentFinitePlaces K n := fun he => hvS (hS he)
    obtain ⟨hav, hbv⟩ := hout v hvS hvP hvQ
    exact hv (finitePlaceHilbertSymbol_integral_units_eq_one K n hnK hmu v hvn a b ha hb hav hbv)
  have hall := hilbertSymbol_allPlaces_product_eq_one K n hnK hmu
    (nonzeroIntegralFieldUnit K a ha) (nonzeroIntegralFieldUnit K b hb)
  change (∏ v : InfinitePlace K, infinitePlaceHilbertSymbol K n v
    (nonzeroIntegralFieldUnit K a ha) (nonzeroIntegralFieldUnit K b hb)) * ∏ᶠ v, H v = 1 at hall
  rw [finprod_eq_prod_of_mulSupport_subset H hsupp,
    Finset.prod_insert (by simp only [Finset.mem_insert, hPQ, hP, or_self, not_false_eq_true]),
    Finset.prod_insert hQ] at hall
  have hiso := hB _ haB _ hbB
  unfold probeHilbertSProduct at hiso
  change (∏ v : InfinitePlace K, infinitePlaceHilbertSymbol K n v
    (nonzeroIntegralFieldUnit K a ha) (nonzeroIntegralFieldUnit K b hb)) * ∏ v ∈ S, H v = 1 at hiso
  calc
    H P * H Q = (H P * H Q) * 1 := (mul_one _).symm
    _ = (H P * H Q) * ((∏ v : InfinitePlace K, infinitePlaceHilbertSymbol K n v
        (nonzeroIntegralFieldUnit K a ha) (nonzeroIntegralFieldUnit K b hb)) * ∏ v ∈ S, H v) := by rw [hiso]
    _ = 1 := by simpa only [mul_assoc, mul_left_comm, mul_comm] using hall

theorem probeHilbert_pair_reciprocity_integral (n : ℕ+)
    (hnK : ((n : ℕ) : K) ≠ 0) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : powerResidueExponentFinitePlaces K n ⊆ S)
    (B : Subgroup Kˣ) (hB : ProbeHilbertSIsotropic K n hnK hmu S B)
    (P Q : HeightOneSpectrum (𝓞 K)) (hPQ : P ≠ Q) (hP : P ∉ S) (hQ : Q ∉ S)
    (a b : 𝓞 K) (ha : a ≠ 0) (hb : b ≠ 0)
    (haB : nonzeroIntegralFieldUnit K a ha ∈ B)
    (hbB : nonzeroIntegralFieldUnit K b hb ∈ B)
    (hout : ∀ v, v ∉ S → v ≠ P → v ≠ Q → a ∉ v.asIdeal ∧ b ∉ v.asIdeal) :
    finitePlaceHilbertSymbol K n hnK hmu P
        (nonzeroIntegralFieldUnit K b hb) (nonzeroIntegralFieldUnit K a ha) =
      finitePlaceHilbertSymbol K n hnK hmu Q
        (nonzeroIntegralFieldUnit K a ha) (nonzeroIntegralFieldUnit K b hb) := by
  have hp := probeHilbert_pair_product_integral K n hnK hmu S hS B hB P Q hPQ hP hQ
    a b ha hb haB hbB hout
  have hsk := finitePlaceHilbertSymbol_skew K n hnK hmu P
    (nonzeroIntegralFieldUnit K a ha) (nonzeroIntegralFieldUnit K b hb)
  rw [hsk, inv_mul_eq_one] at hp
  exact hp

theorem probePrimeResidue_reciprocity_integral (n : ℕ+)
    (hnK : ((n : ℕ) : K) ≠ 0) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : powerResidueExponentFinitePlaces K n ⊆ S)
    (B : Subgroup Kˣ) (hB : ProbeHilbertSIsotropic K n hnK hmu S B)
    (P Q : HeightOneSpectrum (𝓞 K)) (hPQ : P ≠ Q) (hP : P ∉ S) (hQ : Q ∉ S)
    (hPN : (Ideal.absNorm P.asIdeal).Coprime (n : ℕ))
    (hQN : (Ideal.absNorm Q.asIdeal).Coprime (n : ℕ))
    (a b : 𝓞 K) (ha : a ≠ 0) (hb : b ≠ 0)
    (haB : nonzeroIntegralFieldUnit K a ha ∈ B)
    (hbB : nonzeroIntegralFieldUnit K b hb ∈ B)
    (hbP : b ∉ P.asIdeal) (haQ : a ∉ Q.asIdeal)
    (haP : idealPrimeMultiplicity K P (Ideal.span {a}) = 1)
    (hbQ : idealPrimeMultiplicity K Q (Ideal.span {b}) = 1)
    (hout : ∀ v, v ∉ S → v ≠ P → v ≠ Q → a ∉ v.asIdeal ∧ b ∉ v.asIdeal) :
    primeIdealPowerResidueSymbol K P n hmu hPN b hbP =
      primeIdealPowerResidueSymbol K Q n hmu hQN a haQ := by
  have hp := probeHilbert_pair_reciprocity_integral K n hnK hmu S hS B hB P Q hPQ hP hQ
    a b ha hb haB hbB hout
  have hPexp : P ∉ powerResidueExponentFinitePlaces K n := fun he => hP (hS he)
  have hQexp : Q ∉ powerResidueExponentFinitePlaces K n := fun he => hQ (hS he)
  rw [finitePlaceHilbertSymbol_integral_eq_primeIdealPowerResidueFactor K n hnK hmu P hPexp hPN
      b a hb ha hbP,
    finitePlaceHilbertSymbol_integral_eq_primeIdealPowerResidueFactor K n hnK hmu Q hQexp hQN
      a b ha hb haQ, haP, hbQ, pow_one, pow_one] at hp
  exact integralRootsOfUnityToNthRoots_injective K (n : ℕ) hp

end
end ArtinMatthews.VaryingKummerAnalytic

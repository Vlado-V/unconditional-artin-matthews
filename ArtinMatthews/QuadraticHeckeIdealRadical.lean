module

public import ArtinMatthews.QuadraticHeckeSmallResidue
public import ArtinMatthews.QuadraticHeckeMaskedCutoff
public import Mathlib.RingTheory.Radical.Basic


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField VaryingKummerAnalytic UniqueFactorizationMonoid
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
open HeckeIdealMobius (divisors primeSupport)

/-- The squarefree product of the prime ideal support of an integral ideal. -/
def quadraticHeckeIdealRadical (m : Ideal (𝓞 F)) : Ideal (𝓞 F) :=
  UniqueFactorizationMonoid.radical m

theorem quadraticHeckeIdealRadical_squarefree (m : Ideal (𝓞 F)) :
    Squarefree (quadraticHeckeIdealRadical F m) :=
  UniqueFactorizationMonoid.squarefree_radical

theorem quadraticHeckeIdealRadical_ne_bot (m : Ideal (𝓞 F)) :
    quadraticHeckeIdealRadical F m ≠ ⊥ :=
  UniqueFactorizationMonoid.radical_ne_zero

theorem quadraticHeckeIdealRadical_dvd (m : Ideal (𝓞 F)) :
    quadraticHeckeIdealRadical F m ∣ m :=
  UniqueFactorizationMonoid.radical_dvd_self

theorem quadraticHeckeIdealRadical_primeSupport (m : Ideal (𝓞 F)) :
    primeSupport F (quadraticHeckeIdealRadical F m) = primeSupport F m := by
  change UniqueFactorizationMonoid.primeFactors (UniqueFactorizationMonoid.radical m) =
    UniqueFactorizationMonoid.primeFactors m
  exact UniqueFactorizationMonoid.primeFactors_radical

theorem quadraticHeckeIdealRadical_eq_self {m : Ideal (𝓞 F)} (hm : Squarefree m) :
    quadraticHeckeIdealRadical F m = m := by
  change (∏ P ∈ primeSupport F m, P) = m
  exact HeckeIdealMobius.squarefree_support_product_self F hm

theorem quadraticHeckeIdealRadical_mul {a b : Ideal (𝓞 F)} (hab : IsCoprime a b) :
    quadraticHeckeIdealRadical F (a * b) =
      quadraticHeckeIdealRadical F a * quadraticHeckeIdealRadical F b :=
  UniqueFactorizationMonoid.radical_mul hab.isRelPrime

theorem quadraticHeckeIdealRadical_norm_le {m : Ideal (𝓞 F)} (hm : m ≠ ⊥) :
    Ideal.absNorm (quadraticHeckeIdealRadical F m) ≤ Ideal.absNorm m := by
  exact Nat.le_of_dvd
    (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hm))
    (map_dvd Ideal.absNorm (quadraticHeckeIdealRadical_dvd F m))

private theorem ideal_coprime_iff_relPrime (a b : Ideal (𝓞 F)) :
    IsCoprime a b ↔ IsRelPrime a b := by
  rw [Ideal.isCoprime_iff_gcd, ← gcd_isUnit_iff_isRelPrime, Ideal.isUnit_iff, Ideal.one_eq_top]

/-- Passing to the squarefree ideal radical preserves the full coprimality mask. -/
theorem quadraticHeckeIdealRadical_coprime_iff {m : Ideal (𝓞 F)} (hm : m ≠ ⊥)
    (J : Ideal (𝓞 F)) :
    IsCoprime J (quadraticHeckeIdealRadical F m) ↔ IsCoprime J m := by
  constructor
  · intro h
    have hr := h.symm.isRelPrime
    have hrel : IsRelPrime m J := by
      apply (isRelPrime_iff_no_prime_factors hm).2
      intro p hpm hpJ hp
      have hpr : p ∣ quadraticHeckeIdealRadical F m :=
        (UniqueFactorizationMonoid.dvd_radical_iff_of_irreducible hp.irreducible hm).2 hpm
      exact hp.not_isUnit (hr hpr hpJ)
    exact ((ideal_coprime_iff_relPrime F m J).2 hrel).symm
  · intro h
    exact h.of_isCoprime_of_dvd_right (quadraticHeckeIdealRadical_dvd F m)

/-- Divisors of the ideal radical are precisely the squarefree divisors. -/
theorem quadraticHeckeIdealRadical_divisors {m : Ideal (𝓞 F)} (hm : m ≠ ⊥) :
    divisors F (quadraticHeckeIdealRadical F m) = (divisors F m).filter Squarefree := by
  ext d
  simp only [HeckeIdealMobius.mem_divisors F (quadraticHeckeIdealRadical_ne_bot F m),
    Finset.mem_filter, HeckeIdealMobius.mem_divisors F hm]
  constructor
  · intro hd
    exact ⟨hd.trans (quadraticHeckeIdealRadical_dvd F m),
      (quadraticHeckeIdealRadical_squarefree F m).squarefree_of_dvd hd⟩
  · rintro ⟨hd, hsf⟩
    exact (UniqueFactorizationMonoid.dvd_radical_iff hsf.isRadical hm).2 hd

/-- Every finite Möbius-weighted ideal test sum is invariant under taking the radical. -/
theorem quadraticHeckeIdealRadical_moebius_sum {m : Ideal (𝓞 F)} (hm : m ≠ ⊥)
    (f : Ideal (𝓞 F) → ℂ) :
    (∑ d ∈ divisors F m, (moebius d : ℂ) * f d) =
      ∑ d ∈ divisors F (quadraticHeckeIdealRadical F m), (moebius d : ℂ) * f d := by
  rw [quadraticHeckeIdealRadical_divisors F hm]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro d hd hnot
  have hsf : ¬ Squarefree d := fun h => hnot (Finset.mem_filter.mpr ⟨hd, h⟩)
  rw [moebius_of_not_squarefree hsf, Int.cast_zero, zero_mul]

theorem quadraticHeckeIdealRadical_density (m : Ideal (𝓞 F)) :
    quadraticHeckeCoprimeDensity F (quadraticHeckeIdealRadical F m) =
      quadraticHeckeCoprimeDensity F m := by
  unfold quadraticHeckeCoprimeDensity
  rw [quadraticHeckeIdealRadical_primeSupport]

theorem quadraticHeckeIdealRadical_coprimeCutoff {m : Ideal (𝓞 F)} (hm : m ≠ ⊥) (H : ℝ) :
    quadraticHeckeCoprimeCutoff F (quadraticHeckeIdealRadical F m) H =
      quadraticHeckeCoprimeCutoff F m H := by
  ext J
  simp only [mem_quadraticHeckeCoprimeCutoff, quadraticHeckeIdealRadical_coprime_iff F hm]

/-- Multiplication of moduli retains both coprimality conditions in the finite cutoff. -/
theorem quadraticHeckeCoprimeCutoff_mul (a b : Ideal (𝓞 F)) (H : ℝ) :
    quadraticHeckeCoprimeCutoff F (a * b) H =
      (quadraticHeckeCoprimeCutoff F b H).filter (fun J => IsCoprime J a) := by
  ext J
  simp only [mem_quadraticHeckeCoprimeCutoff, Finset.mem_filter, IsCoprime.mul_right_iff]
  tauto

/-- The exact unmasked cutoff cancellation applies to any nonzero finite modulus via its radical. -/
theorem quadraticHeckeMainTerm_radicalCutoffGrouped {N : Ideal (𝓞 F)}
    (ψ : EvenIdealRayCharacter F N)
    (hχ : ∀ J : Ideal (𝓞 F), J ≠ ⊥ → IsCoprime J N → ψ.allCoefficient J ^ 2 = 1)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (hmN : IsCoprime m N) (H : ℝ) :
    (∑ a ∈ quadraticHeckeSquarefreeCutoff F H, quadraticHeckeHalfCoefficient F ψ a) *
        (∑ d ∈ divisors F m, (moebius d : ℂ) * quadraticHeckeHalfCoefficient F ψ d) -
      (∑ a ∈ quadraticHeckeCoprimeCutoff F m H, quadraticHeckeHalfCoefficient F ψ a) *
        quadraticHeckeCoprimeDensity F m =
      ∑ B ∈ quadraticHeckeCutoffAnnulus F (quadraticHeckeIdealRadical F m) H,
        quadraticHeckeCutoffCoefficient F (quadraticHeckeIdealRadical F m) H B *
          quadraticHeckeHalfCoefficient F ψ B := by
  have h := quadraticHeckeMainTerm_cutoffGrouped F ψ hχ (quadraticHeckeIdealRadical F m)
    (quadraticHeckeIdealRadical_squarefree F m)
    (hmN.of_isCoprime_of_dvd_left (quadraticHeckeIdealRadical_dvd F m)) H
  rw [quadraticHeckeIdealRadical_coprimeCutoff F hm,
    quadraticHeckeIdealRadical_density F m] at h
  rw [quadraticHeckeIdealRadical_moebius_sum F hm (quadraticHeckeHalfCoefficient F ψ)]
  exact h

/-- The radical cutoff discrepancy retains the small row and both literal divisor weights. -/
theorem quadraticHeckeMainTerm_radicalCutoffTail {N : Ideal (𝓞 F)}
    (ψ : EvenIdealRayCharacter F N)
    (hχ : ∀ J : Ideal (𝓞 F), J ≠ ⊥ → IsCoprime J N → ψ.allCoefficient J ^ 2 = 1)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (hmN : IsCoprime m N) (H : ℝ) :
    (∑ a ∈ quadraticHeckeSquarefreeCutoff F H, quadraticHeckeHalfCoefficient F ψ a) *
        (∑ d ∈ divisors F m, (moebius d : ℂ) * quadraticHeckeHalfCoefficient F ψ d) -
      (∑ a ∈ quadraticHeckeCoprimeCutoff F m H, quadraticHeckeHalfCoefficient F ψ a) *
        quadraticHeckeCoprimeDensity F m =
      ∑ d ∈ divisors F (quadraticHeckeIdealRadical F m),
        ∑ e ∈ divisors F (quadraticHeckeIdealRadical F m),
          ∑ h ∈ quadraticHeckeCoprimeCutoff F (quadraticHeckeIdealRadical F m) H,
            quadraticHeckeCutoffWeight F H h d e * ψ.allCoefficient (h * d * e) := by
  have h := quadraticHeckeMainTerm_cutoffTail F ψ hχ (quadraticHeckeIdealRadical F m)
    (quadraticHeckeIdealRadical_squarefree F m)
    (hmN.of_isCoprime_of_dvd_left (quadraticHeckeIdealRadical_dvd F m)) H
  rw [quadraticHeckeIdealRadical_coprimeCutoff F hm,
    quadraticHeckeIdealRadical_density F m] at h
  rw [quadraticHeckeIdealRadical_moebius_sum F hm (quadraticHeckeHalfCoefficient F ψ), h]
  simp_rw [quadraticHeckeCutoffTail_summand]
  rw [← quadraticHeckeIdealRadical_coprimeCutoff F hm, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]

end
end ArtinMatthews

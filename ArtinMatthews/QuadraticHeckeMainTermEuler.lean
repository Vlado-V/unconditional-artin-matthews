module

public import ArtinMatthews.VaryingKummerAnalyticHeckeFiniteEulerAlgebra


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Complex VaryingKummerAnalytic UniqueFactorizationMonoid
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
open HeckeIdealMobius (divisors primeSupport)

/-- The normalized Euler density of ideals coprime to a finite modulus. -/
def quadraticHeckeCoprimeDensity (a : Ideal (𝓞 K)) : ℂ :=
  ∏ P ∈ primeSupport K a, (1 - (Ideal.absNorm P : ℂ)⁻¹)

/-- The multiplicative coefficient χ(a)/(Na)^(1/2) in the main term. -/
def quadraticHeckeHalfCoefficient {M : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K M) :
    Ideal (𝓞 K) →*₀ ℂ :=
  ψ.coefficientHom *
    (riemannZetaSummandHom (s := (1 / 2 : ℂ)) (by norm_num)).comp Ideal.absNorm

theorem quadraticHeckeHalfCoefficient_apply {M : Ideal (𝓞 K)}
    (ψ : EvenIdealRayCharacter K M) (J : Ideal (𝓞 K)) :
    quadraticHeckeHalfCoefficient K ψ J =
      ψ.allCoefficient J * (Ideal.absNorm J : ℂ) ^ (-(1 / 2 : ℂ)) := rfl

private theorem sum_squarefree_divisors (a : Ideal (𝓞 K)) (ha : Squarefree a)
    (A : Ideal (𝓞 K) →*₀ ℂ) :
    (∑ d ∈ divisors K a, A d) = ∏ P ∈ primeSupport K a, (1 + A P) := by
  have hfilter : (divisors K a).filter Squarefree = divisors K a := by
    apply Finset.filter_eq_self.mpr
    intro d hd
    exact ha.squarefree_of_dvd ((HeckeIdealMobius.mem_divisors K ha.ne_zero).1 hd)
  rw [← hfilter, HeckeIdealMobius.squarefree_divisors_eq_image K a ha.ne_zero, Finset.sum_image]
  · simp only [map_prod, Finset.prod_one_add]
  · intro S hS T hT he
    exact HeckeIdealMobius.support_product_injective K (Finset.mem_powerset.mp hS)
      (Finset.mem_powerset.mp hT) he

private theorem primeSupport_mul_of_nonzero {a b : Ideal (𝓞 K)}
    (ha : a ≠ ⊥) (hb : b ≠ ⊥) :
    primeSupport K (a * b) = primeSupport K a ∪ primeSupport K b := by
  ext P
  simp only [primeSupport, normalizedFactors_mul ha hb, Multiset.mem_toFinset,
    Finset.mem_union, Multiset.mem_add]

private theorem primeSupport_disjoint {a b : Ideal (𝓞 K)} (hab : IsCoprime a b) :
    Disjoint (primeSupport K a) (primeSupport K b) := by
  apply Finset.disjoint_left.mpr
  intro P ha hb
  exact (HeckeIdealMobius.support_prime K ha).not_isUnit
    (hab.isUnit_of_dvd' (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp ha))
      (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hb)))

private theorem halfCoefficient_sq {M : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K M)
    (hχ : ∀ J : Ideal (𝓞 K), J ≠ ⊥ → IsCoprime J M → ψ.allCoefficient J ^ 2 = 1)
    {P : Ideal (𝓞 K)} (hP : P ≠ ⊥) (hPM : IsCoprime P M) :
    quadraticHeckeHalfCoefficient K ψ P ^ 2 = (Ideal.absNorm P : ℂ)⁻¹ := by
  have hn : (Ideal.absNorm P : ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hP
  rw [quadraticHeckeHalfCoefficient_apply, mul_pow, hχ P hP hPM, one_mul, pow_two,
    ← Complex.cpow_add _ _ hn]
  rw [show (-(1 / 2 : ℂ)) + -(1 / 2 : ℂ) = -1 by ring, Complex.cpow_neg_one]

/-- The exact local cancellation factor in (7.2), with the finite wild
modulus disjoint from the exterior conductor. -/
theorem quadraticHeckeMainTermEuler {M : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K M)
    (hχ : ∀ J : Ideal (𝓞 K), J ≠ ⊥ → IsCoprime J M → ψ.allCoefficient J ^ 2 = 1)
    (a g : Ideal (𝓞 K)) (ha : Squarefree a) (hg : g ≠ ⊥)
    (hag : IsCoprime a g) (haM : IsCoprime a M) :
    (∑ d ∈ divisors K a, ∑ e ∈ divisors K (a * g),
      (moebius e : ℂ) * quadraticHeckeHalfCoefficient K ψ (d * e)) =
      quadraticHeckeCoprimeDensity K a *
        ∑ e ∈ divisors K g, (moebius e : ℂ) * quadraticHeckeHalfCoefficient K ψ e := by
  let A := quadraticHeckeHalfCoefficient K ψ
  have he (d : Ideal (𝓞 K)) :
      (∑ e ∈ divisors K (a * g), (moebius e : ℂ) * A (d * e)) =
        A d * (∑ e ∈ divisors K (a * g), (moebius e : ℂ) * A e) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [map_mul]
    ring
  change (∑ d ∈ divisors K a, ∑ e ∈ divisors K (a * g), (moebius e : ℂ) * A (d * e)) =
    quadraticHeckeCoprimeDensity K a * ∑ e ∈ divisors K g, (moebius e : ℂ) * A e
  simp_rw [he]
  rw [← Finset.sum_mul, sum_squarefree_divisors K a ha A,
    ← HeckeIdealMobius.prime_product_eq_moebius_sum K (a * g) (mul_ne_zero ha.ne_zero hg) A,
    ← HeckeIdealMobius.prime_product_eq_moebius_sum K g hg A,
    primeSupport_mul_of_nonzero K ha.ne_zero hg,
    Finset.prod_union (primeSupport_disjoint K hag), ← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro P hP
  have hne := (HeckeIdealMobius.support_prime K hP).ne_zero
  have hd := dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP)
  have hsq := halfCoefficient_sq K ψ hχ hne (haM.of_isCoprime_of_dvd_left hd)
  change (1 + A P) * (1 - A P) = 1 - (Ideal.absNorm P : ℂ)⁻¹
  calc
    _ = 1 - A P ^ 2 := by ring
    _ = _ := by rw [show A P ^ 2 = _ from hsq]

end
end ArtinMatthews

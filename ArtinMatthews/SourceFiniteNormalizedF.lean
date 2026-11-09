module

public import ArtinMatthews.SourceLocalNormalizedCoefficient
public import ArtinMatthews.SourceFamilyCofactorPhase


set_option backward.privateInPublic true
@[expose] public section

/-! Actual finite-F factorization into literal C coefficients with every
CRT unit multiplier retained. Local unit cofactors may be constructed
from exact ideal-power order; no local phase or value table is assumed. -/
namespace ArtinMatthews.SourceCRTNormalization

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.SIntegerFourier
open scoped NumberField Classical BigOperators
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def sourceFamilyUnitFactor (P : ι → HeightOneSpectrum (𝓞 K))
    (hP : Pairwise fun i j => P i ≠ P j) (hS : ∀ i, P i ∉ principalizingSet S₀)
    (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (χ : ∀ i, MulChar ((𝓞 K) ⧸ (P i).asIdeal) ℂ) (k t : ι → ℕ) (hp : ι → PrincipalIntegerRing S₀)
    (hhp : ∀ i, hp i ∉ (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) (i : ι) : ℂ :=
  sourceLocalUnitFactor S₀ (P i) (hS i) (a i) (ha i) (χ i) (k i) (t i)
    (sourcePrimeCofactor S₀ a k i) (sourcePrimeCofactor S₀ a t i) (hp i)
    (sourcePrimeCofactor_not_mem S₀ P hP hS a ha k i)
    (sourcePrimeCofactor_not_mem S₀ P hP hS a ha t i) (hhp i)

theorem sourceSexticFiniteF_normalized (P : ι → HeightOneSpectrum (𝓞 K))
    (hP : Pairwise fun i j => P i ≠ P j) (hS : ∀ i, P i ∉ principalizingSet S₀)
    (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (χ : ∀ i, MulChar ((𝓞 K) ⧸ (P i).asIdeal) ℂ) (k t J : ι → ℕ)
    (H : PrincipalIntegerRing S₀) (hp : ι → PrincipalIntegerRing S₀)
    (hH : ∀ i, H = a i ^ J i * hp i)
    (hhp : ∀ i, hp i ∉ (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) :
    sourceFiniteF S₀ (∏ i, a i ^ k i) (∏ i, a i ^ t i) H
      (sourceSexticWeight S₀ P hS a ha χ k) (sourceSexticWeight S₀ P hS a ha χ t) =
      ∏ i, sourceFamilyUnitFactor S₀ P hP hS a ha χ k t hp hhp i *
        standardLocalCoefficient S₀ (P i) (hS i) (a i) (ha i) (χ i) (t i) (k i) (J i) := by
  rw [sourceSexticFiniteF_kernel_factor S₀ P hP hS a ha χ k t H]
  apply Finset.prod_congr rfl
  intro i _
  rw [sourceCRTProductPhase_eq_scaled S₀ P hP hS a ha k t i]
  have hA : (∏ j, a j ^ t j) = a i ^ t i * sourcePrimeCofactor S₀ a t i :=
    (sourcePrimeCofactor_product S₀ a t i).symm
  rw [hA, hH i]
  exact sourceLocalKernel_eq_coefficient S₀ (P i) (hS i) (a i) (ha i) (χ i) (k i) (t i) (J i)
    (sourcePrimeCofactor S₀ a k i) (sourcePrimeCofactor S₀ a t i) (hp i)
    (sourcePrimeCofactor_not_mem S₀ P hP hS a ha k i)
    (sourcePrimeCofactor_not_mem S₀ P hP hS a ha t i) (hhp i)

theorem sourceSexticFiniteF_normalized_of_orders (P : ι → HeightOneSpectrum (𝓞 K))
    (hP : Pairwise fun i j => P i ≠ P j) (hS : ∀ i, P i ∉ principalizingSet S₀)
    (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (χ : ∀ i, MulChar ((𝓞 K) ⧸ (P i).asIdeal) ℂ) (k t J : ι → ℕ) (H : PrincipalIntegerRing S₀)
    (hlo : ∀ i, H ∈ primePowerIdeal S₀ (P i) (J i))
    (hhi : ∀ i, H ∉ primePowerIdeal S₀ (P i) (J i + 1)) :
    ∃ hp : ι → PrincipalIntegerRing S₀,
      ∃ hhp : ∀ i, hp i ∉ (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)),
        (∀ i, H = a i ^ J i * hp i) ∧
        sourceFiniteF S₀ (∏ i, a i ^ k i) (∏ i, a i ^ t i) H
          (sourceSexticWeight S₀ P hS a ha χ k) (sourceSexticWeight S₀ P hS a ha χ t) =
          ∏ i, sourceFamilyUnitFactor S₀ P hP hS a ha χ k t hp hhp i *
            standardLocalCoefficient S₀ (P i) (hS i) (a i) (ha i) (χ i) (t i) (k i) (J i) := by
  let hp := fun i => (source_exact_order_factor S₀ (P i) (a i) (ha i) (J i) H (hlo i) (hhi i)).choose
  have hh (i : ι) := (source_exact_order_factor S₀ (P i) (a i) (ha i) (J i) H (hlo i) (hhi i)).choose_spec
  have hhp : ∀ i, hp i ∉ (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) := fun i => (hh i).2
  have hH : ∀ i, H = a i ^ J i * hp i := fun i => (hh i).1
  exact ⟨hp, hhp, hH, sourceSexticFiniteF_normalized S₀ P hP hS a ha χ k t J H hp hH hhp⟩

end
end ArtinMatthews.SourceCRTNormalization

module

public import ArtinMatthews.SourceUnitWeightValues
public import ArtinMatthews.SourceCofactorLocalOrder
public import ArtinMatthews.SIntegerSexticReciprocity


set_option backward.privateInPublic true
@[expose] public section

/-! Directed residue-symbol factors in actual omitted prime products.
The diagonal is one and every off-diagonal unit is derived from the
actual distinct exterior generators. -/
namespace ArtinMatthews.SourceCRTNormalization

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient
open scoped NumberField Classical BigOperators
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def sourceDirectedCharacterUnit (P : ι → HeightOneSpectrum (𝓞 K))
    (hP : Pairwise fun i j => P i ≠ P j) (hS : ∀ i, P i ∉ principalizingSet S₀)
    (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (χ : ∀ i, MulChar ((𝓞 K) ⧸ (P i).asIdeal) ℂ) (i j : ι) : ℂˣ :=
  if h : i = j then 1 else
    sourceCharacterUnit S₀ (P i) (hS i) (a i) (ha i) (χ i) (a j)
      (ArtinMatthews.SIntegerTameSymbol.primeGenerator_other_avoids K S₀
        (P i) (P j) (hP h) (hS i) (a j) (ha j))

omit [Fintype ι] in
theorem sourceDirectedCharacterUnit_diag (P : ι → HeightOneSpectrum (𝓞 K))
    (hP : Pairwise fun i j => P i ≠ P j) (hS : ∀ i, P i ∉ principalizingSet S₀)
    (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (χ : ∀ i, MulChar ((𝓞 K) ⧸ (P i).asIdeal) ℂ) (i : ι) :
    sourceDirectedCharacterUnit K S₀ P hP hS a ha χ i i = 1 := by
  rw [sourceDirectedCharacterUnit, dite_eq_left rfl]

omit [Fintype ι] in
theorem sourceDirectedCharacterUnit_val (P : ι → HeightOneSpectrum (𝓞 K))
    (hP : Pairwise fun i j => P i ≠ P j) (hS : ∀ i, P i ∉ principalizingSet S₀)
    (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (χ : ∀ i, MulChar ((𝓞 K) ⧸ (P i).asIdeal) ℂ) (i j : ι) (hij : i ≠ j) :
    (sourceDirectedCharacterUnit K S₀ P hP hS a ha χ i j : ℂ) =
      generatorResidueCharacter S₀ (P i) (hS i) (a i) (ha i) (χ i) (Ideal.Quotient.mk _ (a j)) := by
  rw [sourceDirectedCharacterUnit, dite_eq_right hij, sourceCharacterUnit_val]

theorem sourceCharacterUnit_cofactor (P : ι → HeightOneSpectrum (𝓞 K))
    (hP : Pairwise fun i j => P i ≠ P j) (hS : ∀ i, P i ∉ principalizingSet S₀)
    (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (χ : ∀ i, MulChar ((𝓞 K) ⧸ (P i).asIdeal) ℂ) (n : ι → ℕ) (i : ι) :
    sourceCharacterUnit S₀ (P i) (hS i) (a i) (ha i) (χ i) (sourcePrimeCofactor S₀ a n i)
        (sourcePrimeCofactor_not_mem S₀ P hP hS a ha n i) =
      ∏ j ∈ Finset.univ.erase i, sourceDirectedCharacterUnit K S₀ P hP hS a ha χ i j ^ n j := by
  apply Units.ext
  rw [sourceCharacterUnit_val]
  simp only [Units.coe_prod, Units.val_pow_eq_pow_val, sourcePrimeCofactor, map_prod, map_pow]
  apply Finset.prod_congr rfl
  intro j hj
  rw [sourceDirectedCharacterUnit_val K S₀ P hP hS a ha χ i j (Finset.mem_erase.mp hj).1.symm]

end
end ArtinMatthews.SourceCRTNormalization

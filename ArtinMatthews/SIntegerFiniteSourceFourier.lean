module

public import ArtinMatthews.PrincipalSourceFiniteFourier
public import ArtinMatthews.SourceProductPhasePrimitive
public import ArtinMatthews.SIntegerGaussCRT


set_option backward.privateInPublic true
@[expose] public section

/-! The original finite source Fourier transform over the actual
S-integer ring.  The Gauss factor uses the genuine standard additive
character, and F is the original double quotient sum. -/
namespace ArtinMatthews.SIntegerFourier

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.StandardAdelic
open ArtinMatthews.SourceCRTNormalization
open scoped NumberField Classical BigOperators
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

def sourceResidueGauss (s : PrincipalIntegerRing S₀) (hs : s ≠ 0)
    (f : (PrincipalIntegerRing S₀) ⧸ Ideal.span {s} → ℂ)
    (m : PrincipalIntegerRing S₀) : ℂ :=
  ∑' d : (PrincipalIntegerRing S₀) ⧸ Ideal.span {s}, f d *
    sIntegerQuotientPhase K (principalizingSet S₀) s hs (Ideal.Quotient.mk _ m * d)

def sourcePeriodicFourier (s A : PrincipalIntegerRing S₀) (hs : s ≠ 0) (hA : A ≠ 0)
    (f : (PrincipalIntegerRing S₀) ⧸ Ideal.span {s} → ℂ)
    (g : (PrincipalIntegerRing S₀) ⧸ Ideal.span {A} → ℂ) (h : PrincipalIntegerRing S₀) : ℂ :=
  ∑' m : (PrincipalIntegerRing S₀) ⧸ Ideal.span {s * A},
    sourceResidueGauss S₀ s hs f (-Quotient.out m) * g (Ideal.Quotient.mk _ (Quotient.out m)) *
      sIntegerQuotientPhase K (principalizingSet S₀) (s * A) (mul_ne_zero hs hA)
        (Ideal.Quotient.mk _ (h * Quotient.out m))

theorem sourceQuotientLowerChar (s A : PrincipalIntegerRing S₀) (hs : s ≠ 0) (hA : A ≠ 0) :
    quotientLowerChar s A
      (sIntegerQuotientPhase K (principalizingSet S₀) (s * A) (mul_ne_zero hs hA)) =
    sIntegerQuotientPhase K (principalizingSet S₀) s hs := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [quotientLowerChar_mk, sIntegerQuotientPhase_mk, sIntegerQuotientPhase_mk]
  apply congrArg (sCharacter K (principalizingSet S₀))
  have hs' : (s : K) ≠ 0 := fun h => hs (Subtype.ext h)
  have hA' : (A : K) ≠ 0 := fun h => hA (Subtype.ext h)
  push_cast
  field_simp

theorem principalSourceKernel_eq_sourceFiniteF (s A : PrincipalIntegerRing S₀)
    (hs : s ≠ 0) (hA : A ≠ 0)
    (f : (PrincipalIntegerRing S₀) ⧸ Ideal.span {s} → ℂ)
    (g : (PrincipalIntegerRing S₀) ⧸ Ideal.span {A} → ℂ) (h : PrincipalIntegerRing S₀) :
    principalSourceKernel s A
      (sIntegerQuotientPhase K (principalizingSet S₀) (s * A) (mul_ne_zero hs hA)) f g h =
    sourceFiniteF S₀ s A h (fun x => f (Ideal.Quotient.mk _ x))
      (fun x => g (Ideal.Quotient.mk _ x)) := by
  unfold principalSourceKernel sourceFiniteF sourceFiniteSum
  apply tsum_congr
  intro d
  apply tsum_congr
  intro v
  split_ifs
  · simp only [Ideal.Quotient.mk_out, sIntegerQuotientPhase_mk]
    rfl
  · rfl

theorem sourcePeriodicFourier_eq (s A : PrincipalIntegerRing S₀) (hs : s ≠ 0) (hA : A ≠ 0)
    (hphase : (sIntegerQuotientPhase K (principalizingSet S₀) (s * A)
      (mul_ne_zero hs hA)).IsPrimitive)
    (f : (PrincipalIntegerRing S₀) ⧸ Ideal.span {s} → ℂ)
    (g : (PrincipalIntegerRing S₀) ⧸ Ideal.span {A} → ℂ) (h : PrincipalIntegerRing S₀) :
    sourcePeriodicFourier S₀ s A hs hA f g h =
      (sourceQuotientNorm S₀ s : ℂ) *
        sourceFiniteF S₀ s A h (fun x => f (Ideal.Quotient.mk _ x))
          (fun x => g (Ideal.Quotient.mk _ x)) := by
  let : Finite ((PrincipalIntegerRing S₀) ⧸ Ideal.span {s}) := principal_element_quotient_finite S₀ s hs
  let : Finite ((PrincipalIntegerRing S₀) ⧸ Ideal.span {A}) := principal_element_quotient_finite S₀ A hA
  let : Finite ((PrincipalIntegerRing S₀) ⧸ Ideal.span {s * A}) :=
    principal_element_quotient_finite S₀ (s * A) (mul_ne_zero hs hA)
  have H := principalSourceFiniteFourier s A hA
    (sIntegerQuotientPhase K (principalizingSet S₀) (s * A) (mul_ne_zero hs hA)) hphase f g h
  dsimp only [principalQuotientGauss] at H
  rw [sourceQuotientLowerChar S₀ s A hs hA] at H
  rw [principalSourceKernel_eq_sourceFiniteF S₀ s A hs hA] at H
  refine Eq.trans ?_ H
  unfold sourcePeriodicFourier sourceResidueGauss
  apply tsum_congr
  intro m
  have hr : quotientReduction s A m = Ideal.Quotient.mk (Ideal.span {s}) (Quotient.out m) := by
    conv_lhs => rw [← Ideal.Quotient.mk_out m]
    rfl
  have hv : oppositeReduction s A m = Ideal.Quotient.mk (Ideal.span {A}) (Quotient.out m) := by
    conv_lhs => rw [← Ideal.Quotient.mk_out m]
    rfl
  rw [hr, hv]
  simp only [map_neg, map_mul, Ideal.Quotient.mk_out]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem sourceQuotientPhase_primitive_congr {a b : PrincipalIntegerRing S₀}
    (hab : a = b) (ha : a ≠ 0) (hb : b ≠ 0) :
    (sIntegerQuotientPhase K (principalizingSet S₀) a ha).IsPrimitive ↔
      (sIntegerQuotientPhase K (principalizingSet S₀) b hb).IsPrimitive := by
  cases hab
  rfl

theorem sourceFamilyPeriodicFourier_eq (P : ι → HeightOneSpectrum (𝓞 K))
    (hP : Pairwise fun i j => P i ≠ P j) (hS : ∀ i, P i ∉ principalizingSet S₀)
    (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (k t : ι → ℕ) (hbad : ∀ i, P i ∉ traceBadPlaces K)
    (f : (PrincipalIntegerRing S₀) ⧸ Ideal.span {∏ i, a i ^ k i} → ℂ)
    (g : (PrincipalIntegerRing S₀) ⧸ Ideal.span {∏ i, a i ^ t i} → ℂ)
    (h : PrincipalIntegerRing S₀) :
    sourcePeriodicFourier S₀ (∏ i, a i ^ k i) (∏ i, a i ^ t i)
      (generatorProduct_ne_zero S₀ P a ha k) (generatorProduct_ne_zero S₀ P a ha t) f g h =
      (sourceQuotientNorm S₀ (∏ i, a i ^ k i) : ℂ) *
        sourceFiniteF S₀ (∏ i, a i ^ k i) (∏ i, a i ^ t i) h
          (fun x => f (Ideal.Quotient.mk _ x)) (fun x => g (Ideal.Quotient.mk _ x)) := by
  apply sourcePeriodicFourier_eq S₀ _ _ _ _
  have H := sourceProductQuotientPhase_primitive S₀ P hP hS a ha
    (fun i => k i + t i) hbad
  have hp : (∏ i, a i ^ (k i + t i)) = (∏ i, a i ^ k i) * ∏ i, a i ^ t i := by
    simp only [pow_add, Finset.prod_mul_distrib]
  exact (sourceQuotientPhase_primitive_congr S₀ hp _ _).mp H

end
end ArtinMatthews.SIntegerFourier

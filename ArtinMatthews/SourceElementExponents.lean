module

public import ArtinMatthews.SourcePrimeIdealFactorization
public import ArtinMatthews.SourcePrimeExponentProducts
public import ArtinMatthews.SourcePrimeExponentValuation
public import ArtinMatthews.SourceExponentPowers


set_option backward.privateInPublic true
@[expose] public section

/-! Extract the true finite exterior order vector of any nonzero source
S-integer, using the proved localization and unique ideal factorization. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization SIntegerQuotient
open scoped NumberField Classical nonZeroDivisors
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

def sourcePrimeExponentRingIdealEquiv :
    SourcePrimeExponents F S₀ ≃ (Ideal (sourceRing F S₀))⁰ :=
  (sourcePrimeExponentIdealEquiv F S₀).trans
    (principalExteriorIdealEquiv (sourceHilbertSeed F S₀)).toEquiv

theorem sourcePrimeExponentRingIdealEquiv_val (e : SourcePrimeExponents F S₀) :
    (sourcePrimeExponentRingIdealEquiv F S₀ e).val =
      (sourcePrimeExponentIdeal F S₀ e).map (algebraMap (𝓞 F) (sourceRing F S₀)) := rfl

def sourceElementExponents (u : sourceRing F S₀) (hu : u ≠ 0) : SourcePrimeExponents F S₀ :=
  (sourcePrimeExponentRingIdealEquiv F S₀).symm
    ⟨Ideal.span {u}, mem_nonZeroDivisors_iff_ne_zero.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hu)⟩

theorem sourceElementExponents_congr {u v : sourceRing F S₀}
    (hu : u ≠ 0) (hv : v ≠ 0) (h : u = v) :
    sourceElementExponents F S₀ u hu = sourceElementExponents F S₀ v hv := by
  subst v
  rfl

theorem sourceElementExponents_ideal (u : sourceRing F S₀) (hu : u ≠ 0) :
    (sourcePrimeExponentIdeal F S₀ (sourceElementExponents F S₀ u hu)).map
      (algebraMap (𝓞 F) (sourceRing F S₀)) = Ideal.span {u} :=
  congrArg Subtype.val ((sourcePrimeExponentRingIdealEquiv F S₀).apply_symm_apply _)

theorem sourceElementExponents_of_generator {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (e : SourcePrimeExponents F S₀) :
    sourceElementExponents F S₀ (sourcePrimeExponentGenerator F hζ S₀ e)
      (sourcePrimeExponentGenerator_ne_zero F hζ S₀ e) = e := by
  apply (sourcePrimeExponentRingIdealEquiv F S₀).injective
  apply Subtype.ext
  exact (sourceElementExponents_ideal F S₀ _ _).trans
    (sourcePrimeExponentGenerator_ideal F hζ S₀ e).symm

theorem sourceElementExponents_mul (u v : sourceRing F S₀) (hu : u ≠ 0) (hv : v ≠ 0) :
    sourceElementExponents F S₀ (u * v) (mul_ne_zero hu hv) =
      sourceElementExponents F S₀ u hu + sourceElementExponents F S₀ v hv := by
  apply (sourcePrimeExponentRingIdealEquiv F S₀).injective
  apply Subtype.ext
  simp only [sourcePrimeExponentRingIdealEquiv_val, sourcePrimeExponentIdeal_add,
    Ideal.map_mul, sourceElementExponents_ideal, Ideal.span_singleton_mul_span_singleton]

theorem sourceElementExponents_one :
    sourceElementExponents F S₀ 1 one_ne_zero = 0 := by
  apply (sourcePrimeExponentRingIdealEquiv F S₀).injective
  apply Subtype.ext
  simp only [sourcePrimeExponentRingIdealEquiv_val, sourcePrimeExponentIdeal_zero,
    sourceElementExponents_ideal, Ideal.span_singleton_one, Ideal.one_eq_top, Ideal.map_top]

theorem sourceElementExponents_pow (u : sourceRing F S₀) (hu : u ≠ 0) (k : ℕ) :
    sourceElementExponents F S₀ (u ^ k) (pow_ne_zero k hu) = k • sourceElementExponents F S₀ u hu := by
  induction k with
  | zero => simp only [pow_zero, zero_nsmul, sourceElementExponents_one]
  | succ k ih =>
    calc
      _ = sourceElementExponents F S₀ (u ^ k * u) (mul_ne_zero (pow_ne_zero k hu) hu) :=
        sourceElementExponents_congr F S₀ _ _ (pow_succ u k)
      _ = sourceElementExponents F S₀ (u ^ k) (pow_ne_zero k hu) +
          sourceElementExponents F S₀ u hu := sourceElementExponents_mul F S₀ _ _ _ _
      _ = (k + 1) • sourceElementExponents F S₀ u hu := by rw [ih, succ_nsmul]

theorem sourceElementExponents_mem_primePower_iff {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (u : sourceRing F S₀) (hu : u ≠ 0) (P : SourceExteriorPrime F S₀) (n : ℕ) :
    u ∈ (P.val.asIdeal ^ n).map (algebraMap (𝓞 F) (sourceRing F S₀)) ↔
      n ≤ sourceElementExponents F S₀ u hu P := by
  let e := sourceElementExponents F S₀ u hu
  let J := (P.val.asIdeal ^ n).map (algebraMap (𝓞 F) (sourceRing F S₀))
  have he : Ideal.span {u} = Ideal.span {sourcePrimeExponentGenerator F hζ S₀ e} :=
    (sourceElementExponents_ideal F S₀ u hu).symm.trans
      (sourcePrimeExponentGenerator_ideal F hζ S₀ e)
  calc
    u ∈ J ↔ Ideal.span {u} ≤ J := (Ideal.span_singleton_le_iff_mem J).symm
    _ ↔ Ideal.span {sourcePrimeExponentGenerator F hζ S₀ e} ≤ J := by rw [he]
    _ ↔ sourcePrimeExponentGenerator F hζ S₀ e ∈ J := Ideal.span_singleton_le_iff_mem _
    _ ↔ n ≤ e P := sourcePrimeExponentGenerator_mem_primePower_iff F hζ S₀ e P n

end
end ArtinMatthews

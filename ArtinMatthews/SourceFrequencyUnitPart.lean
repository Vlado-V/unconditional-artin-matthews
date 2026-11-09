module

public import ArtinMatthews.SourceElementExponents
public import ArtinMatthews.SixthExteriorPowerClasses
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Core


set_option backward.privateInPublic true
@[expose] public section

/-! The actual exterior order vector is the normalized valuation of
the original source integer. Removing the fixed product generator
leaves an actual exterior S-unit. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization SIntegerQuotient
open scoped NumberField Classical nonZeroDivisors
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

theorem sourceElementExponents_valuation {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (x : sourceRing F S₀) (hx : x ≠ 0) (P : SourceExteriorPrime F S₀) :
    P.val.valuation F (x : F) = WithZero.exp (-(sourceElementExponents F S₀ x hx P : ℤ)) := by
  let e := sourceElementExponents F S₀ x hx P
  let a := P.val.valuation F (x : F)
  have ha : a ≠ 0 := (Valuation.ne_zero_iff _).mpr (fun h => hx (Subtype.ext h))
  have he (n : ℕ) : a ≤ WithZero.exp (-(n : ℤ)) ↔ n ≤ e :=
    (principalInteger_power_mem_iff_valuation (sourceHilbertSeed F S₀) P.val P.property n x).symm.trans
      (sourceElementExponents_mem_primePower_iff F S₀ hζ x hx P n)
  have h₁ : WithZero.log a ≤ -(e : ℤ) :=
    (WithZero.log_le_iff_le_exp ha).mpr ((he e).mpr le_rfl)
  have h₂ : ¬ WithZero.log a ≤ -((e + 1 : ℕ) : ℤ) := fun h =>
    (Nat.not_succ_le_self e) ((he (e + 1)).mp ((WithZero.log_le_iff_le_exp ha).mp h))
  have hlog : WithZero.log a = -(e : ℤ) := by omega
  change a = WithZero.exp (-(e : ℤ))
  rw [← WithZero.exp_log ha, hlog]

theorem sourceExteriorPrincipalValuation_eq_neg_log
    (P : HeightOneSpectrum (𝓞 F)) (u : Fˣ) :
    exteriorPrincipalValuation P u = -WithZero.log (P.valuation F (u : F)) :=
  IdeleGroup.count_toPrincipalIdeal u P

theorem sourceExteriorPrincipalValuation_eq_zero_iff
    (P : HeightOneSpectrum (𝓞 F)) (u : Fˣ) :
    exteriorPrincipalValuation P u = 0 ↔ P.valuation F (u : F) = 1 := by
  have hv : P.valuation F (u : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr u.ne_zero
  rw [sourceExteriorPrincipalValuation_eq_neg_log, neg_eq_zero]
  constructor
  · intro h
    rw [← WithZero.exp_log hv, h, WithZero.exp_zero]
  · intro h
    rw [h, WithZero.log_one]

def sourceExteriorUnitToSourceRing : exteriorUnitSubgroup (sourceHilbertSet F S₀) →* sourceRing F S₀ where
  toFun u := ⟨(u.val : F), fun P hP =>
    ((sourceExteriorPrincipalValuation_eq_zero_iff F P u.val).mp (u.property P hP)).le⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem sourceExteriorUnitToSourceRing_val (u : exteriorUnitSubgroup (sourceHilbertSet F S₀)) :
    (sourceExteriorUnitToSourceRing F S₀ u : F) = (u.val : F) := rfl

theorem sourceExteriorUnitToSourceRing_ne_zero (u : exteriorUnitSubgroup (sourceHilbertSet F S₀)) :
    sourceExteriorUnitToSourceRing F S₀ u ≠ 0 :=
  fun h => u.val.ne_zero (congrArg (fun x : sourceRing F S₀ => (x : F)) h)

theorem sourceExteriorUnitToSourceRing_injective :
    Function.Injective (sourceExteriorUnitToSourceRing F S₀) := by
  intro a b h
  apply Subtype.ext
  apply Units.ext
  exact congrArg (fun x : sourceRing F S₀ => (x : F)) h

theorem sourceExteriorUnitToSourceRing_exponents {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (u : exteriorUnitSubgroup (sourceHilbertSet F S₀)) :
    sourceElementExponents F S₀ (sourceExteriorUnitToSourceRing F S₀ u)
      (sourceExteriorUnitToSourceRing_ne_zero F S₀ u) = 0 := by
  ext P
  have h := sourceElementExponents_valuation F S₀ hζ (sourceExteriorUnitToSourceRing F S₀ u)
    (sourceExteriorUnitToSourceRing_ne_zero F S₀ u) P
  rw [sourceExteriorUnitToSourceRing_val, (sourceExteriorPrincipalValuation_eq_zero_iff F P.val u.val).mp
    (u.property P.val P.property)] at h
  simpa only [WithZero.exp_eq_one, neg_eq_zero, Int.natCast_eq_zero, Finsupp.zero_apply] using h.symm

def sourceFrequencyUnitPart {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (x : sourceRing F S₀) (hx : x ≠ 0) : exteriorUnitSubgroup (sourceHilbertSet F S₀) := by
  let e := sourceElementExponents F S₀ x hx
  let a : Fˣ := Units.mk0 (x : F) (fun h => hx (Subtype.ext h))
  let b := sourcePrimeExponentUnit F hζ S₀ e
  refine ⟨a / b, ?_⟩
  intro P hP
  apply (sourceExteriorPrincipalValuation_eq_zero_iff F P (a / b)).mpr
  rw [Units.val_div_eq_div_val]
  change P.valuation F ((x : F) / (b : F)) = 1
  rw [map_div₀, sourcePrimeExponentUnit_val, sourceElementExponents_valuation F S₀ hζ x hx ⟨P, hP⟩,
    sourcePrimeExponentGenerator_valuation F hζ S₀ e ⟨P, hP⟩,
    div_self WithZero.exp_ne_zero]

theorem sourceFrequencyUnitPart_factor {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (x : sourceRing F S₀) (hx : x ≠ 0) :
    sourceExteriorUnitToSourceRing F S₀ (sourceFrequencyUnitPart F S₀ hζ x hx) *
      sourcePrimeExponentGenerator F hζ S₀ (sourceElementExponents F S₀ x hx) = x := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, sourceExteriorUnitToSourceRing_val]
  let e := sourceElementExponents F S₀ x hx
  let b := sourcePrimeExponentUnit F hζ S₀ e
  let a : Fˣ := Units.mk0 (x : F) (fun h => hx (Subtype.ext h))
  change ((a / b : Fˣ) : F) * (sourcePrimeExponentGenerator F hζ S₀ e : F) = (x : F)
  rw [Units.val_div_eq_div_val, ← sourcePrimeExponentUnit_val F hζ S₀ e]
  exact div_mul_cancel₀ _ b.ne_zero

end
end ArtinMatthews

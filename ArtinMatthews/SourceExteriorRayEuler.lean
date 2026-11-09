module

public import ArtinMatthews.SourcePrimeIdealFactorization
public import ArtinMatthews.FiniteSupportEuler
public import ArtinMatthews.VaryingKummerAnalyticRayIdealEuler


set_option backward.privateInPublic true
@[expose] public section

/-! The actual exterior-ideal ray series in the derived prime coordinates.
Its Euler product follows from ideal multiplicativity and absolute
convergence; all additional conductor-prime zero values are retained. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M)

def sourceExteriorRaySeries (s : ℂ) : ℂ :=
  ∑' e : SourcePrimeExponents F S₀, η.allCoefficient (sourcePrimeExponentIdeal F S₀ e) *
    (sourcePrimeExponentNorm F S₀ e : ℂ) ^ (-s)

theorem sourceExteriorRay_term (s : ℂ) (hs : 1 < s.re)
    (e : SourcePrimeExponents F S₀) :
    SourceEuler.finiteChoiceWeight
        (fun P : SourceExteriorPrime F S₀ => fun n => (η.idealTerm hs P.val.asIdeal) ^ n) e =
      η.idealTerm hs (sourcePrimeExponentIdeal F S₀ e) := by
  rw [SourceEuler.finiteChoiceWeight, sourcePrimeExponentIdeal, Finsupp.prod, map_prod]
  apply Finset.prod_congr rfl
  intro P _
  exact (map_pow (η.idealTerm hs) P.val.asIdeal (e P)).symm

theorem sourceExteriorRay_series_eq (s : ℂ) (hs : 1 < s.re) :
    sourceExteriorRaySeries F S₀ η s =
      ∑' e : SourcePrimeExponents F S₀, η.idealTerm hs (sourcePrimeExponentIdeal F S₀ e) := by
  apply tsum_congr
  intro e
  rw [EvenIdealRayCharacter.idealTerm_apply, sourcePrimeExponentIdeal_norm]

theorem sourceExteriorRay_summable (s : ℂ) (hs : 1 < s.re) :
    Summable (fun e : SourcePrimeExponents F S₀ =>
      ‖η.idealTerm hs (sourcePrimeExponentIdeal F S₀ e)‖) :=
  (η.idealTerm_summable hs).norm.comp_injective (sourcePrimeExponentIdeal_injective F S₀)

theorem sourceExteriorRay_prime_norm_lt_one (s : ℂ) (hs : 1 < s.re)
    (P : SourceExteriorPrime F S₀) : ‖η.idealTerm hs P.val.asIdeal‖ < 1 := by
  have hq0 : Ideal.absNorm P.val.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr P.val.ne_bot
  have hq1 : Ideal.absNorm P.val.asIdeal ≠ 1 :=
    fun h => P.val.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have hq : 2 ≤ Ideal.absNorm P.val.asIdeal := by omega
  have h := VaryingKummerAnalytic.zetaSummand_norm_lt_one hs hq
  change ‖η.allCoefficient P.val.asIdeal *
    riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) (Ideal.absNorm P.val.asIdeal)‖ < 1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (η.allCoefficient_norm_le_one P.val.asIdeal)).trans_lt h

theorem sourceExteriorRay_hasProd (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun P : SourceExteriorPrime F S₀ =>
      (1 - η.allCoefficient P.val.asIdeal * (Ideal.absNorm P.val.asIdeal : ℂ) ^ (-s))⁻¹)
      (sourceExteriorRaySeries F S₀ η s) := by
  let f (P : SourceExteriorPrime F S₀) (n : ℕ) : ℂ := (η.idealTerm hs P.val.asIdeal) ^ n
  have hw (e : SourcePrimeExponents F S₀) : SourceEuler.finiteChoiceWeight f e =
      η.idealTerm hs (sourcePrimeExponentIdeal F S₀ e) := sourceExteriorRay_term F S₀ η s hs e
  have hsum : Summable (fun e : SourcePrimeExponents F S₀ => ‖SourceEuler.finiteChoiceWeight f e‖) :=
    (sourceExteriorRay_summable F S₀ η s hs).congr (fun e => congrArg norm (hw e).symm)
  have he := SourceEuler.finiteChoice_hasProd f (fun _ => pow_zero _) hsum
  have htot : (∑' e, SourceEuler.finiteChoiceWeight f e) = sourceExteriorRaySeries F S₀ η s :=
    (tsum_congr hw).trans (sourceExteriorRay_series_eq F S₀ η s hs).symm
  rw [htot] at he
  apply he.congr_fun
  intro P
  exact (hasSum_geometric_of_norm_lt_one (sourceExteriorRay_prime_norm_lt_one F S₀ η s hs P)).tsum_eq.symm

end
end ArtinMatthews

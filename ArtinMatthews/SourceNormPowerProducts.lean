module

public import ArtinMatthews.SourcePrimeExponents
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex


set_option backward.privateInPublic true
@[expose] public section

/-! The norm-power factors split over actual primes on the ordinary
complex branch because every base is a nonnegative rational integer. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators
open scoped NumberField Classical BigOperators
noncomputable section

def sourceNatNormPowerHom (s : ℂ) : ℕ →* ℂ where
  toFun n := (n : ℂ) ^ s
  map_one' := by simpa only [Nat.cast_one] using Complex.one_cpow s
  map_mul' m n := by
    simpa only [Nat.cast_mul] using Complex.natCast_mul_natCast_cpow m n s

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

theorem sourcePrimeExponentNorm_cpow_prod (e : SourcePrimeExponents F S₀) (s : ℂ) :
    (sourcePrimeExponentNorm F S₀ e : ℂ) ^ s =
      e.prod (fun P n => ((Ideal.absNorm P.val.asIdeal : ℂ) ^ s) ^ n) := by
  change sourceNatNormPowerHom s (sourcePrimeExponentNorm F S₀ e) =
    e.prod (fun P n => sourceNatNormPowerHom s (Ideal.absNorm P.val.asIdeal) ^ n)
  rw [sourcePrimeExponentNorm, Finsupp.prod, map_prod]
  apply Finset.prod_congr rfl
  intro P _
  exact map_pow (sourceNatNormPowerHom s) _ _

theorem sourcePrimeExponentNorm_cpow_prefix (e : SourcePrimeExponents F S₀) (s : ℂ)
    (T : Finset (SourceExteriorPrime F S₀)) (he : e.support ⊆ T) :
    (sourcePrimeExponentNorm F S₀ e : ℂ) ^ s =
      ∏ P : T, ((Ideal.absNorm P.val.val.asIdeal : ℂ) ^ s) ^ e P.val := by
  rw [sourcePrimeExponentNorm_cpow_prod]
  calc
    _ = ∏ P ∈ T, ((Ideal.absNorm P.val.asIdeal : ℂ) ^ s) ^ e P := by
      apply Finset.prod_subset he
      intro P _ hp
      rw [Finsupp.notMem_support_iff.mp hp]
      exact pow_zero _
    _ = _ := (Finset.prod_coe_sort T _).symm

end
end ArtinMatthews

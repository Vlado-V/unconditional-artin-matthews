module

public import ArtinMatthews.SourceQuadraticDualExteriorErrors
public import ArtinMatthews.QuadraticHeckeCutoffCoefficientBounds


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain VaryingKummerAnalytic
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "Bad" => sourceQuadraticBlockBadIdeal F S₀

theorem sourceQuadraticDual_outer_divisor_card (g : E) :
    (HeckeIdealMobius.divisors F (sourceQuadraticBlockRadical F S₀ g)).card ≤
      Ideal.absNorm Bad * q g :=
  (quadraticHecke_divisor_card_le_norm F _ (sourceQuadraticBlockRadical_squarefree F S₀ g)).trans
    (sourceQuadraticBlockRadical_norm_le F S₀ g)

theorem sourceQuadraticDual_bad_divisor_card :
    (HeckeIdealMobius.divisors F (quadraticHeckeIdealRadical F Bad)).card ≤ Ideal.absNorm Bad := by
  apply (quadraticHecke_divisor_card_le_norm F _ (quadraticHeckeIdealRadical_squarefree F Bad)).trans
  apply quadraticHeckeIdealRadical_norm_le F
  unfold sourceQuadraticBlockBadIdeal
  exact Ideal.span_singleton_eq_bot.not.mpr
    (SIntegerPrincipalization.principalizingDenominator_ne_zero (sourceHilbertSeed F S₀))

theorem sourceQuadraticDual_divisor_norm_one_le (g : E) (d : Ideal (𝓞 F))
    (hd : d ∈ HeckeIdealMobius.divisors F (sourceQuadraticBlockRadical F S₀ g)) :
    1 ≤ (Ideal.absNorm d : ℝ) := by
  have hn := quadraticHeckeCoprime_divisor_norm_pos F (sourceQuadraticBlockRadical F S₀ g)
    (quadraticHeckeIdealRadical_ne_bot F _) hd
  exact_mod_cast (show 1 ≤ Ideal.absNorm d from Nat.succ_le_of_lt (by exact_mod_cast hn))

theorem sourceQuadraticDual_bad_norm_one_le (d : Ideal (𝓞 F))
    (hd : d ∈ HeckeIdealMobius.divisors F (quadraticHeckeIdealRadical F Bad)) :
    1 ≤ (Ideal.absNorm d : ℝ) := by
  have hn := quadraticHeckeCoprime_divisor_norm_pos F (quadraticHeckeIdealRadical F Bad)
    (quadraticHeckeIdealRadical_ne_bot F _) hd
  exact_mod_cast (show 1 ≤ Ideal.absNorm d from Nat.succ_le_of_lt (by exact_mod_cast hn))

end
end ArtinMatthews.SourceEulerAssembly

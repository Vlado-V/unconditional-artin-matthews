module

public import ArtinMatthews.SourceQuadraticRadicalDivisors
public import ArtinMatthews.SourceQuadraticSmallAmplitude


set_option backward.privateInPublic true
@[expose] public section

/-! All squarefree ideal rows split into a fixed bad divisor and an
actual exterior row. The original product cutoff is retained. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain StandardAdelic VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "I" => sourcePrimeExponentIdeal F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "Bad" => sourceQuadraticBlockBadIdeal F S₀
local notation "Ψ" => sourceQuadraticRayCharacter F S₀ hζ
local notation "χ" => sourceReflectionQuadraticSymbol F S₀ hζ

omit [IsTotallyComplex F] in
theorem sourceQuadraticDual_zero_radical :
    sourceQuadraticBlockRadical F S₀ 0 = quadraticHeckeIdealRadical F Bad := by
  simp only [sourceQuadraticBlockRadical, sourcePrimeExponentIdeal_zero, mul_one]

theorem sourceQuadraticDual_bad_row_coefficient (b c g a : E)
    (hb : sourceReflectionIsSquarefree b) (hc : sourceReflectionIsSquarefree c)
    (hg : b ⊓ c = g)
    (hclass : sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c)
    (d : Ideal (𝓞 F)) (hd : d ∣ quadraticHeckeIdealRadical F Bad) :
    (Ψ ((b-g)+(c-g))).allCoefficient (I a * d) = χ a (b-g) * χ a (c-g) := by
  rw [EvenIdealRayCharacter.allCoefficient_mul,
    sourceQuadraticPair_badIdeal_coefficient_one F S₀ hζ b c g hg hclass d
      (hd.trans (quadraticHeckeIdealRadical_dvd F Bad)), mul_one,
    sourceQuadraticSmallPair_coefficient F S₀ hζ b c g hb hc hg a]

theorem sourceQuadraticDual_all_ideal_rows (b c g : E)
    (hb : sourceReflectionIsSquarefree b) (hc : sourceReflectionIsSquarefree c)
    (hg : b ⊓ c = g)
    (hclass : sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c)
    (K : ℝ) (H : Ideal (𝓞 F) → ℂ) :
    (∑ a ∈ quadraticHeckeSquarefreeCutoff F K,
      (Ψ ((b-g)+(c-g))).allCoefficient a * H a) =
    ∑ a ∈ sourceQuadraticBlockRadicalRows F S₀ 0 K,
      ∑ d ∈ HeckeIdealMobius.divisors F (quadraticHeckeIdealRadical F Bad),
        if (q a : ℝ) * (Ideal.absNorm d : ℝ) ≤ K then
          χ a (b-g) * χ a (c-g) * H (I a * d) else 0 := by
  rw [quadraticHeckeSquarefreeCutoff_split F (quadraticHeckeIdealRadical F Bad)
    (quadraticHeckeIdealRadical_squarefree F Bad) K]
  have hrow := sourceQuadraticBlockRadicalRows_sum F S₀ 0 K
    (fun a => ∑ d ∈ HeckeIdealMobius.divisors F (quadraticHeckeIdealRadical F Bad),
      if (Ideal.absNorm (a*d) : ℝ) ≤ K then
        (Ψ ((b-g)+(c-g))).allCoefficient (a*d) * H (a*d) else 0)
  rw [sourceQuadraticDual_zero_radical F S₀] at hrow
  rw [← hrow]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro d hd
  rw [map_mul, Nat.cast_mul, sourcePrimeExponentIdeal_norm]
  split_ifs with h
  · rw [sourceQuadraticDual_bad_row_coefficient F S₀ hζ b c g a hb hc hg hclass d
      ((HeckeIdealMobius.mem_divisors F (quadraticHeckeIdealRadical_ne_bot F Bad)).mp hd)]
  · rfl

end
end ArtinMatthews.SourceEulerAssembly

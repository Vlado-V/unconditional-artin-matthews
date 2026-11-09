module

public import ArtinMatthews.SourceQuadraticRadicalRows
public import ArtinMatthews.QuadraticHeckeDivisorProduct
public import ArtinMatthews.SourceQuadraticPairBadTriviality
public import ArtinMatthews.SourceQuadraticBlockCharacter


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain StandardAdelic VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "E" => SourcePrimeExponents F S₀
local notation "I" => sourcePrimeExponentIdeal F S₀
local notation "Bad" => sourceQuadraticBlockBadIdeal F S₀

/-- The exterior part of a radical divisor, with every fixed bad prime removed. -/
def sourceQuadraticBlockGoodDivisor (g : E) (d : Ideal (𝓞 F)) : Ideal (𝓞 F) :=
  gcd d (I g)

theorem sourceQuadraticBlockGoodDivisor_dvd (g : E) (d : Ideal (𝓞 F)) :
    sourceQuadraticBlockGoodDivisor F S₀ g d ∣ I g := gcd_dvd_right _ _

theorem sourceQuadraticBlockGoodDivisor_ne_bot (g : E) (d : Ideal (𝓞 F)) :
    sourceQuadraticBlockGoodDivisor F S₀ g d ≠ ⊥ :=
  ne_zero_of_dvd_ne_zero (sourcePrimeExponentIdeal_ne_bot F S₀ g)
    (sourceQuadraticBlockGoodDivisor_dvd F S₀ g d)

theorem sourceQuadraticBlockGoodDivisor_coprime (g : E) (d : Ideal (𝓞 F)) :
    IsCoprime (sourceQuadraticBlockGoodDivisor F S₀ g d) Bad :=
  (sourceQuadraticBlock_exterior_coprime F S₀ g).of_isCoprime_of_dvd_left
    (sourceQuadraticBlockGoodDivisor_dvd F S₀ g d)

/-- The source exponent label of the exterior part of a divisor. -/
def sourceQuadraticBlockGoodIndex (g : E) (d : Ideal (𝓞 F)) : E :=
  sourceExteriorIdealExponents F S₀
    ⟨sourceQuadraticBlockGoodDivisor F S₀ g d,
      sourceQuadraticBlockGoodDivisor_ne_bot F S₀ g d,
      sourceQuadraticBlockGoodDivisor_coprime F S₀ g d⟩

theorem sourceQuadraticBlockGoodIndex_ideal (g : E) (d : Ideal (𝓞 F)) :
    I (sourceQuadraticBlockGoodIndex F S₀ g d) = sourceQuadraticBlockGoodDivisor F S₀ g d :=
  sourceExteriorIdealExponents_recover F S₀ _

/-- A radical divisor is the product of a fixed-bad divisor and its exact exterior part. -/
theorem sourceQuadraticBlockRadical_divisor_split (g : E)
    (hg : sourceReflectionIsSquarefree g) (d : Ideal (𝓞 F))
    (hd : d ∣ sourceQuadraticBlockRadical F S₀ g) :
    ∃ u : Ideal (𝓞 F), u ∣ Bad ∧ d = u * sourceQuadraticBlockGoodDivisor F S₀ g d := by
  rw [sourceQuadraticBlockRadical_eq F S₀ g hg] at hd
  obtain ⟨u, v, hu, hv, huv⟩ := exists_dvd_and_dvd_of_dvd_mul hd
  have huB : u ∣ Bad := hu.trans (quadraticHeckeIdealRadical_dvd F Bad)
  have hcop : IsCoprime u (I g) :=
    (sourceQuadraticBlock_exterior_coprime F S₀ g).symm.of_isCoprime_of_dvd_left huB
  have hgood : sourceQuadraticBlockGoodDivisor F S₀ g d = v := by
    change gcd d (I g) = v
    rw [huv]
    exact quadraticHecke_coprime_divisor_gcd F hcop hv
  exact ⟨u, huB, by rw [hgood]; exact huv⟩

variable [IsTotallyComplex F] {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "Ψ" => sourceQuadraticRayCharacter F S₀ hζ
local notation "χ" => sourceReflectionQuadraticSymbol F S₀ hζ

/-- The actual common-pair character ignores exactly the fixed-bad part of a radical divisor. -/
theorem sourceQuadraticPair_radicalDivisor_coefficient (b c g : E)
    (hb : sourceReflectionIsSquarefree b) (hc : sourceReflectionIsSquarefree c)
    (hg : b ⊓ c = g)
    (hclass : sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c)
    (d : Ideal (𝓞 F)) (hd : d ∣ sourceQuadraticBlockRadical F S₀ g) :
    (Ψ ((b-g)+(c-g))).allCoefficient d =
      χ (sourceQuadraticBlockGoodIndex F S₀ g d) ((b-g)+(c-g)) := by
  have hgs : sourceReflectionIsSquarefree g := by
    intro P
    have hgb : g ≤ b := hg ▸ (inf_le_left : b ⊓ c ≤ b)
    exact (hgb P).trans (hb P)
  obtain ⟨u, hu, hdu⟩ := sourceQuadraticBlockRadical_divisor_split F S₀ g hgs d hd
  have he : sourceReflectionIsSquarefree ((b-g)+(c-g)) :=
    sourceQuadraticBlock_residual_squarefree F S₀ b c g hb hc
      ((sourceQuadratic_inf_eq_iff_quotient_disjoint F S₀ b c g).1 hg).2.2
  calc
    _ = (Ψ ((b-g)+(c-g))).allCoefficient
        (u * sourceQuadraticBlockGoodDivisor F S₀ g d) := congrArg _ hdu
    _ = (Ψ ((b-g)+(c-g))).allCoefficient (sourceQuadraticBlockGoodDivisor F S₀ g d) := by
      rw [EvenIdealRayCharacter.allCoefficient_mul,
        sourceQuadraticPair_badIdeal_coefficient_one F S₀ hζ b c g hg hclass u hu, one_mul]
    _ = _ := by
      rw [← sourceQuadraticBlockGoodIndex_ideal F S₀ g d]
      exact sourceQuadraticRayCharacter_allCoefficient F S₀ hζ _ he _

/-- Both radical divisors become a single genuine source-character twist. -/
theorem sourceQuadraticPair_radicalTriple_coefficient (b c g h : E)
    (hb : sourceReflectionIsSquarefree b) (hc : sourceReflectionIsSquarefree c)
    (hg : b ⊓ c = g)
    (hclass : sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c)
    (d e : Ideal (𝓞 F)) (hd : d ∣ sourceQuadraticBlockRadical F S₀ g)
    (he : e ∣ sourceQuadraticBlockRadical F S₀ g) :
    (Ψ ((b-g)+(c-g))).allCoefficient (I h * d * e) =
      χ h ((b-g)+(c-g)) *
        χ (sourceQuadraticBlockGoodIndex F S₀ g d + sourceQuadraticBlockGoodIndex F S₀ g e)
          ((b-g)+(c-g)) := by
  have hres : sourceReflectionIsSquarefree ((b-g)+(c-g)) :=
    sourceQuadraticBlock_residual_squarefree F S₀ b c g hb hc
      ((sourceQuadratic_inf_eq_iff_quotient_disjoint F S₀ b c g).1 hg).2.2
  rw [EvenIdealRayCharacter.allCoefficient_mul, EvenIdealRayCharacter.allCoefficient_mul,
    sourceQuadraticPair_radicalDivisor_coefficient F S₀ hζ b c g hb hc hg hclass d hd,
    sourceQuadraticPair_radicalDivisor_coefficient F S₀ hζ b c g hb hc hg hclass e he,
    sourceQuadraticRayCharacter_allCoefficient F S₀ hζ _ hres h]
  have hmul : χ (sourceQuadraticBlockGoodIndex F S₀ g d + sourceQuadraticBlockGoodIndex F S₀ g e)
      ((b-g)+(c-g)) = χ (sourceQuadraticBlockGoodIndex F S₀ g d) ((b-g)+(c-g)) *
        χ (sourceQuadraticBlockGoodIndex F S₀ g e) ((b-g)+(c-g)) := by
    unfold sourceReflectionQuadraticSymbol
    exact sourceReflectionQuadraticSymbol_add_left F S₀ hζ _ _ _
  rw [hmul]
  ring

/-- The exact omitted ideal summand carries the canonical exterior divisor twist. -/
theorem sourceQuadraticPair_radicalCutoff_summand (b c g h : E)
    (hb : sourceReflectionIsSquarefree b) (hc : sourceReflectionIsSquarefree c)
    (hg : b ⊓ c = g)
    (hclass : sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c)
    (H : ℝ) (d e : Ideal (𝓞 F)) (hd : d ∣ sourceQuadraticBlockRadical F S₀ g)
    (he : e ∣ sourceQuadraticBlockRadical F S₀ g) :
    (if H < (Ideal.absNorm (I h * d) : ℝ) then
      -(UniqueFactorizationMonoid.moebius e : ℂ) *
        quadraticHeckeHalfCoefficient F (Ψ ((b-g)+(c-g))) (I h * d * e) else 0) =
      quadraticHeckeCutoffWeight F H (I h) d e * χ h ((b-g)+(c-g)) *
        χ (sourceQuadraticBlockGoodIndex F S₀ g d + sourceQuadraticBlockGoodIndex F S₀ g e)
          ((b-g)+(c-g)) := by
  rw [quadraticHeckeCutoffTail_summand,
    sourceQuadraticPair_radicalTriple_coefficient F S₀ hζ b c g h hb hc hg hclass d e hd he]
  ring

/-- The omitted ideal coefficient is exactly the source quadratic pair with its divisor twist. -/
theorem sourceQuadraticPair_radicalCutoff_pair (a : E → ℂ) (b c g h : E)
    (hb : sourceReflectionIsSquarefree b) (hc : sourceReflectionIsSquarefree c)
    (hg : b ⊓ c = g)
    (hclass : sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c)
    (H : ℝ) (d e : Ideal (𝓞 F)) (hd : d ∣ sourceQuadraticBlockRadical F S₀ g)
    (he : e ∣ sourceQuadraticBlockRadical F S₀ g) :
    star (a b) * a c *
      (if H < (Ideal.absNorm (I h * d) : ℝ) then
        -(UniqueFactorizationMonoid.moebius e : ℂ) *
          quadraticHeckeHalfCoefficient F (Ψ ((b-g)+(c-g))) (I h * d * e) else 0) =
      quadraticHeckeCutoffWeight F H (I h) d e *
        star (χ h (b-g) *
          (a b * χ (sourceQuadraticBlockGoodIndex F S₀ g d + sourceQuadraticBlockGoodIndex F S₀ g e) (b-g))) *
        (χ h (c-g) *
          (a c * χ (sourceQuadraticBlockGoodIndex F S₀ g d + sourceQuadraticBlockGoodIndex F S₀ g e) (c-g))) := by
  rw [sourceQuadraticPair_radicalCutoff_summand F S₀ hζ b c g h hb hc hg hclass H d e hd he]
  simp only [star_mul]
  rw [sourceQuadraticBlock_symbol_star F S₀ hζ h (b-g)
    (sourceQuadraticExteriorQuotient_squarefree F S₀ b g hb),
    sourceQuadraticBlock_symbol_star F S₀ hζ
      (sourceQuadraticBlockGoodIndex F S₀ g d + sourceQuadraticBlockGoodIndex F S₀ g e) (b-g)
      (sourceQuadraticExteriorQuotient_squarefree F S₀ b g hb)]
  simp only [sourceQuadraticSymbol_add_right]
  ring

/-- GL7.3 for the actual retained exterior rows and the canonical radical-divisor twists. -/
theorem sourceQuadraticBlockRadical_canonicalMain_bound {α : ℝ}
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
    (hE : QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) α)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ cBound : ℝ, 0 < cBound ∧ ∀ M P H : ℝ, 1 ≤ M → 1 ≤ P → 1 ≤ H → H ≤ M →
      ∀ (g : E) (cols : Finset E),
      (∀ b ∈ cols, sourceReflectionIsSquarefree b ∧ (sourcePrimeExponentNorm F S₀ b : ℝ) ≤ P) →
      ∀ coeff : E → ℂ,
      ‖(Real.sqrt M : ℂ) * sourceQuadraticActualCutoffMainSum F S₀ hζ
          (sourceQuadraticBlockRadical F S₀ g) H (sourceQuadraticBlockRadicalRows F S₀ g H) cols
          (fun d e => sourceQuadraticBlockGoodIndex F S₀ g d + sourceQuadraticBlockGoodIndex F S₀ g e)
          coeff‖ ≤
        cBound * (sourcePrimeExponentNorm F S₀ g : ℝ) ^ 4 * (M * P) ^ ε *
          (Real.sqrt M * H ^ (α - 1 / 2) + Real.sqrt (M / H) * P) *
            ∑ b ∈ cols, ‖coeff b‖ ^ 2 := by
  obtain ⟨cBound, hc, hbound⟩ := sourceQuadraticBlockRadical_main_bound F S₀ hζ htrace hE ε hε
  refine ⟨cBound, hc, ?_⟩
  intro M P H hM hP hH hHM g cols hcols coeff
  exact hbound M P H hM hP hH hHM g (sourceQuadraticBlockRadicalRows F S₀ g H) cols
    (fun h hh => sourceQuadraticBlockRadicalRows_spec F S₀ g H h hh) hcols _ coeff

end
end ArtinMatthews.SourceEulerAssembly

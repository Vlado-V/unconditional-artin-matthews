module

public import ArtinMatthews.SourceQuadraticDualErrorIntegral
public import ArtinMatthews.SourceQuadraticDualExteriorErrors
public import ArtinMatthews.SourceQuadraticDualRestrictedContour


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain VaryingKummerAnalytic UniqueFactorizationMonoid
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "I" => sourcePrimeExponentIdeal F S₀
local notation "Bad" => sourceQuadraticBlockBadIdeal F S₀
local notation "C" e:max => sourceQuadraticConductor F S₀ hζ e
local notation "Ψ" => sourceQuadraticRayCharacter F S₀ hζ
local notation "χ" => sourceReflectionQuadraticSymbol F S₀ hζ
local notation "A" => quadraticHeckeFieldScale F
local notation "r" => InfinitePlace.nrComplexPlaces F

theorem sourceQuadraticDualDivisorError_radical (M K σ : ℝ) (g e : E) :
    sourceQuadraticDualDivisorError F S₀ hζ M K σ g e =
      ∑ d ∈ HeckeIdealMobius.divisors F (sourceQuadraticBlockRadical F S₀ g),
        (moebius d : ℂ) * (Ψ e).allCoefficient d *
          ((M/(Ideal.absNorm d : ℝ))/Real.sqrt (Ideal.absNorm (C e)) : ℝ) *
          sourceQuadraticDualSquarefreeError F S₀ hζ e (M/(Ideal.absNorm d : ℝ)) K σ := by
  simpa only [sourceQuadraticDualDivisorError, sourceQuadraticBlockRadical,
    sourceQuadraticBlockModulus, mul_assoc] using
    quadraticHeckeIdealRadical_moebius_sum F (sourceQuadraticBlockModulus_ne_bot F S₀ g)
      (fun d => (Ψ e).allCoefficient d *
        ((M/(Ideal.absNorm d : ℝ))/Real.sqrt (Ideal.absNorm (C e)) : ℝ) *
        sourceQuadraticDualSquarefreeError F S₀ hζ e (M/(Ideal.absNorm d : ℝ)) K σ)

theorem sourceQuadraticDualErrorBlock_eq_restricted (M K σ : ℝ)
    (cols : Finset E) (u : E → ℂ) (g : E)
    (hcols : ∀ b ∈ cols, sourceReflectionIsSquarefree b)
    (hclass : ∀ b ∈ cols, ∀ c ∈ cols,
      sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c) :
    sourceQuadraticDualErrorBlock F S₀ hζ M K σ cols u g =
      ∑ d ∈ HeckeIdealMobius.divisors F (sourceQuadraticBlockRadical F S₀ g),
        (moebius d : ℂ) *
          ∑ h ∈ HeckeIdealMobius.divisors F (quadraticHeckeIdealRadical F Bad),
            sourceQuadraticDualRestrictedContour F S₀ hζ
              (sourceQuadraticDualExteriorRows F S₀ K h) cols u g
              (sourceQuadraticBlockGoodIndex F S₀ g d)
              (M/(Ideal.absNorm d : ℝ)) (Ideal.absNorm h : ℝ) σ := by
  let pairs := (cols ×ˢ cols).filter (fun p : E × E => p.1 ⊓ p.2 = g)
  let T (p : E × E) (d h : Ideal (𝓞 F)) : ℂ :=
    star (u p.1) * u p.2 * χ (sourceQuadraticBlockGoodIndex F S₀ g d) ((p.1-g)+(p.2-g)) *
      (((M/(Ideal.absNorm d : ℝ))/Real.sqrt (Ideal.absNorm (C ((p.1-g)+(p.2-g))))) : ℝ) *
      ∑ a ∈ sourceQuadraticDualExteriorRows F S₀ K h,
        (Ψ ((p.1-g)+(p.2-g))).allCoefficient (I a) *
          quadraticHeckeCoprimeContourRemainder F (C ((p.1-g)+(p.2-g)))
            (quadraticHeckeSquareMellin (quadraticHeckeDualMellin A r sourceQuadraticBlockProfile))
            σ (Real.sqrt ((Ideal.absNorm (C ((p.1-g)+(p.2-g))) : ℝ) /
              ((M/(Ideal.absNorm d : ℝ))*((q a : ℝ)*(Ideal.absNorm h : ℝ)))))
  have hterm (p : E × E) (hp : p ∈ pairs) (d : Ideal (𝓞 F))
      (hd : d ∈ HeckeIdealMobius.divisors F (sourceQuadraticBlockRadical F S₀ g)) :
      star (u p.1) * u p.2 *
        ((moebius d : ℂ) * (Ψ ((p.1-g)+(p.2-g))).allCoefficient d *
          (((M/(Ideal.absNorm d : ℝ))/Real.sqrt (Ideal.absNorm (C ((p.1-g)+(p.2-g))))) : ℝ) *
          sourceQuadraticDualSquarefreeError F S₀ hζ ((p.1-g)+(p.2-g))
            (M/(Ideal.absNorm d : ℝ)) K σ) =
        (moebius d : ℂ) *
          ∑ h ∈ HeckeIdealMobius.divisors F (quadraticHeckeIdealRadical F Bad), T p d h := by
    obtain ⟨hp', hg⟩ := Finset.mem_filter.mp hp
    obtain ⟨hb, hc⟩ := Finset.mem_product.mp hp'
    rw [sourceQuadraticDualSquarefreeError_exterior F S₀ hζ p.1 p.2 g
      (hcols p.1 hb) (hcols p.2 hc) hg (hclass p.1 hb p.2 hc),
      sourceQuadraticPair_radicalDivisor_coefficient F S₀ hζ p.1 p.2 g
        (hcols p.1 hb) (hcols p.2 hc) hg (hclass p.1 hb p.2 hc) d
        ((HeckeIdealMobius.mem_divisors F
          (quadraticHeckeIdealRadical_ne_bot F (sourceQuadraticBlockModulus F S₀ g))).mp hd)]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    dsimp only [T]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  unfold sourceQuadraticDualErrorBlock
  simp_rw [sourceQuadraticDualDivisorError_radical, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  change (∑ p ∈ pairs, _) = _
  rw [Finset.sum_congr rfl (fun p hp => hterm p hp d hd), ← Finset.mul_sum,
    Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  congr 1

end
end ArtinMatthews.SourceEulerAssembly

module

public import ArtinMatthews.SourceQuadraticRadicalDivisors
public import ArtinMatthews.SourceQuadraticDensityContraction
public import ArtinMatthews.SourceQuadraticSmallCofactors


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain VaryingKummerAnalytic QuadraticScale
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "I" => sourcePrimeExponentIdeal F S₀
local notation "Ψ" => sourceQuadraticRayCharacter F S₀ hζ
local notation "χ" => sourceReflectionQuadraticSymbol F S₀ hζ
local notation "C" => sourceQuadraticConductor F S₀ hζ
local notation "m" g:max => sourceQuadraticBlockBadIdeal F S₀ * I g
local notation "R" g:max => sourceQuadraticBlockRadical F S₀ g
local notation "D" g:max => HeckeIdealMobius.divisors F (R g)
local notation "Rows" g:max H:max => sourceQuadraticBlockRadicalRows F S₀ g H

/-- The exact difference of the two normalized half-coefficient residues. -/
def sourceQuadraticHalfResidueDifference (H : ℝ) (g e : E) : ℂ :=
  (∑ a ∈ quadraticHeckeSquarefreeCutoff F H, quadraticHeckeHalfCoefficient F (Ψ e) a) *
      (∑ d ∈ HeckeIdealMobius.divisors F (m g),
        (UniqueFactorizationMonoid.moebius d : ℂ) * quadraticHeckeHalfCoefficient F (Ψ e) d) -
    (∑ a ∈ quadraticHeckeCoprimeCutoff F (m g) H,
      quadraticHeckeHalfCoefficient F (Ψ e) a) * quadraticHeckeCoprimeDensity F (m g)

/-- The literal common-pair sum after the two residues are normalized. -/
def sourceQuadraticNormalizedResidueBlock (M H : ℝ) (cols : Finset E)
    (u : E → ℂ) (g : E) : ℂ :=
  sourceQuadraticSmallResidueFactor F M *
    ∑ p ∈ (cols ×ˢ cols).filter (fun p : E × E => p.1 ⊓ p.2 = g),
      star (u p.1) * u p.2 * quadraticHeckeCoprimeDensity F (C ((p.1-g)+(p.2-g))) *
        sourceQuadraticHalfResidueDifference F S₀ hζ H g ((p.1-g)+(p.2-g))

theorem sourceQuadraticPair_halfResidueDifference_tail (H : ℝ) (b c g : E)
    (hb : sourceReflectionIsSquarefree b) (hc : sourceReflectionIsSquarefree c)
    (hg : b ⊓ c = g)
    (hclass : sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c) :
    sourceQuadraticHalfResidueDifference F S₀ hζ H g ((b-g)+(c-g)) =
      ∑ d ∈ D g, ∑ e ∈ D g, ∑ h ∈ Rows g H,
        quadraticHeckeCutoffWeight F H (I h) d e *
          (Ψ ((b-g)+(c-g))).allCoefficient (I h * d * e) := by
  have hm : m g ≠ ⊥ := mul_ne_zero (sourceQuadraticBlockBadIdeal_ne_bot F S₀)
    (sourcePrimeExponentIdeal_ne_bot F S₀ g)
  have hmc : IsCoprime (m g) (C ((b-g)+(c-g))) := by
    rw [sourceQuadraticPairConductor_eq_product F S₀ hζ b c g hb hc hg hclass]
    exact sourceQuadratic_commonModulus_coprime_residualProduct F S₀ b c g hb hc
  have hχ (J : Ideal (𝓞 F)) (hJ : J ≠ ⊥) (hJC : IsCoprime J (C ((b-g)+(c-g)))) :
      (Ψ ((b-g)+(c-g))).allCoefficient J ^ 2 = 1 := by
    unfold EvenIdealRayCharacter.allCoefficient
    rw [dite_eq_left hJ, ite_eq_left hJC]
    exact congrArg Units.val (sourceQuadraticRayCharacter_sq F S₀ hζ ((b-g)+(c-g)) _)
  rw [sourceQuadraticHalfResidueDifference,
    quadraticHeckeMainTerm_radicalCutoffTail F (Ψ ((b-g)+(c-g))) hχ (m g) hm hmc H]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro e _
  exact (sourceQuadraticBlockRadicalRows_sum F S₀ g H
    (fun J => quadraticHeckeCutoffWeight F H J d e * (Ψ ((b-g)+(c-g))).allCoefficient (J*d*e))).symm

omit [IsTotallyComplex F] in
private theorem residual_source_pair (cols : Finset E) (g h t : E) (v : E → ℂ) :
    (∑ p ∈ (cols ×ˢ cols).filter (fun p : E × E => p.1 ⊓ p.2 = g),
      star (χ h (p.1-g) * (v p.1 * χ t (p.1-g))) *
        (χ h (p.2-g) * (v p.2 * χ t (p.2-g)))) =
      sourceQuadraticCutoffPairValue F S₀ hζ (sourceQuadraticSmallResidualColumns F S₀ cols g) h
        (fun b => sourceQuadraticSmallResidualCoeff F S₀ g v b * χ t b) := by
  rw [sourceQuadraticSmall_common_pair_reindex F S₀ cols g (fun b c =>
    star (χ h (b-g) * (v b * χ t (b-g))) * (χ h (c-g) * (v c * χ t (c-g))))]
  simp only [add_tsub_cancel_left, sourceQuadraticCutoffPairValue,
    sourceQuadraticSmallResidualCoeff]

/-- Exact residue cancellation as the retained-row source sum with canonical divisor twists. -/
theorem sourceQuadraticNormalizedResidueBlock_eq_main (M H : ℝ) (cols : Finset E)
    (u : E → ℂ) (g : E)
    (hcols : ∀ b ∈ cols, sourceReflectionIsSquarefree b)
    (hclass : ∀ b ∈ cols, ∀ c ∈ cols, b ⊓ c = g →
      sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c) :
    sourceQuadraticNormalizedResidueBlock F S₀ hζ M H cols u g =
      sourceQuadraticSmallResidueFactor F M *
        sourceQuadraticActualCutoffMainSum F S₀ hζ (R g) H (Rows g H)
          (sourceQuadraticSmallResidualColumns F S₀ cols g)
          (fun d e => sourceQuadraticBlockGoodIndex F S₀ g d + sourceQuadraticBlockGoodIndex F S₀ g e)
          (sourceQuadraticSmallResidualCoeff F S₀ g (sourceQuadraticDensityTwistedCoeff F S₀ g u)) := by
  unfold sourceQuadraticNormalizedResidueBlock
  congr 1
  let pairs := (cols ×ˢ cols).filter (fun p : E × E => p.1 ⊓ p.2 = g)
  have hp (p : E × E) (hp : p ∈ pairs) :
      sourceReflectionIsSquarefree p.1 ∧ sourceReflectionIsSquarefree p.2 ∧ p.1 ⊓ p.2 = g ∧
        sourceQuadraticLocalClass F S₀ hζ p.1 = sourceQuadraticLocalClass F S₀ hζ p.2 := by
    obtain ⟨hpcols, hpg⟩ := Finset.mem_filter.mp hp
    obtain ⟨hb, hc⟩ := Finset.mem_product.mp hpcols
    exact ⟨hcols p.1 hb, hcols p.2 hc, hpg, hclass p.1 hb p.2 hc hpg⟩
  have hterm (p : E × E) (hp' : p ∈ pairs) :
      star (u p.1) * u p.2 * quadraticHeckeCoprimeDensity F (C ((p.1-g)+(p.2-g))) *
          sourceQuadraticHalfResidueDifference F S₀ hζ H g ((p.1-g)+(p.2-g)) =
        ∑ d ∈ D g, ∑ e ∈ D g, ∑ h ∈ Rows g H,
          quadraticHeckeCutoffWeight F H (I h) d e *
            (star (χ h (p.1-g) * (sourceQuadraticDensityTwistedCoeff F S₀ g u p.1 *
                χ (sourceQuadraticBlockGoodIndex F S₀ g d + sourceQuadraticBlockGoodIndex F S₀ g e) (p.1-g))) *
              (χ h (p.2-g) * (sourceQuadraticDensityTwistedCoeff F S₀ g u p.2 *
                χ (sourceQuadraticBlockGoodIndex F S₀ g d + sourceQuadraticBlockGoodIndex F S₀ g e) (p.2-g)))) := by
    obtain ⟨hb, hc, hg, hcl⟩ := hp p hp'
    rw [sourceQuadraticPair_halfResidueDifference_tail F S₀ hζ H p.1 p.2 g hb hc hg hcl]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    apply Finset.sum_congr rfl
    intro h _
    have hpair := sourceQuadraticPair_radicalCutoff_pair F S₀ hζ
      (sourceQuadraticDensityTwistedCoeff F S₀ g u) p.1 p.2 g h hb hc hg hcl H d e
      ((HeckeIdealMobius.mem_divisors F (quadraticHeckeIdealRadical_ne_bot F (m g))).1 hd)
      ((HeckeIdealMobius.mem_divisors F (quadraticHeckeIdealRadical_ne_bot F (m g))).1 he)
    rw [quadraticHeckeCutoffTail_summand] at hpair
    rw [sourceQuadraticPair_density_twist F S₀ hζ p.1 p.2 g hb hc hg hcl u]
    simpa only [mul_assoc] using hpair
  change (∑ p ∈ pairs, _) = _
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  unfold sourceQuadraticActualCutoffMainSum sourceQuadraticCutoffMainSum
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  rw [← Finset.mul_sum]
  exact congrArg (quadraticHeckeCutoffWeight F H (I h) d e * ·)
    (residual_source_pair F S₀ hζ cols g h
      (sourceQuadraticBlockGoodIndex F S₀ g d + sourceQuadraticBlockGoodIndex F S₀ g e)
      (sourceQuadraticDensityTwistedCoeff F S₀ g u))

end
end ArtinMatthews.SourceEulerAssembly

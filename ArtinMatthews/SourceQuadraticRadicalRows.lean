module

public import ArtinMatthews.QuadraticHeckeIdealRadical
public import ArtinMatthews.SourceQuadraticSmallResidue
public import ArtinMatthews.SourceQuadraticActualCutoffMainBound
public import ArtinMatthews.QuadraticHeckeSmallResidue
public import ArtinMatthews.SourceQuadraticPairConductor
public import ArtinMatthews.SourceQuadraticPrimitive
public import ArtinMatthews.SourceReflectionExteriorRows
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain StandardAdelic VaryingKummerAnalytic SIntegerPrincipalization
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "E" => SourcePrimeExponents F S₀
local notation "I" => sourcePrimeExponentIdeal F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "Bad" => sourceQuadraticBlockBadIdeal F S₀

private theorem blockBadIdeal_ne_bot : Bad ≠ ⊥ := by
  unfold sourceQuadraticBlockBadIdeal
  exact Ideal.span_singleton_eq_bot.not.mpr
    (principalizingDenominator_ne_zero (sourceHilbertSeed F S₀))

/-- The squarefree modulus used for the fixed-bad and common-ideal cancellation. -/
def sourceQuadraticBlockRadical (g : E) : Ideal (𝓞 F) :=
  quadraticHeckeIdealRadical F (Bad * I g)

theorem sourceQuadraticBlockRadical_squarefree (g : E) :
    Squarefree (sourceQuadraticBlockRadical F S₀ g) :=
  quadraticHeckeIdealRadical_squarefree F _

theorem sourceQuadraticBlockRadical_eq (g : E) (hg : sourceReflectionIsSquarefree g) :
    sourceQuadraticBlockRadical F S₀ g = quadraticHeckeIdealRadical F Bad * I g := by
  rw [sourceQuadraticBlockRadical,
    quadraticHeckeIdealRadical_mul F (sourceQuadraticBlock_exterior_coprime F S₀ g).symm,
    quadraticHeckeIdealRadical_eq_self F ((sourceReflectionExteriorIdeal_squarefree F S₀ g).mpr hg)]

theorem sourceQuadraticBlockRadical_norm_le (g : E) :
    Ideal.absNorm (sourceQuadraticBlockRadical F S₀ g) ≤ Ideal.absNorm Bad * q g := by
  have h := quadraticHeckeIdealRadical_norm_le F
    (mul_ne_zero (blockBadIdeal_ne_bot F S₀) (sourcePrimeExponentIdeal_ne_bot F S₀ g))
  simpa only [sourceQuadraticBlockRadical, map_mul, sourcePrimeExponentIdeal_norm] using h

theorem sourceQuadraticBlockRadical_row_coprime (g : E) (H : ℝ)
    (J : Ideal (𝓞 F)) (hJ : J ∈ quadraticHeckeCoprimeCutoff F (sourceQuadraticBlockRadical F S₀ g) H) :
    IsCoprime J Bad := by
  have hc := (mem_quadraticHeckeCoprimeCutoff F).1 hJ |>.2.2
  have hm := mul_ne_zero (blockBadIdeal_ne_bot F S₀)
    (sourcePrimeExponentIdeal_ne_bot F S₀ g)
  have hcop := (quadraticHeckeIdealRadical_coprime_iff F hm J).1 hc
  exact hcop.of_isCoprime_of_dvd_right (dvd_mul_right _ _)

/-- Every retained radical-coprime row is its actual exterior exponent label. -/
def sourceQuadraticBlockRadicalRow (g : E) (H : ℝ)
    (J : {J : Ideal (𝓞 F) // J ∈ quadraticHeckeCoprimeCutoff F (sourceQuadraticBlockRadical F S₀ g) H}) : E :=
  sourceExteriorIdealExponents F S₀
    ⟨J.val, ((mem_quadraticHeckeCoprimeCutoff F).1 J.property).1.ne_zero,
      sourceQuadraticBlockRadical_row_coprime F S₀ g H J.val J.property⟩

theorem sourceQuadraticBlockRadicalRow_ideal (g : E) (H : ℝ)
    (J : {J : Ideal (𝓞 F) // J ∈ quadraticHeckeCoprimeCutoff F (sourceQuadraticBlockRadical F S₀ g) H}) :
    I (sourceQuadraticBlockRadicalRow F S₀ g H J) = J.val :=
  sourceExteriorIdealExponents_recover F S₀ _

theorem sourceQuadraticBlockRadicalRow_squarefree (g : E) (H : ℝ)
    (J : {J : Ideal (𝓞 F) // J ∈ quadraticHeckeCoprimeCutoff F (sourceQuadraticBlockRadical F S₀ g) H}) :
    sourceReflectionIsSquarefree (sourceQuadraticBlockRadicalRow F S₀ g H J) := by
  apply (sourceReflectionExteriorIdeal_squarefree F S₀ _).mp
  rw [sourceQuadraticBlockRadicalRow_ideal]
  exact ((mem_quadraticHeckeCoprimeCutoff F).1 J.property).1

theorem sourceQuadraticBlockRadicalRow_norm (g : E) (H : ℝ)
    (J : {J : Ideal (𝓞 F) // J ∈ quadraticHeckeCoprimeCutoff F (sourceQuadraticBlockRadical F S₀ g) H}) :
    q (sourceQuadraticBlockRadicalRow F S₀ g H J) = Ideal.absNorm J.val := by
  rw [← sourcePrimeExponentIdeal_norm, sourceQuadraticBlockRadicalRow_ideal]

theorem sourceQuadraticBlockRadicalRow_norm_le (g : E) (H : ℝ)
    (J : {J : Ideal (𝓞 F) // J ∈ quadraticHeckeCoprimeCutoff F (sourceQuadraticBlockRadical F S₀ g) H}) :
    (q (sourceQuadraticBlockRadicalRow F S₀ g H J) : ℝ) ≤ H := by
  rw [sourceQuadraticBlockRadicalRow_norm]
  exact ((mem_quadraticHeckeCoprimeCutoff F).1 J.property).2.1

theorem sourceQuadraticBlockRadicalRow_injective (g : E) (H : ℝ) :
    Function.Injective (sourceQuadraticBlockRadicalRow F S₀ g H) := by
  intro J L h
  apply Subtype.ext
  have hI := congrArg I h
  simpa only [sourceQuadraticBlockRadicalRow_ideal] using hI

/-- The finite exterior row set corresponding to the retained ideal cutoff. -/
def sourceQuadraticBlockRadicalRows (g : E) (H : ℝ) : Finset E :=
  (quadraticHeckeCoprimeCutoff F (sourceQuadraticBlockRadical F S₀ g) H).attach.image
    (sourceQuadraticBlockRadicalRow F S₀ g H)

theorem sourceQuadraticBlockRadicalRows_spec (g : E) (H : ℝ) (h : E)
    (hh : h ∈ sourceQuadraticBlockRadicalRows F S₀ g H) :
    sourceReflectionIsSquarefree h ∧ (q h : ℝ) ≤ H := by
  obtain ⟨J, _, rfl⟩ := Finset.mem_image.mp hh
  exact ⟨sourceQuadraticBlockRadicalRow_squarefree F S₀ g H J,
    sourceQuadraticBlockRadicalRow_norm_le F S₀ g H J⟩

/-- Ideal test sums on the retained cutoff are literal sums over the exterior rows. -/
theorem sourceQuadraticBlockRadicalRows_sum (g : E) (H : ℝ)
    (f : Ideal (𝓞 F) → ℂ) :
    (∑ h ∈ sourceQuadraticBlockRadicalRows F S₀ g H, f (I h)) =
      ∑ J ∈ quadraticHeckeCoprimeCutoff F (sourceQuadraticBlockRadical F S₀ g) H, f J := by
  unfold sourceQuadraticBlockRadicalRows
  rw [Finset.sum_image]
  · simp only [sourceQuadraticBlockRadicalRow_ideal, Finset.sum_attach]
  · intro J _ L _ h
    exact sourceQuadraticBlockRadicalRow_injective F S₀ g H h

variable [IsTotallyComplex F] {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "C" => sourceQuadraticConductor F S₀ hζ
local notation "Ψ" => sourceQuadraticRayCharacter F S₀ hζ

/-- The actual Small residue has the combined-modulus form used by radical cancellation. -/
theorem sourceQuadraticSmallResidue_combinedModulus (g e : E)
    (hmc : IsCoprime (Bad * I g) (C e)) {M : ℝ} (hM : 0 < M) (H : ℝ) :
    (∑' a : {J : Ideal (𝓞 F) // Squarefree J},
      if IsCoprime a.val Bad ∧ IsCoprime a.val (I g) ∧ (Ideal.absNorm a.val : ℝ) ≤ H then
        (Ψ e).allCoefficient a.val *
          ((dedekindZeta_residue F : ℂ) *
            (Real.sqrt (M / (Ideal.absNorm a.val : ℝ)) : ℂ) *
            ((1 / 2 : ℂ) * mellin (fun t : ℝ => (sourceQuadraticB2Bump t : ℂ)) (1 / 2)) *
            quadraticHeckeCoprimeDensity F (Bad * I g * C e)) else 0) =
      sourceQuadraticSmallResidueFactor F M * quadraticHeckeCoprimeDensity F (C e) *
        quadraticHeckeCoprimeDensity F (Bad * I g) *
        ∑ a ∈ quadraticHeckeCoprimeCutoff F (Bad * I g) H,
          quadraticHeckeHalfCoefficient F (Ψ e) a := by
  have hgC : IsCoprime (I g) (C e) := hmc.of_isCoprime_of_dvd_left (dvd_mul_left _ _)
  have hm : Bad * I g ≠ ⊥ := mul_ne_zero (blockBadIdeal_ne_bot F S₀)
    (sourcePrimeExponentIdeal_ne_bot F S₀ g)
  have hρ : quadraticHeckeCoprimeDensity F (Bad * C e) * quadraticHeckeCoprimeDensity F (I g) =
      quadraticHeckeCoprimeDensity F (C e) * quadraticHeckeCoprimeDensity F (Bad * I g) := by
    calc
      _ = quadraticHeckeCoprimeDensity F (Bad * I g * C e) :=
        (sourceQuadraticSmallModulus_density F S₀ hζ g e hgC).symm
      _ = quadraticHeckeCoprimeDensity F (Bad * I g) * quadraticHeckeCoprimeDensity F (C e) :=
        quadraticHeckeCoprimeDensity_mul F hm (sourceQuadraticConductor_ne_bot F S₀ hζ e) hmc
      _ = _ := mul_comm _ _
  have hsum : (∑ a ∈ quadraticHeckeCoprimeCutoff F (I g) H,
      if IsCoprime a Bad then quadraticHeckeHalfCoefficient F (Ψ e) a else 0) =
      ∑ a ∈ quadraticHeckeCoprimeCutoff F (Bad * I g) H,
        quadraticHeckeHalfCoefficient F (Ψ e) a := by
    rw [quadraticHeckeCoprimeCutoff_mul F Bad (I g) H, Finset.sum_filter]
  calc
    _ = sourceQuadraticSmallResidueFactor F M *
        quadraticHeckeCoprimeDensity F (Bad * C e) * quadraticHeckeCoprimeDensity F (I g) *
        ∑ a ∈ quadraticHeckeCoprimeCutoff F (I g) H,
          if IsCoprime a Bad then quadraticHeckeHalfCoefficient F (Ψ e) a else 0 :=
      sourceQuadraticSmallResidue_eq_halfCoefficient F S₀ hζ g e hgC hM H
    _ = sourceQuadraticSmallResidueFactor F M *
        (quadraticHeckeCoprimeDensity F (Bad * C e) * quadraticHeckeCoprimeDensity F (I g)) *
        ∑ a ∈ quadraticHeckeCoprimeCutoff F (I g) H,
          if IsCoprime a Bad then quadraticHeckeHalfCoefficient F (Ψ e) a else 0 := by ring
    _ = _ := by rw [hρ, hsum]; ring

/-- The full and Small principal factors cancel through the squarefree radical of the combined modulus. -/
theorem sourceQuadraticCommonPair_radicalResidueDifference (b c g : E)
    (hb : sourceReflectionIsSquarefree b) (hc : sourceReflectionIsSquarefree c)
    (hg : b ⊓ c = g)
    (hclass : sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c)
    (M H : ℝ) :
    sourceQuadraticSmallResidueFactor F M *
        quadraticHeckeCoprimeDensity F (C ((b - g) + (c - g))) *
      ((∑ a ∈ quadraticHeckeSquarefreeCutoff F H,
          quadraticHeckeHalfCoefficient F (Ψ ((b - g) + (c - g))) a) *
          (∑ d ∈ HeckeIdealMobius.divisors F (Bad * I g), (UniqueFactorizationMonoid.moebius d : ℂ) *
            quadraticHeckeHalfCoefficient F (Ψ ((b - g) + (c - g))) d) -
        (∑ a ∈ quadraticHeckeCoprimeCutoff F (Bad * I g) H,
          quadraticHeckeHalfCoefficient F (Ψ ((b - g) + (c - g))) a) *
          quadraticHeckeCoprimeDensity F (Bad * I g)) =
    sourceQuadraticSmallResidueFactor F M *
        quadraticHeckeCoprimeDensity F (C ((b - g) + (c - g))) *
      ∑ B ∈ quadraticHeckeCutoffAnnulus F (sourceQuadraticBlockRadical F S₀ g) H,
        quadraticHeckeCutoffCoefficient F (sourceQuadraticBlockRadical F S₀ g) H B *
          quadraticHeckeHalfCoefficient F (Ψ ((b - g) + (c - g))) B := by
  have hm : Bad * I g ≠ ⊥ := mul_ne_zero (blockBadIdeal_ne_bot F S₀)
    (sourcePrimeExponentIdeal_ne_bot F S₀ g)
  have hmc : IsCoprime (Bad * I g) (C ((b - g) + (c - g))) := by
    rw [sourceQuadraticPairConductor_eq_product F S₀ hζ b c g hb hc hg hclass]
    exact sourceQuadratic_commonModulus_coprime_residualProduct F S₀ b c g hb hc
  have hχ (J : Ideal (𝓞 F)) (hJ : J ≠ ⊥)
      (hJC : IsCoprime J (C ((b - g) + (c - g)))) :
      (Ψ ((b - g) + (c - g))).allCoefficient J ^ 2 = 1 := by
    unfold EvenIdealRayCharacter.allCoefficient
    rw [dite_eq_left hJ, ite_eq_left hJC]
    exact congrArg Units.val (sourceQuadraticRayCharacter_sq F S₀ hζ ((b - g) + (c - g)) _)
  exact congrArg (fun z : ℂ => sourceQuadraticSmallResidueFactor F M *
      quadraticHeckeCoprimeDensity F (C ((b - g) + (c - g))) * z)
    (quadraticHeckeMainTerm_radicalCutoffGrouped F (Ψ ((b - g) + (c - g))) hχ (Bad * I g) hm hmc H)

/-- The fixed bad ideal contributes only a fixed fourth-power constant to the main-term estimate. -/
theorem sourceQuadraticBlockRadical_main_bound {α : ℝ}
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
    (hE : QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) α)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ cBound : ℝ, 0 < cBound ∧ ∀ M P H : ℝ, 1 ≤ M → 1 ≤ P → 1 ≤ H → H ≤ M →
      ∀ g : E, ∀ rows cols : Finset E,
      (∀ h ∈ rows, sourceReflectionIsSquarefree h ∧ (q h : ℝ) ≤ H) →
      (∀ b ∈ cols, sourceReflectionIsSquarefree b ∧ (q b : ℝ) ≤ P) →
      ∀ (twistIndex : Ideal (𝓞 F) → Ideal (𝓞 F) → E) (coeff : E → ℂ),
      ‖(Real.sqrt M : ℂ) * sourceQuadraticActualCutoffMainSum F S₀ hζ
          (sourceQuadraticBlockRadical F S₀ g) H rows cols twistIndex coeff‖ ≤
        cBound * (q g : ℝ) ^ 4 * (M * P) ^ ε *
          (Real.sqrt M * H ^ (α - 1 / 2) + Real.sqrt (M / H) * P) *
            ∑ b ∈ cols, ‖coeff b‖ ^ 2 := by
  obtain ⟨cBound, hC, hb⟩ := sourceQuadraticActualCutoffMainSum_bound F S₀ hζ htrace hE ε hε
  have hBad : 0 < (Ideal.absNorm Bad : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (blockBadIdeal_ne_bot F S₀))
  refine ⟨cBound * (Ideal.absNorm Bad : ℝ) ^ 4, by positivity, ?_⟩
  intro M P H hM hP hH hHM g rows cols hrows hcols twistIndex coeff
  have hbound := hb M P H hM hP hH hHM (sourceQuadraticBlockRadical F S₀ g)
    (sourceQuadraticBlockRadical_squarefree F S₀ g) rows cols hrows hcols twistIndex coeff
  have hn : (Ideal.absNorm (sourceQuadraticBlockRadical F S₀ g) : ℝ) ≤
      (Ideal.absNorm Bad : ℝ) * (q g : ℝ) := by
    exact_mod_cast sourceQuadraticBlockRadical_norm_le F S₀ g
  calc
    _ ≤ cBound * (Ideal.absNorm (sourceQuadraticBlockRadical F S₀ g) : ℝ) ^ 4 * (M * P) ^ ε *
        (Real.sqrt M * H ^ (α - 1 / 2) + Real.sqrt (M / H) * P) *
          ∑ b ∈ cols, ‖coeff b‖ ^ 2 := hbound
    _ ≤ cBound * ((Ideal.absNorm Bad : ℝ) * (q g : ℝ)) ^ 4 * (M * P) ^ ε *
        (Real.sqrt M * H ^ (α - 1 / 2) + Real.sqrt (M / H) * P) *
          ∑ b ∈ cols, ‖coeff b‖ ^ 2 := by gcongr
    _ = _ := by rw [mul_pow]; ring

end
end ArtinMatthews.SourceEulerAssembly

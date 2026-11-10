module

public import ArtinMatthews.SourceQuadraticBlockDualCutoff
public import ArtinMatthews.SourceQuadraticLocalClasses
public import ArtinMatthews.QuadraticDualTailArithmetic
public import ArtinMatthews.QuadraticHeckeMobiusDivisorMoment
public import ArtinMatthews.SourcePrimeNormSummability
public import ArtinMatthews.SourceQuadraticPairScale
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain Set VaryingKummerAnalytic UniqueFactorizationMonoid QuadraticScale
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "Ψ" => sourceQuadraticRayCharacter F S₀ hζ

theorem sourceQuadraticBlockDualPrefactor_norm_le {M : ℝ} (hM : 0 < M) (e : E)
    (d : Ideal (𝓞 F)) (hd : 0 < (Ideal.absNorm d : ℝ)) :
    ‖sourceQuadraticBlockDualPrefactor F S₀ hζ M e d‖ ≤
      ‖(moebius d : ℂ)‖ * (M / (Ideal.absNorm d : ℝ) /
        Real.sqrt (Ideal.absNorm (sourceQuadraticConductor F S₀ hζ e) : ℝ)) := by
  have hQ : 0 < (Ideal.absNorm (sourceQuadraticConductor F S₀ hζ e) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (sourceQuadraticConductor_ne_bot F S₀ hζ e))
  have hx : 0 ≤ M / (Ideal.absNorm d : ℝ) /
      Real.sqrt (Ideal.absNorm (sourceQuadraticConductor F S₀ hζ e) : ℝ) := by positivity
  rw [sourceQuadraticBlockDualPrefactor, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hx]
  simpa only [mul_one] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left ((Ψ e).allCoefficient_norm_le_one d) (norm_nonneg _)) hx

theorem sourceQuadraticBlockDualScaledNorm_le {M : ℝ} (hM : 0 < M) (e : E)
    (d : Ideal (𝓞 F)) (hd : 0 < (Ideal.absNorm d : ℝ)) (σ : ℝ) :
    ‖sourceQuadraticBlockDualPrefactor F S₀ hζ M e d‖ *
        (sourceQuadraticBlockDualScale F S₀ hζ M e d) ^ (-σ) ≤
      (M ^ (1 - σ) * (Ideal.absNorm (sourceQuadraticConductor F S₀ hζ e) : ℝ) ^ (σ - 1 / 2)) *
        (‖(moebius d : ℂ)‖ * (Ideal.absNorm d : ℝ) ^ (σ - 1)) := by
  let Q : ℝ := Ideal.absNorm (sourceQuadraticConductor F S₀ hζ e)
  have hQ : 0 < Q := by
    dsimp only [Q]
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (sourceQuadraticConductor_ne_bot F S₀ hζ e))
  calc
    _ ≤ (‖(moebius d : ℂ)‖ * (M / (Ideal.absNorm d : ℝ) / Real.sqrt Q)) *
        (M / (Ideal.absNorm d : ℝ) / Q) ^ (-σ) :=
      mul_le_mul_of_nonneg_right (sourceQuadraticBlockDualPrefactor_norm_le F S₀ hζ hM e d hd)
        (Real.rpow_nonneg (by positivity) _)
    _ = _ := by
      rw [mul_assoc, quadraticDualTail_scale_eq hM hd hQ σ]
      ring

/-- The original finite divisor factor is bounded uniformly in the source pair. -/
theorem sourceQuadraticB3_divisor_tail_bound (σ : ℝ) (hσ : 2 ≤ σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M P K : ℝ), 0 < M → 0 < P → 0 < K →
      ∀ (b c g : E), sourceReflectionIsSquarefree b → sourceReflectionIsSquarefree c →
      b ⊓ c = g → sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c →
      (q b : ℝ) ≤ 2 * P → (q c : ℝ) ≤ 2 * P →
      (∑ d ∈ HeckeIdealMobius.divisors F (sourceQuadraticBlockModulus F S₀ g),
        ‖sourceQuadraticBlockDualPrefactor F S₀ hζ M ((b - g) + (c - g)) d‖ *
          (sourceQuadraticBlockDualScale F S₀ hζ M ((b - g) + (c - g)) d) ^ (-σ) *
            K ^ (2 - σ)) ≤
        C * (q g : ℝ) ^ 4 * (M ^ (1 - σ) * P ^ (2 * σ - 1) * K ^ (2 - σ)) := by
  obtain ⟨C, hC, hmom⟩ := quadraticHeckeMobiusDivisorMoment_bound F
  let B : ℝ := Ideal.absNorm (sourceQuadraticBlockBadIdeal F S₀)
  let C₁ := C * B ^ σ * 4 ^ (σ - 1 / 2)
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁, B]; positivity
  refine ⟨C₁, hC₁, ?_⟩
  intro M P K hM hP hK b c g hb hc hg hclass hbP hcP
  let e := (b - g) + (c - g)
  let Q : ℝ := Ideal.absNorm (sourceQuadraticConductor F S₀ hζ e)
  let I := sourceQuadraticBlockModulus F S₀ g
  have hI : I ≠ ⊥ := sourceQuadraticBlockModulus_ne_bot F S₀ g
  have hQ : 0 < Q := by
    dsimp only [Q]
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (sourceQuadraticConductor_ne_bot F S₀ hζ e))
  have hqg : 1 ≤ (q g : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (sourcePrimeExponentNorm_pos F S₀ g).ne'
  have hscale : (q g : ℝ) ^ 2 * Q ≤ 4 * P ^ 2 := by
    change (q g : ℝ) ^ 2 *
      (Ideal.absNorm (sourceQuadraticConductor F S₀ hζ ((b - g) + (c - g))) : ℝ) ≤ _
    rw [sourceQuadraticPairConductor_norm_scaled F S₀ hζ b c g hb hc hg hclass]
    calc
      _ ≤ (2 * P) * (2 * P) := mul_le_mul hbP hcP (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring
  have hmod : (Ideal.absNorm I : ℝ) = B * (q g : ℝ) := by
    dsimp [I, B, sourceQuadraticBlockModulus]
    rw [map_mul, Nat.cast_mul, sourcePrimeExponentIdeal_norm]
  have hconductor : (Ideal.absNorm I : ℝ) ^ σ * Q ^ (σ - 1 / 2) ≤
      B ^ σ * (4 ^ (σ - 1 / 2) * P ^ (2 * σ - 1)) := by
    calc
      _ = B ^ σ * ((q g : ℝ) ^ σ * Q ^ (σ - 1 / 2)) := by
        rw [hmod, Real.mul_rpow (by dsimp [B]; positivity) (Nat.cast_nonneg _)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (quadraticDualTail_conductor_le hqg hQ hP (by linarith) hscale)
        (Real.rpow_nonneg (by dsimp [B]; positivity) _)
  have hsum : (∑ d ∈ HeckeIdealMobius.divisors F I,
      ‖sourceQuadraticBlockDualPrefactor F S₀ hζ M e d‖ *
        (sourceQuadraticBlockDualScale F S₀ hζ M e d) ^ (-σ)) ≤
      (M ^ (1 - σ) * Q ^ (σ - 1 / 2)) * (C * (Ideal.absNorm I : ℝ) ^ σ) := by
    calc
      _ ≤ ∑ d ∈ HeckeIdealMobius.divisors F I,
          (M ^ (1 - σ) * Q ^ (σ - 1 / 2)) *
            (‖(moebius d : ℂ)‖ * (Ideal.absNorm d : ℝ) ^ (σ - 1)) := by
        apply Finset.sum_le_sum
        intro d hd
        exact sourceQuadraticBlockDualScaledNorm_le F S₀ hζ hM e d
          (sourceQuadraticBlock_divisorNorm_pos F S₀ g d hd) σ
      _ = (M ^ (1 - σ) * Q ^ (σ - 1 / 2)) *
          ∑ d ∈ HeckeIdealMobius.divisors F I,
            ‖(moebius d : ℂ)‖ * (Ideal.absNorm d : ℝ) ^ (σ - 1) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hmom I hI σ (by linarith)) (by positivity)
  have hraw : (∑ d ∈ HeckeIdealMobius.divisors F I,
      ‖sourceQuadraticBlockDualPrefactor F S₀ hζ M e d‖ *
        (sourceQuadraticBlockDualScale F S₀ hζ M e d) ^ (-σ) * K ^ (2 - σ)) ≤
      C₁ * (M ^ (1 - σ) * P ^ (2 * σ - 1) * K ^ (2 - σ)) := by
    calc
      _ = (∑ d ∈ HeckeIdealMobius.divisors F I,
          ‖sourceQuadraticBlockDualPrefactor F S₀ hζ M e d‖ *
            (sourceQuadraticBlockDualScale F S₀ hζ M e d) ^ (-σ)) * K ^ (2 - σ) :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ ((M ^ (1 - σ) * Q ^ (σ - 1 / 2)) * (C * (Ideal.absNorm I : ℝ) ^ σ)) *
          K ^ (2 - σ) := mul_le_mul_of_nonneg_right hsum (Real.rpow_nonneg hK.le _)
      _ = (C * M ^ (1 - σ)) * ((Ideal.absNorm I : ℝ) ^ σ * Q ^ (σ - 1 / 2)) *
          K ^ (2 - σ) := by ring
      _ ≤ (C * M ^ (1 - σ)) * (B ^ σ * (4 ^ (σ - 1 / 2) * P ^ (2 * σ - 1))) *
          K ^ (2 - σ) := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hconductor (by positivity)) (Real.rpow_nonneg hK.le _)
      _ = _ := by dsimp [C₁]; ring
  have hq4 : 1 ≤ (q g : ℝ) ^ 4 := one_le_pow₀ hqg
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (le_mul_of_one_le_right hC₁ hq4) (by positivity))

end
end ArtinMatthews.SourceEulerAssembly

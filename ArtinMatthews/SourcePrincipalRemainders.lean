module

public import ArtinMatthews.SourcePrincipalContourIntegrals
public import ArtinMatthews.SourceProbeComparison
public import ArtinMatthews.SourcePrincipalContourGeometry
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
public import Mathlib.Tactic.Basify
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

/-! The exact two principal remainder contours have the manuscript power saving. -/

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain Asymptotics Filter Set
open VaryingKummerAnalytic QuadraticWeil SourcePhysical
open scoped NumberField Classical Topology
noncomputable section

theorem sourcePrincipalTripleScale_source {Z : ℝ} (hZ : 0 < Z) (a b c : ℝ) :
    sourcePoissonTripleScale (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z a b c =
      Z ^ sourceContourExponent a b c * Real.exp ((a + c - 1) ^ 2) := by
  unfold sourcePoissonTripleScale
  rw [← Real.rpow_mul hZ.le (9 / 10 : ℝ) (1 / 2 - c),
    ← Real.rpow_mul hZ.le (133 / 1000 : ℝ) (b - 1), ← Real.rpow_add hZ, ← Real.rpow_add hZ]
  congr 2
  unfold sourceContourExponent
  ring

variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
variable (v : InfinitePlace F)
local notation "σ₁" => sourcePrincipalSigma
local notation "z₁" => sourcePrincipalZetaLine

def sourcePrincipalPoissonWRemainder (Z : ℝ) : ℂ :=
  sourcePrincipalPoissonIntegral F hζ S₀ η v (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z σ₁ (95 / 100) z₁

def sourcePrincipalPoissonZRemainder (Z : ℝ) : ℂ :=
  sourcePrincipalPoissonResidueIntegral F hζ S₀ η v (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z σ₁ (16 / 100)

theorem sourcePrincipalPoissonWRemainder_bigO
    (hJ : J ≠ ⊥) (hcut : principalAngularCutoff F J ⊆ sourceHilbertSet F S₀) :
    sourcePrincipalPoissonWRemainder F hζ S₀ η v =O[atTop]
      (fun Z : ℝ => Z ^ (7 / 15 - 1 / 2000 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := sourcePrincipalPoissonIntegral_integrable_and_bound F hζ S₀ η v hJ hcut
    (a := σ₁) le_rfl (by norm_num : (95 / 100 : ℝ) ∈ Icc (95 / 100 : ℝ) 4)
    sourcePrincipalZetaLine_mem (by norm_num) sourcePrincipalZetaLine_gt_sixth.ne'
  apply IsBigO.of_bound (C * Real.exp ((σ₁ + z₁ - 1) ^ 2))
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Z hZ
  have hZ' : 0 < Z := zero_lt_one.trans_le hZ
  have h := (hb (X := Z ^ (9 / 10 : ℝ)) (Y := Z ^ (133 / 1000 : ℝ))
    (Real.rpow_pos_of_pos hZ' _) (Real.rpow_pos_of_pos hZ' _) hZ').2
  change ‖sourcePrincipalPoissonWRemainder F hζ S₀ η v Z‖ ≤ _ at h
  rw [sourcePrincipalTripleScale_source hZ'] at h
  have he : sourceContourExponent σ₁ (95 / 100) z₁ ≤ 7 / 15 - 1 / 2000 := by
    exact sourceContourExponent_w_remainder.le
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hZ'.le _)]
  calc
    _ ≤ C * (Z ^ sourceContourExponent σ₁ (95 / 100) z₁ * Real.exp ((σ₁ + z₁ - 1) ^ 2)) := h
    _ = (C * Real.exp ((σ₁ + z₁ - 1) ^ 2)) * Z ^ sourceContourExponent σ₁ (95 / 100) z₁ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ he)
      (mul_nonneg hC (Real.exp_nonneg _))

theorem sourcePrincipalPoissonZRemainder_bigO
    (hJ : J ≠ ⊥) (hcut : principalAngularCutoff F J ⊆ sourceHilbertSet F S₀) :
    sourcePrincipalPoissonZRemainder F hζ S₀ η v =O[atTop]
      (fun Z : ℝ => Z ^ (7 / 15 - 1 / 2000 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := sourcePrincipalPoissonResidueIntegral_integrable_and_bound F hζ S₀ η v hJ hcut
    (a := σ₁) le_rfl (by norm_num : (16 / 100 : ℝ) ∈ Icc (16 / 100 : ℝ) 2) (by norm_num)
  apply IsBigO.of_bound (C * Real.exp ((σ₁ + 16 / 100 - 1) ^ 2))
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Z hZ
  have hZ' : 0 < Z := zero_lt_one.trans_le hZ
  have h := (hb (X := Z ^ (9 / 10 : ℝ)) (Y := Z ^ (133 / 1000 : ℝ))
    (Real.rpow_pos_of_pos hZ' _) (Real.rpow_pos_of_pos hZ' _) hZ').2
  change ‖sourcePrincipalPoissonZRemainder F hζ S₀ η v Z‖ ≤ _ at h
  rw [sourcePrincipalTripleScale_source hZ'] at h
  have he : sourceContourExponent σ₁ 1 (16 / 100) ≤ 7 / 15 - 1 / 2000 :=
    sourceContourExponent_z_remainder.le
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hZ'.le _)]
  calc
    _ ≤ C * (Z ^ sourceContourExponent σ₁ 1 (16 / 100) * Real.exp ((σ₁ + 16 / 100 - 1) ^ 2)) := h
    _ = (C * Real.exp ((σ₁ + 16 / 100 - 1) ^ 2)) * Z ^ sourceContourExponent σ₁ 1 (16 / 100) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ he)
      (mul_nonneg hC (Real.exp_nonneg _))

end
end ArtinMatthews.SourceEulerAssembly

module

public import ArtinMatthews.QuadraticHeckeScaleOptimizer
public import ArtinMatthews.SourceQuadraticSieveEnergy
public import ArtinMatthews.SourceQuadraticSupport
public import ArtinMatthews.SourceQuadraticTagPool
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

/-! The actual GL scale comparison and bootstrap for the exterior
quadratic family. The field degree enters only the logarithmic
enlargement, which the scale optimizer absorbs. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain VaryingKummerAnalytic StandardAdelic QuadraticScale
open scoped NumberField Classical BigOperators

noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
include htrace

local notation "d" => Module.finrank ℚ F
local notation "w" => sourceReflectionPrimeNorm F S₀
local notation "energy" => sourceQuadraticDyadicEnergy F S₀ hζ

theorem sourceQuadraticDyadicEnergy_enlarge :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ M N L : ℝ, 1 ≤ M → 1 ≤ N →
      A * (1 + Real.log (M * N)) ^ (2 * d : ℕ) * M ≤ L →
      energy M N ≤ 16 * energy L N := by
  obtain ⟨A, hA, hpool⟩ := exists_sourceQuadraticTagPool F S₀
  refine ⟨(3 / 2) * A, by linarith, ?_⟩
  intro M N L hM hN hscale
  let U := 1 + Real.log (M * N)
  have hM0 := zero_lt_one.trans_le hM
  have hMN := one_le_mul_of_one_le_of_one_le hM hN
  have hU : 1 ≤ U := by dsimp [U]; linarith [Real.log_nonneg hMN]
  have hpos : 0 ≤ A * U ^ (2 * d : ℕ) := by positivity
  have hL : 1 ≤ L := by
    have hh : 1 ≤ (3 / 2 * A) * U ^ (2 * d : ℕ) * M := by
      exact one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hU)) hM
    exact hh.trans hscale
  have hsmall : A * U ^ (2 * d : ℕ) ≤ L / M := by
    apply (le_div_iff₀ hM0).mpr
    calc
      _ ≤ 3 / 2 * (A * U ^ (2 * d : ℕ) * M) := by
        exact le_mul_of_one_le_left (mul_nonneg hpos hM0.le) (by norm_num)
      _ = (3 / 2 * A) * U ^ (2 * d : ℕ) * M := by ring
      _ ≤ _ := hscale
  have hbig : A * U ^ (2 * d : ℕ) ≤ L / ((3 / 2) * M) := by
    apply (le_div_iff₀ (by positivity : 0 < (3 / 2) * M)).mpr
    calc
      _ = (3 / 2 * A) * U ^ (2 * d : ℕ) * M := by ring
      _ ≤ _ := hscale
  obtain ⟨lo, hlo⟩ := hpool M N (L / M) hM hN hsmall
  obtain ⟨hi, hhi⟩ := hpool M N (L / ((3 / 2) * M)) hM hN hbig
  have hlarge := (sourceQuadraticAdmissible_iff_support F S₀ hζ L N (energy L N)).mp
    (sourceQuadraticDyadicEnergy_admissible F S₀ hζ htrace hL hN)
  apply sourceQuadraticDyadicEnergy_le F S₀ hζ
  apply (sourceQuadraticAdmissible_iff_support F S₀ hζ M N (16 * energy L N)).mpr
  refine ⟨mul_nonneg (by norm_num) hlarge.1, ?_⟩
  exact annularEnergyBound_compare w (sourceReflection_primeNorm_two_le F S₀)
    (sourceQuadraticSupportKernel F S₀ hζ) (sourceQuadraticSupportKernel_norm_le F S₀ hζ)
    (fun t r c h _ => sourceQuadraticSupportKernel_union F S₀ hζ t r c h)
    (sourceQuadraticSupportKernel_norm_eq F S₀ hζ) hM hN (zero_lt_one.trans_le hL) hlarge.1
    lo hi hlo hhi hlarge.2

theorem sourceQuadraticDyadicEnergy_exponent_one_of_poisson
    (hpoisson : ∀ a : ℝ, 1 < a → QuadraticHeckeSieveExponentBound energy a →
      QuadraticHeckePoissonScaleBound energy a) :
    QuadraticHeckeSieveExponentBound energy 1 := by
  obtain ⟨A, hA, h⟩ := sourceQuadraticDyadicEnergy_enlarge F S₀ hζ htrace
  exact quadraticHeckeSieveExponentBound_bootstrap_of_poisson_scale energy
    (sourceQuadraticDyadicEnergy_exponent_two F S₀ hζ htrace) A hA (2 * d) h hpoisson

end
end ArtinMatthews.SourceEulerAssembly

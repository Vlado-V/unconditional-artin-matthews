module

public import ArtinMatthews.SourceQuadraticBlockPoissonExpansion
public import ArtinMatthews.QuadraticHeckeRayDualTail
public import ArtinMatthews.QuadraticHeckeRayDualCutoff
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
open NumberField IsDedekindDomain Set VaryingKummerAnalytic Filter
open UniqueFactorizationMonoid
open scoped NumberField Classical BigOperators ContDiff Topology
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "J₀" => {J : Ideal (𝓞 F) // J ≠ ⊥}
local notation "Ψ" => sourceQuadraticRayCharacter F S₀ hζ
local notation "A" => quadraticHeckeFieldScale F
local notation "r" => InfinitePlace.nrComplexPlaces F

def sourceQuadraticBlockDualScale (M : ℝ) (e : E) (d : Ideal (𝓞 F)) : ℝ :=
  (M / (Ideal.absNorm d : ℝ)) /
    (Ideal.absNorm (sourceQuadraticConductor F S₀ hζ e) : ℝ)

def sourceQuadraticBlockDualPrefactor (M : ℝ) (e : E) (d : Ideal (𝓞 F)) : ℂ :=
  (moebius d : ℂ) * (Ψ e).allCoefficient d *
    ((M / (Ideal.absNorm d : ℝ)) /
      Real.sqrt (Ideal.absNorm (sourceQuadraticConductor F S₀ hζ e) : ℝ) : ℝ)

omit [IsTotallyComplex F] in
theorem sourceQuadraticBlockDualScale_pos {M : ℝ} (hM : 0 < M) (g e : E)
    (d : Ideal (𝓞 F))
    (hd : d ∈ HeckeIdealMobius.divisors F (sourceQuadraticBlockModulus F S₀ g)) :
    0 < sourceQuadraticBlockDualScale F S₀ hζ M e d := by
  apply div_pos (div_pos hM (sourceQuadraticBlock_divisorNorm_pos F S₀ g d hd))
  exact_mod_cast Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr (sourceQuadraticConductor_ne_bot F S₀ hζ e))

theorem sourceQuadraticBlockDualTerm_eq (M : ℝ) (e : E) (d : Ideal (𝓞 F)) (J : J₀) :
    quadraticHeckeRayDualTerm F (Ψ e) A r sourceQuadraticBlockProfile
        (sourceQuadraticBlockDualScale F S₀ hζ M e d) J =
      (Ψ e).allCoefficient J.val *
        quadraticHeckeDualProfile A r sourceQuadraticBlockProfile
          ((Ideal.absNorm J.val : ℝ) * (M / (Ideal.absNorm d : ℝ)) /
            (Ideal.absNorm (sourceQuadraticConductor F S₀ hζ e) : ℝ)) := by
  unfold quadraticHeckeRayDualTerm sourceQuadraticBlockDualScale
  congr 2
  ring

theorem sourceQuadraticBlockDual_norm_summable {M : ℝ} (hM : 0 < M) (g e : E)
    (d : Ideal (𝓞 F))
    (hd : d ∈ HeckeIdealMobius.divisors F (sourceQuadraticBlockModulus F S₀ g)) :
    Summable (fun J : J₀ => ‖(Ψ e).allCoefficient J.val *
      quadraticHeckeDualProfile A r sourceQuadraticBlockProfile
        ((Ideal.absNorm J.val : ℝ) * (M / (Ideal.absNorm d : ℝ)) /
          (Ideal.absNorm (sourceQuadraticConductor F S₀ hζ e) : ℝ))‖) := by
  simpa only [← sourceQuadraticBlockDualTerm_eq F S₀ hζ] using
    quadraticHeckeRayDualTerm_norm_summable F (Ψ e) A r sourceQuadraticBlockProfile
      sourceQuadraticBlockProfile_compact sourceQuadraticBlockProfile_positive
      sourceQuadraticBlockProfile_smooth (sourceQuadraticBlockDualScale_pos F S₀ hζ hM g e d hd)

def sourceQuadraticBlockNonzeroPoissonCutoff (M : ℝ) (g e : E)
    (H : Ideal (𝓞 F) → ℝ) : ℂ :=
  ∑ d ∈ HeckeIdealMobius.divisors F (sourceQuadraticBlockModulus F S₀ g),
    sourceQuadraticBlockDualPrefactor F S₀ hζ M e d *
      ∑ J ∈ quadraticHeckeIdealNormBall F (H d),
        quadraticHeckeRayDualTerm F (Ψ e) A r sourceQuadraticBlockProfile
          (sourceQuadraticBlockDualScale F S₀ hζ M e d) J

theorem sourceQuadraticBlockNonzeroPoissonSum_eq_dual (M : ℝ) (g e : E) :
    sourceQuadraticBlockNonzeroPoissonSum F S₀ hζ M g e =
      ∑ d ∈ HeckeIdealMobius.divisors F (sourceQuadraticBlockModulus F S₀ g),
        sourceQuadraticBlockDualPrefactor F S₀ hζ M e d *
          ∑' J : J₀, quadraticHeckeRayDualTerm F (Ψ e) A r sourceQuadraticBlockProfile
            (sourceQuadraticBlockDualScale F S₀ hζ M e d) J := by
  simp only [sourceQuadraticBlockNonzeroPoissonSum, sourceQuadraticBlockDualPrefactor,
    sourceQuadraticBlockDualTerm_eq F S₀ hζ]

theorem sourceQuadraticBlockNonzeroPoissonCutoff_difference {M : ℝ} (hM : 0 < M)
    (g e : E) (H : Ideal (𝓞 F) → ℝ)
    (hH : ∀ d ∈ HeckeIdealMobius.divisors F (sourceQuadraticBlockModulus F S₀ g), 0 ≤ H d) :
    sourceQuadraticBlockNonzeroPoissonSum F S₀ hζ M g e -
        sourceQuadraticBlockNonzeroPoissonCutoff F S₀ hζ M g e H =
      ∑ d ∈ HeckeIdealMobius.divisors F (sourceQuadraticBlockModulus F S₀ g),
        sourceQuadraticBlockDualPrefactor F S₀ hζ M e d *
          ∑' J : {J : J₀ // H d < (Ideal.absNorm J.val : ℝ)},
            quadraticHeckeRayDualTerm F (Ψ e) A r sourceQuadraticBlockProfile
              (sourceQuadraticBlockDualScale F S₀ hζ M e d) J.val := by
  rw [sourceQuadraticBlockNonzeroPoissonSum_eq_dual, sourceQuadraticBlockNonzeroPoissonCutoff,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← mul_sub, quadraticHeckeRayDualTerm_cutoff_difference F (Ψ e) A r
    sourceQuadraticBlockProfile sourceQuadraticBlockProfile_compact
    sourceQuadraticBlockProfile_positive sourceQuadraticBlockProfile_smooth
    (sourceQuadraticBlockDualScale_pos F S₀ hζ hM g e d hd) (hH d hd)]

theorem sourceQuadraticBlockNonzeroPoissonCutoff_tendsto {M : ℝ} (hM : 0 < M) (g e : E) :
    Tendsto (fun H : ℝ => sourceQuadraticBlockNonzeroPoissonCutoff F S₀ hζ M g e (fun _ => H))
      atTop (𝓝 (sourceQuadraticBlockNonzeroPoissonSum F S₀ hζ M g e)) := by
  rw [sourceQuadraticBlockNonzeroPoissonSum_eq_dual]
  apply tendsto_finsetSum
  intro d hd
  exact (quadraticHeckeRayDual_cutoff_tendsto F (Ψ e) A r sourceQuadraticBlockProfile
    sourceQuadraticBlockProfile_compact sourceQuadraticBlockProfile_positive
    sourceQuadraticBlockProfile_smooth
    (sourceQuadraticBlockDualScale_pos F S₀ hζ hM g e d hd)).const_mul _

end
end ArtinMatthews.SourceEulerAssembly

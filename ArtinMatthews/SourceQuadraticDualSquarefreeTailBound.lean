module

public import ArtinMatthews.SourceQuadraticDualSquarefreeSplit
public import ArtinMatthews.QuadraticHeckeRayDualTail
public import ArtinMatthews.QuadraticHeckeRaySquarefreeTail
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
open NumberField Set VaryingKummerAnalytic
open scoped NumberField Classical ContDiff
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "NZ" => {J : Ideal (𝓞 F) // J ≠ ⊥}
local notation "Q" e => (Ideal.absNorm (sourceQuadraticConductor F S₀ hζ e) : ℝ)

theorem sourceQuadraticDualSummand_eq_rayDualTerm (e : E) (X : ℝ) (J : NZ) :
    sourceQuadraticDualSummand F S₀ hζ e X J =
      quadraticHeckeRayDualTerm F (sourceQuadraticRayCharacter F S₀ hζ e)
        (quadraticHeckeFieldScale F) (InfinitePlace.nrComplexPlaces F)
        sourceQuadraticBlockProfile (X / Q e) J := by
  unfold sourceQuadraticDualSummand quadraticHeckeRayDualTerm
  congr 1
  congr 1
  ring

/-- The actual source dual tail keeps its conductor scale and squarefree cutoff. -/
theorem sourceQuadraticDualSquarefreeTail_bound {u σ : ℝ}
    (hu : 1 < u) (huσ : u ≤ σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (e : E) (X U : ℝ), 0 < X → 0 < U →
      ‖sourceQuadraticDualSquarefreeTail F S₀ hζ e X U‖ ≤
        C * (X / Q e) ^ (-σ) * U ^ (u - σ) := by
  obtain ⟨C, hC, hbound⟩ := quadraticHeckeRayDualTerm_squarefree_tail_bound F
    (quadraticHeckeFieldScale F) (InfinitePlace.nrComplexPlaces F)
    sourceQuadraticBlockProfile sourceQuadraticBlockProfile_compact
    sourceQuadraticBlockProfile_positive sourceQuadraticBlockProfile_smooth hu huσ
  refine ⟨C, hC, ?_⟩
  intro e X U hX hU
  have hscale := div_pos hX (sourceQuadraticDual_conductorNorm_pos F S₀ hζ e)
  have h := hbound (X / Q e) U hscale hU (sourceQuadraticRayCharacter F S₀ hζ e)
  simpa only [sourceQuadraticDualSquarefreeTail,
    sourceQuadraticDualSummand_eq_rayDualTerm F S₀ hζ] using h

/-- Removing a finite squarefree-part cutoff has the same quantitative error. -/
theorem sourceQuadraticDualTruncated_error_bound {u σ : ℝ}
    (hu : 1 < u) (huσ : u ≤ σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (e : E) (X U : ℝ), 0 < X → 0 < U →
      ‖(∑' J : NZ, sourceQuadraticDualSummand F S₀ hζ e X J) -
        sourceQuadraticDualTruncated F S₀ hζ e X U‖ ≤
          C * (X / Q e) ^ (-σ) * U ^ (u - σ) := by
  obtain ⟨C, hC, hbound⟩ := sourceQuadraticDualSquarefreeTail_bound F S₀ hζ hu huσ
  refine ⟨C, hC, ?_⟩
  intro e X U hX hU
  rw [sourceQuadraticDual_full_eq_truncated_add_tail F S₀ hζ e hX U,
    add_sub_cancel_left]
  exact hbound e X U hX hU

end
end ArtinMatthews.SourceEulerAssembly

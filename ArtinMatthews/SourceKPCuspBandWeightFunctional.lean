module

public import ArtinMatthews.SourceKPAutomorphicCuspBandFunctional
public import ArtinMatthews.SourceKPArithmeticDiscreteness
public import ArtinMatthews.SourceKPAutomorphicCompactMeasure
public import ArtinMatthews.SourceKPAutomorphicCompactTopology
public import ArtinMatthews.SourceKPAutomorphicMeasureRegularity
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
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

/-! A bounded Borel weight on a finite height band tests the actual genuine L² space. -/

namespace ArtinMatthews
open NumberField MeasureTheory
open scoped NumberField MatrixGroups AdeleRing InnerProductSpace
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)

theorem sourceKPAutomorphicBandWeight_memLp (W : Y → ℂ) (hW : Measurable W) {B C : ℝ}
    (hbound : ∀ y, ‖W y‖ ≤ C)
    (hsupport : Function.support W ⊆ {y | sourceKPAutomorphicCompactOrbitHeight K hζ y ≤ B}) :
    MemLp W 2 μY := by
  have hc := HasCompactSupport.of_support_subset_isCompact
    (sourceKPAutomorphicCompactOrbitHeight_sublevel_isCompact K hζ B) hsupport
  exact hc.memLp_of_bound hW.aestronglyMeasurable C (ae_of_all _ hbound)

/-- Pairing an ambient test with a genuine vector gives a bounded complex-linear functional. -/
def sourceKPGenuineAutomorphicL2Pairing (W : Y → ℂ) (hW : MemLp W 2 μY) :
    SourceKPGenuineAutomorphicL2 K hζ →L[ℂ] ℂ :=
  (innerSL ℂ (hW.toLp W)).comp
    (sourceKPCompactGenuineL2Subspace K hζ (sourceKPArchHaar K hζ)).subtypeL

theorem sourceKPGenuineAutomorphicL2Pairing_norm_le (W : Y → ℂ) (hW : MemLp W 2 μY) :
    ‖sourceKPGenuineAutomorphicL2Pairing K hζ W hW‖ ≤ ‖hW.toLp W‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  change ‖inner ℂ (hW.toLp W) u.val‖ ≤ ‖hW.toLp W‖ * ‖u.val‖
  exact norm_inner_le_norm _ _

private theorem cuspBandWeight_integrand_ae {W F : Y → ℂ} (hW : MemLp W 2 μY)
    (u : SourceKPGenuineAutomorphicL2 K hζ) (hF : (u.val : Y → ℂ) =ᵐ[μY] F) :
    (fun y => inner ℂ ((hW.toLp W) y) (u.val y)) =ᵐ[μY] fun y => star (W y) * F y := by
  filter_upwards [hW.coeFn_toLp, hF] with y hw hf
  rw [hw, hf, RCLike.inner_apply, Complex.star_def, mul_comm]

theorem sourceKPGenuineAutomorphicL2Pairing_integrable {W F : Y → ℂ} (hW : MemLp W 2 μY)
    (u : SourceKPGenuineAutomorphicL2 K hζ) (hF : (u.val : Y → ℂ) =ᵐ[μY] F) :
    Integrable (fun y => star (W y) * F y) μY :=
  (L2.integrable_inner (𝕜 := ℂ) (hW.toLp W) u.val).congr (cuspBandWeight_integrand_ae K hζ hW u hF)

theorem sourceKPGenuineAutomorphicL2Pairing_apply {W F : Y → ℂ} (hW : MemLp W 2 μY)
    (u : SourceKPGenuineAutomorphicL2 K hζ) (hF : (u.val : Y → ℂ) =ᵐ[μY] F) :
    sourceKPGenuineAutomorphicL2Pairing K hζ W hW u = ∫ y : Y, star (W y) * F y ∂μY := by
  change inner ℂ (hW.toLp W) u.val = _
  rw [L2.inner_def]
  exact integral_congr_ae (cuspBandWeight_integrand_ae K hζ hW u hF)

theorem sourceKPAutomorphicCuspBandFunctional_eq_pairing {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B) (s : ℂ) :
    sourceKPAutomorphicCuspBandFunctional K hζ hA hAB s =
      sourceKPGenuineAutomorphicL2Pairing K hζ (sourceKPAutomorphicCuspBandTest K hζ A B s)
        (sourceKPAutomorphicCuspBandTest_memLp K hζ hA hAB s) := by
  ext u
  rfl

end
end ArtinMatthews

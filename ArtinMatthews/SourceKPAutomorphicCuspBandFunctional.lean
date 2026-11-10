module

public import ArtinMatthews.SourceKPAutomorphicCuspBandTest
public import ArtinMatthews.SourceKPCompactGenuineL2
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

/-! The full-band pairing is a bounded linear functional on the actual genuine L² space. -/

namespace ArtinMatthews
open NumberField MeasureTheory
open scoped NumberField MatrixGroups AdeleRing InnerProductSpace
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)

def sourceKPAutomorphicCuspBandTestL2 {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B) (s : ℂ) :
    SourceKPGenuineAutomorphicL2 K hζ := by
  let test := sourceKPAutomorphicCuspBandTest K hζ A B s
  let hm := sourceKPAutomorphicCuspBandTest_memLp K hζ hA hAB s
  refine ⟨hm.toLp test, ?_⟩
  apply (sourceKPCompactGenuineL2Subspace_mem_ae K hζ (sourceKPArchHaar K hζ) _).mpr
  intro z
  have hAE := hm.coeFn_toLp
  have hZ := (sourceKPAutomorphicCompactMeasure_center_preserving K hζ z
    (sourceKPArchHaar K hζ)).quasiMeasurePreserving.ae_eq_comp hAE
  filter_upwards [hAE, hZ] with x hx hzx
  calc
    (hm.toLp test) (z • x) = test (z • x) := hzx
    _ = (sourceKPAdelicCentralComplex K hζ z : ℂ) * test x :=
      sourceKPAutomorphicCuspBandTest_center K hζ A B s z x
    _ = _ := congrArg (fun w => (sourceKPAdelicCentralComplex K hζ z : ℂ) * w) hx.symm

theorem sourceKPAutomorphicCuspBandTestL2_ae {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B) (s : ℂ) :
    ((sourceKPAutomorphicCuspBandTestL2 K hζ hA hAB s).val : Y → ℂ) =ᵐ[μY]
      sourceKPAutomorphicCuspBandTest K hζ A B s :=
  (sourceKPAutomorphicCuspBandTest_memLp K hζ hA hAB s).coeFn_toLp

def sourceKPAutomorphicCuspBandFunctional {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B) (s : ℂ) :
    SourceKPGenuineAutomorphicL2 K hζ →L[ℂ] ℂ :=
  innerSL ℂ (sourceKPAutomorphicCuspBandTestL2 K hζ hA hAB s)

theorem sourceKPAutomorphicCuspBandFunctional_norm {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B) (s : ℂ) :
    ‖sourceKPAutomorphicCuspBandFunctional K hζ hA hAB s‖ =
      ‖sourceKPAutomorphicCuspBandTestL2 K hζ hA hAB s‖ :=
  innerSL_apply_norm ℂ _

theorem sourceKPAutomorphicCuspBandFunctional_norm_apply_le {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B)
    (s : ℂ) (u : SourceKPGenuineAutomorphicL2 K hζ) :
    ‖sourceKPAutomorphicCuspBandFunctional K hζ hA hAB s u‖ ≤
      ‖sourceKPAutomorphicCuspBandTestL2 K hζ hA hAB s‖ * ‖u‖ := by
  rw [sourceKPAutomorphicCuspBandFunctional, innerSL_apply_apply]
  exact norm_inner_le_norm _ _

private theorem cuspBandFunctional_integrand_ae {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B)
    (s : ℂ) (u : SourceKPGenuineAutomorphicL2 K hζ) {F : Y → ℂ} (hF : (u.val : Y → ℂ) =ᵐ[μY] F) :
    (fun x => inner ℂ ((sourceKPAutomorphicCuspBandTestL2 K hζ hA hAB s).val x) (u.val x)) =ᵐ[μY]
      fun x => star (sourceKPAutomorphicCuspBandTest K hζ A B s x) * F x := by
  filter_upwards [sourceKPAutomorphicCuspBandTestL2_ae K hζ hA hAB s, hF] with x ht hu
  rw [ht, hu, RCLike.inner_apply, Complex.star_def, mul_comm]

theorem sourceKPAutomorphicCuspBandFunctional_integrable {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B)
    (s : ℂ) (u : SourceKPGenuineAutomorphicL2 K hζ) {F : Y → ℂ} (hF : (u.val : Y → ℂ) =ᵐ[μY] F) :
    Integrable (fun x => star (sourceKPAutomorphicCuspBandTest K hζ A B s x) * F x) μY :=
  (L2.integrable_inner (𝕜 := ℂ) (sourceKPAutomorphicCuspBandTestL2 K hζ hA hAB s).val u.val).congr
    (cuspBandFunctional_integrand_ae K hζ hA hAB s u hF)

theorem sourceKPAutomorphicCuspBandFunctional_apply {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B)
    (s : ℂ) (u : SourceKPGenuineAutomorphicL2 K hζ) {F : Y → ℂ} (hF : (u.val : Y → ℂ) =ᵐ[μY] F) :
    sourceKPAutomorphicCuspBandFunctional K hζ hA hAB s u =
      ∫ x : Y, star (sourceKPAutomorphicCuspBandTest K hζ A B s x) * F x ∂μY := by
  change inner ℂ (sourceKPAutomorphicCuspBandTestL2 K hζ hA hAB s).val u.val = _
  rw [L2.inner_def]
  exact integral_congr_ae (cuspBandFunctional_integrand_ae K hζ hA hAB s u hF)

theorem sourceKPAutomorphicCuspBandFunctional_apply_band {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B)
    (s : ℂ) (u : SourceKPGenuineAutomorphicL2 K hζ) {F : Y → ℂ} (hF : (u.val : Y → ℂ) =ᵐ[μY] F) :
    sourceKPAutomorphicCuspBandFunctional K hζ hA hAB s u =
      ∫ x in {x : Y | A < sourceKPAutomorphicCompactOrbitHeight K hζ x ∧
        sourceKPAutomorphicCompactOrbitHeight K hζ x < 2*B},
        star (sourceKPAutomorphicCuspBandTest K hζ A B s x) * F x ∂μY := by
  rw [sourceKPAutomorphicCuspBandFunctional_apply K hζ hA hAB s u hF]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hz : sourceKPAutomorphicCuspBandTest K hζ A B s x = 0 := by
    by_contra hn
    exact hx (sourceKPAutomorphicCuspBandTest_support K hζ hA hAB s hn)
  rw [hz, star_zero, zero_mul]

end
end ArtinMatthews

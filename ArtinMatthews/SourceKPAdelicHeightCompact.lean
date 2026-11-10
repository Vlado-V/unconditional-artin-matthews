module

public import ArtinMatthews.SourceKPAdelicTranslatedHeight
public import ArtinMatthews.SourceKPFiniteMatrixTopology
public import ArtinMatthews.SourceKPHeightLocalContinuity
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Uniform bounds for the actual translated-height constant on compact matrix sets. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain Topology Matrix Filter SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K]
local notation "Pr" => HeightOneSpectrum (𝓞 K)

lemma sourceKPAdelicMatrices_locally_integral (g : GL (Fin 2) 𝔸[K]) :
    ∃ S : Finset Pr, ∀ᶠ h : GL (Fin 2) 𝔸[K] in nhds g,
      ∀ P : Pr, P ∉ S → SourceKPIntegralMatrix (sourceKPFiniteVal K P) (sourceKPAdelicBaseFiniteAt K P h) := by
  classical
  have hfin : {P : Pr | ¬SourceKPIntegralMatrix (sourceKPFiniteVal K P) (sourceKPAdelicBaseFiniteAt K P g)}.Finite :=
    Filter.eventually_cofinite.mp (sourceKPAdeleMatrixAt_eventually_integral K (sourceKPGL2ProductEquiv K g).2)
  let S : Finset Pr := hfin.toFinset
  have hg (P : Pr) (hP : P ∉ S) :
      SourceKPIntegralMatrix (sourceKPFiniteVal K P) (sourceKPAdelicBaseFiniteAt K P g) := by
    by_contra hp
    exact hP (hfin.mem_toFinset.mpr hp)
  let f : GL (Fin 2) 𝔸[K] → GL (Fin 2) 𝔸ᶠ[K] :=
    fun h => (sourceKPGL2ProductEquiv K (g⁻¹ * h)).2
  have hf : Continuous f :=
    (sourceKPAdelicFiniteMatrix_continuous K).comp (continuous_const.mul continuous_id)
  have hfg : f g ∈ sourceKPFiniteIntegralMatrixGroup K := by
    simp [f]
  have hU := ((sourceKPFiniteIntegralMatrixGroup_isOpen K).preimage hf).mem_nhds hfg
  refine ⟨S, ?_⟩
  filter_upwards [hU] with h hh
  intro P hP
  have hhP := (sourceKPFiniteIntegralMatrixGroup_mem K (f h)).mp hh P
  have he : h = g * (g⁻¹ * h) := by simp
  rw [he, map_mul]
  exact sourceKPIntegralMatrix_mul _ (hg P hP) hhP

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

lemma sourceKPAdelicHeightConstant_continuous : Continuous (sourceKPAdelicHeightConstant K hζ) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro g
  obtain ⟨S, hS⟩ := sourceKPAdelicMatrices_locally_integral K g
  have harch : Continuous (fun h : GL (Fin 2) 𝔸[K] =>
      ∏ v : InfinitePlace K, sourceArchMatrixHeightConstant (sourceKPAdelicBaseComplexAt K hζ v h) ^ v.mult) :=
    continuous_finsetProd Finset.univ (fun v _ =>
      (sourceArchMatrixHeightConstant_continuous.comp (sourceKPAdelicBaseComplexAt_continuous K hζ v)).pow v.mult)
  have hfinite : Continuous (fun h : GL (Fin 2) 𝔸[K] =>
      ∏ P ∈ S, sourceKPFiniteMatrixHeightConstant K P (sourceKPAdelicBaseFiniteAt K P h)) :=
    continuous_finsetProd S (fun P _ =>
      (sourceKPFiniteMatrixHeightConstant_continuous K P).comp (sourceKPAdelicBaseFiniteAt_continuous K P))
  apply (harch.mul hfinite).continuousAt.congr_of_eventuallyEq
  filter_upwards [hS] with h hh
  unfold sourceKPAdelicHeightConstant
  congr 1
  apply finprod_eq_prod_of_mulSupport_subset
  intro P hP
  by_contra hPS
  change sourceKPFiniteMatrixHeightConstant K P (sourceKPAdelicBaseFiniteAt K P h) ≠ 1 at hP
  exact hP (sourceKPFiniteMatrixHeightConstant_integral K P _ (hh P hPS))

lemma sourceKPAdelicHeightConstant_bounded
    (C : Set (GL (Fin 2) 𝔸[K])) (hC : IsCompact C) :
    ∃ B : ℝ, 0 < B ∧ ∀ g ∈ C, sourceKPAdelicHeightConstant K hζ g ≤ B := by
  obtain ⟨B, hB⟩ := hC.bddAbove_image (sourceKPAdelicHeightConstant_continuous K hζ).continuousOn
  refine ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro g hg
  exact (hB ⟨g, hg, rfl⟩).trans (le_max_right _ _)

lemma sourceKPAdelicHeight_translate_uniform_on_compact
    (C : Set (GL (Fin 2) 𝔸[K])) (hC : IsCompact C) :
    ∃ B : ℝ, 0 < B ∧ ∀ g ∈ C, ∀ x : K,
      sourceKPAdelicHeight K hζ (sourceKPAdelicOpenCellMatrix K x * g) ≤
        B * (Height.mulHeight₁ x)⁻¹ ^ 2 := by
  obtain ⟨B, hB, hbound⟩ := sourceKPAdelicHeightConstant_bounded K hζ C hC
  refine ⟨B, hB, ?_⟩
  intro g hg x
  exact (sourceKPAdelicHeight_translate K hζ g x).trans
    (mul_le_mul_of_nonneg_right (hbound g hg) (sq_nonneg _))

end
end ArtinMatthews

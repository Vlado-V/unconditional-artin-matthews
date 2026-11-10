module

public import ArtinMatthews.SourceKPCuspProductMeasure
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

/-! The native height product is supported on positive heights and is
exhausted by compact positive boxes. -/
namespace ArtinMatthews
open NumberField MeasureTheory Set
open scoped ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K]
local notation "V" => InfinitePlace K
local notation "ν" => sourceKPCuspProductHeightMeasure K

theorem sourceKPCuspProductHeight_ae_positive :
    ∀ᵐ y ∂ν, ∀ v : V, 0 < y v := by
  have h : ∀ᵐ z ∂sourceKPCuspHeightMeasure, z ∈ Ioi (0 : ℝ) :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)
  refine ae_all_iff.mpr fun v => ?_
  exact (Measure.tendsto_eval_ae_ae (μ := fun _ : V => sourceKPCuspHeightMeasure)
    (i := v)).eventually h

theorem sourceKPCuspProductHeight_ae_of_compact (P : (V → ℝ) → Prop)
    (h : ∀ B : Set (V → ℝ), IsCompact B → (∀ y ∈ B, ∀ v, 0 < y v) →
      ∀ᵐ y ∂(ν).restrict B, P y) :
    ∀ᵐ y ∂ν, P y := by
  let B (n : ℕ) : Set (V → ℝ) :=
    Set.univ.pi fun _ => Icc (((n : ℝ) + 1)⁻¹) ((n : ℝ) + 1)
  have hB (n : ℕ) : IsCompact (B n) := isCompact_univ_pi fun _ => isCompact_Icc
  have hp (n : ℕ) (y : V → ℝ) (hy : y ∈ B n) (v : V) : 0 < y v :=
    (by positivity : (0 : ℝ) < ((n : ℝ) + 1)⁻¹).trans_le (hy v (mem_univ v)).1
  have hcover : (⋃ n, B n) = {y | ∀ v, 0 < y v} := by
    ext y
    constructor
    · intro hy
      obtain ⟨n, hn⟩ := mem_iUnion.mp hy
      exact hp n y hn
    · intro hy
      obtain ⟨M, hM⟩ := (Set.finite_range fun v : V => max (y v) (y v)⁻¹).bddAbove
      obtain ⟨n, hn⟩ := exists_nat_gt M
      refine mem_iUnion.mpr ⟨n, ?_⟩
      intro v _
      have hmax : max (y v) (y v)⁻¹ ≤ (n : ℝ) + 1 :=
        (hM (Set.mem_range_self v)).trans (by linarith)
      exact ⟨(inv_le_comm₀ (by positivity) (hy v)).mpr ((le_max_right _ _).trans hmax),
        (le_max_left _ _).trans hmax⟩
  have hlocal := (ae_restrict_iUnion_iff B P).mpr fun n => h (B n) (hB n) (hp n)
  have hfull : ∀ᵐ y ∂ν, y ∈ ⋃ n, B n := by
    rw [hcover]
    exact sourceKPCuspProductHeight_ae_positive K
  rwa [Measure.restrict_eq_self_of_ae_mem hfull] at hlocal

end
end ArtinMatthews

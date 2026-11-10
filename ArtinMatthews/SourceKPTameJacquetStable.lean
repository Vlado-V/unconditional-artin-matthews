module

public import ArtinMatthews.SourceKPTameJacquetTruncation
public import ArtinMatthews.SourceJacquetShellVectorValues
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The literal spherical Jacquet integral stabilizes on every original
x-ball of radius at least Q. It equals the computed vector, with a
normalized coordinate-zero value and the three valuation cases. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical AllowedGenerators QuadraticWeil Filter
open scoped NumberField SourcePhysical Topology BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "Q₀" => (Ideal.absNorm P.val.asIdeal : ℝ)

theorem sourceKPTameJacquetTruncation_stable
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (e N : ℕ) (hN : 1 ≤ N) :
    sourceKPTameJacquetTruncation K hζ S₀ P e N = sourceJacquetShellVector K hζ S₀ P e := by
  have hP : P.val ∉ traceBadPlaces K := fun h => P.property (hS (Finset.mem_union_left _ h))
  rw [(sourceKPTameJacquetTruncation_formula K hζ S₀ P hP e N).2, sourceJacquetShellVector]
  let f := fun l : ℕ =>
    (sourceJacquetScale Q₀ ((l : ℝ) / 3) * sourceJacquetActualShell K hζ S₀ P e l) •
      sourceJacquetBasis (-(e : ZMod 3) + 2 * (l : ZMod 3))
  change sourceJacquetScale Q₀ (-2 * (e : ℝ) / 3) • (sourceJacquetBasis (-(e : ZMod 3)) +
    ∑ l ∈ Finset.Icc 1 (N + e), f l) = sourceJacquetScale Q₀ (-2 * (e : ℝ) / 3) •
    (sourceJacquetBasis (-(e : ZMod 3)) + ∑ l ∈ Finset.Icc 1 (e + 1), f l)
  have hs : Finset.Icc 1 (e + 1) ⊆ Finset.Icc 1 (N + e) := by
    intro l hl
    simp only [Finset.mem_Icc] at hl ⊢
    exact ⟨hl.1, by omega⟩
  have hz : ∀ l ∈ Finset.Icc 1 (N + e), l ∉ Finset.Icc 1 (e + 1) → f l = 0 := by
    intro l hl he
    simp only [Finset.mem_Icc] at hl he
    have hle : ¬l ≤ e := by omega
    have hlast : l ≠ e + 1 := by omega
    dsimp only [f]
    rw [sourceJacquetActualShell_table K hζ S₀ P hS, ite_eq_right hle, ite_eq_right hlast, mul_zero, zero_smul]
  rw [← Finset.sum_subset hs hz]

def sourceKPTameJacquetStable (e : ℕ) : ZMod 3 → ℂ :=
  sourceKPTameJacquetTruncation K hζ S₀ P e 1

theorem sourceKPTameJacquetStable_eq_shellVector
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (e : ℕ) :
    sourceKPTameJacquetStable K hζ S₀ P e = sourceJacquetShellVector K hζ S₀ P e :=
  sourceKPTameJacquetTruncation_stable K hζ S₀ P hS e 1 le_rfl

theorem sourceKPTameJacquetTruncation_tendsto
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (e : ℕ) :
    Tendsto (sourceKPTameJacquetTruncation K hζ S₀ P e) atTop (𝓝 (sourceKPTameJacquetStable K hζ S₀ P e)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  exact (sourceKPTameJacquetStable_eq_shellVector K hζ S₀ P hS e).trans
    (sourceKPTameJacquetTruncation_stable K hζ S₀ P hS e N hN).symm

theorem sourceKPTameJacquetStable_zero_at_zero
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) :
    sourceKPTameJacquetStable K hζ S₀ P 0 0 = 1 := by
  rw [sourceKPTameJacquetStable_eq_shellVector K hζ S₀ P hS, sourceJacquetShellVector_zero_at_zero K hζ S₀ P hS]

private theorem sourceKPTameJacquetShellVector_zero_formula
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) :
    sourceJacquetShellVector K hζ S₀ P 0 = sourceJacquetBasis 0 +
      (sourceJacquetScale Q₀ (-1 / 6) * sourceJacquetActualGauss K hζ S₀ P 4) • sourceJacquetBasis 2 := by
  have hz : sourceJacquetScale Q₀ 0 = 1 := by simp [sourceJacquetScale]
  simpa only [mul_zero, Nat.cast_zero, neg_zero, hz, one_smul] using
    sourceJacquetShellVector_three K hζ S₀ P hS 0

theorem sourceKPTameJacquetStable_three
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (k : ℕ) :
    sourceKPTameJacquetStable K hζ S₀ P (3 * k) =
      sourceJacquetScale Q₀ (-(k : ℝ)) • sourceKPTameJacquetStable K hζ S₀ P 0 := by
  rw [sourceKPTameJacquetStable_eq_shellVector K hζ S₀ P hS (3 * k),
    sourceKPTameJacquetStable_eq_shellVector K hζ S₀ P hS 0, sourceJacquetShellVector_three K hζ S₀ P hS,
    sourceKPTameJacquetShellVector_zero_formula K hζ S₀ P hS]

theorem sourceKPTameJacquetStable_three_add_one
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (k : ℕ) :
    sourceKPTameJacquetStable K hζ S₀ P (3 * k + 1) =
      (sourceJacquetScale Q₀ (-(k : ℝ) - 1 / 2) * sourceJacquetActualGauss K hζ S₀ P 2) •
        sourceKPTameJacquetStable K hζ S₀ P 0 := by
  rw [sourceKPTameJacquetStable_eq_shellVector K hζ S₀ P hS (3 * k + 1),
    sourceKPTameJacquetStable_eq_shellVector K hζ S₀ P hS 0, sourceJacquetShellVector_three_add_one K hζ S₀ P hS,
    sourceKPTameJacquetShellVector_zero_formula K hζ S₀ P hS]

theorem sourceKPTameJacquetStable_three_add_two
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (k : ℕ) :
    sourceKPTameJacquetStable K hζ S₀ P (3 * k + 2) = 0 := by
  rw [sourceKPTameJacquetStable_eq_shellVector K hζ S₀ P hS, sourceJacquetShellVector_three_add_two K hζ S₀ P hS]

end
end ArtinMatthews

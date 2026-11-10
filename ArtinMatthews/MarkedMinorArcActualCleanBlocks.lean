module

public import ArtinMatthews.MarkedMinorArcActualCleanBlock
public import ArtinMatthews.MarkedMinorArcBlockOperator
public import ArtinMatthews.MarkedMinorArcSymmetrization
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

/-! Genuine actual clean blocks, direct sums of arbitrary size, and
independent left/right probability slot symmetrizations. -/
namespace ArtinMatthews
open Matrix MeasureTheory Filter
open scoped BigOperators Matrix.Norms.L2Operator

/-- Actual data of one fixed shared-list, line-tuple and position-cell block. -/
structure MarkedMinorCleanCellData where
  shared : ℕ
  positions : Finset (ℤ × ℤ)
  products : Finset ℤ
  root : ℤ × ℤ
  complement : ℤ × ℤ
  deriving DecidableEq

abbrev MarkedMinorCleanCellIndex (d : MarkedMinorCleanCellData) := d.positions × d.products

/-- Only the literal source geometric and first-good-state conditions enter
this predicate. It contains no norm, cancellation or distribution statement. -/
def MarkedMinorCleanCellGeometry (r Y c B R : ℝ) (d : MarkedMinorCleanCellData) : Prop :=
  0 < d.shared ∧ Squarefree d.shared ∧ markedMinorIntegerDet d.root d.complement=1 ∧
  MarkedMinorShearGood ((d.shared : ℝ)*markedMinorIntegerTau r d.complement/markedMinorIntegerTau r d.root) Y ∧
  c ≤ |markedMinorIntegerTau r d.root| ∧ |markedMinorIntegerTau r d.root| ≤ B ∧
  (∀ v ∈ d.positions, c ≤ |markedMinorIntegerTau r v| ∧ |markedMinorIntegerTau r v| ≤ B) ∧
  (∀ v ∈ d.positions, ∀ p ∈ d.shared.primeFactors, MarkedMinorSamePrimeLine p d.root v) ∧
  (∀ v ∈ d.positions, |(v.2 : ℝ)/markedMinorIntegerTau r v-
    (d.root.2 : ℝ)/markedMinorIntegerTau r d.root| ≤ R*d.shared*Y)

/-- The exact counting conjugate of one actual tilted-measure clean block. -/
noncomputable def markedMinorActualMemoryCell {J : Type*} [Fintype J]
    (e : J → ℝ) (q x : ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (Y Q : ℝ)
    (d : MarkedMinorCleanCellData) : Matrix (MarkedMinorCleanCellIndex d) (MarkedMinorCleanCellIndex d) ℂ :=
  markedWeightedCountingMatrix (fun i : d.positions × d.products => markedMinorIntegerProductMass e q x i.2.1)
    (markedMinorActualCleanRawMatrix ψ η d.shared Y Q d.positions d.products)

/-- Literal dependent direct sum of the actual clean cells. Its cardinality
and the dimensions of its summands can grow arbitrarily. -/
noncomputable def markedMinorActualMemoryBlocks {J : Type*} [Fintype J]
    (e : J → ℝ) (q x : ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (Y Q : ℝ)
    (I : Finset MarkedMinorCleanCellData) :
    Matrix (Σ d : I, MarkedMinorCleanCellIndex d.1) (Σ d : I, MarkedMinorCleanCellIndex d.1) ℂ :=
  Matrix.blockDiagonal' (fun d : I => markedMinorActualMemoryCell e q x ψ η Y Q d.1)

/-- Actual prime-product clean estimates survive every dependent direct sum,
with threshold uniform in the complete family of source cell data. -/
theorem marked_minor_actual_memory_clean_blocks_opNorm {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) (hinj : Function.Injective e)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (hη : Function.support η ⊆ Set.Icc 1 4)
    (hηnorm : ∀ t, ‖η t‖ ≤ 1) {G H c B R : ℝ}
    (hG : 0 < G) (hH : 1 ≤ H) (hc : 0 < c) (hB : 0 ≤ B) (hR : 0 ≤ R) :
    ∀ᶠ x : ℝ in atTop, ∀ (q Y r : ℝ) (I : Finset MarkedMinorCleanCellData),
      0 ≤ q → q ≤ 1 → Real.exp ((Real.log x)^(1/10 : ℝ)) ≤ Y →
      Y ≤ Real.exp (H*(Real.log x)^(1/5 : ℝ)) →
      (∀ d ∈ I, MarkedMinorCleanCellGeometry r Y c B R d) →
      ‖markedMinorActualMemoryBlocks e q x ψ η Y ((Real.log x)^(G+4)) I‖ ≤ (Real.log x)^(-G) := by
  classical
  filter_upwards [marked_minor_actual_memory_clean_opNorm e he hinj ψ η hη hηnorm hG hH hc hB hR,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx hlog
  intro q Y r I hq0 hq1 hYlo hYhi hgeo
  apply markedMinorBlockDiagonal_norm_le _ (Real.rpow_nonneg (by linarith : (0:ℝ)≤Real.log x) _)
  intro d
  obtain ⟨hD,hDsq,hd,hg,hzlo,hzhi,hτ,hlines,hcell⟩ := hgeo d.1 d.2
  exact hx q Y r d.1.shared d.1.positions d.1.products d.1.root d.1.complement
    hq0 hq1 hYlo hYhi hD hDsq hd hg hzlo hzhi hτ hlines hcell

/-- Independent incoming and outgoing finite slot averages preserve the
actual clean-block bound, with no loss in group sizes or permutation counts. -/
theorem marked_minor_actual_memory_clean_symmetrized_opNorm {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) (hinj : Function.Injective e)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (hη : Function.support η ⊆ Set.Icc 1 4)
    (hηnorm : ∀ t, ‖η t‖ ≤ 1) {G H c B R : ℝ}
    (hG : 0 < G) (hH : 1 ≤ H) (hc : 0 < c) (hB : 0 ≤ B) (hR : 0 ≤ R) :
    ∀ᶠ x : ℝ in atTop, ∀ (q Y r : ℝ) (I : Finset MarkedMinorCleanCellData),
      0 ≤ q → q ≤ 1 → Real.exp ((Real.log x)^(1/10 : ℝ)) ≤ Y →
      Y ≤ Real.exp (H*(Real.log x)^(1/5 : ℝ)) →
      (∀ d ∈ I, MarkedMinorCleanCellGeometry r Y c B R d) →
      ∀ (W : Finset (Equiv.Perm (Σ d : I, MarkedMinorCleanCellIndex d.1) ×
        Equiv.Perm (Σ d : I, MarkedMinorCleanCellIndex d.1))) (weight : W → ℝ),
        (∀ j, 0 ≤ weight j) → (∑ j, weight j)=1 →
        ‖∑ j : W, (weight j) •
          (markedMinorActualMemoryBlocks e q x ψ η Y ((Real.log x)^(G+4)) I).submatrix
            j.1.1 j.1.2‖ ≤ (Real.log x)^(-G) := by
  classical
  filter_upwards [marked_minor_actual_memory_clean_blocks_opNorm e he hinj ψ η hη hηnorm hG hH hc hB hR]
    with x hx
  intro q Y r I hq0 hq1 hYlo hYhi hgeo W weight hw hmass
  exact (markedMinorMatrix_average_slotPairs_norm_le _ (fun j : W => j.1.1)
    (fun j : W => j.1.2) weight hw hmass).trans (hx q Y r I hq0 hq1 hYlo hYhi hgeo)

end ArtinMatthews

module

public import ArtinMatthews.MarkedRootGoodPathCells
public import ArtinMatthews.MarkedRootIndicatorPartition
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
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

/-! A genuine root-versus-volume comparison for the full actual finite
path box/first/beta indicator. No replacement or boundary estimate is assumed. -/

noncomputable section
namespace ArtinMatthews
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedRootGoodPathSet {J ι : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) {M : ℕ} (I : Finset ι)
    (a : ι → MarkedRawActive (markedRawActualPrimeBand e x) M) (d₀ Y U V : ℝ)
    (z w : ι → Fin 2 → ℝ) : Set (ℝ × (ℝ × ℝ)) :=
  markedRootBoxDomain ∩ {p | MarkedRootPhysicalGoodPath e x I a d₀ Y U V z w p}

theorem markedRoot_zeta_two_pos : 0 < (riemannZeta 2).re := by
  have hz : (riemannZeta 2).re = Real.pi^2/6 := by
    rw [riemannZeta_two,← Complex.ofReal_pow]
    norm_num [pow_two,Complex.mul_re]
  rw [hz]
  positivity

theorem markedRootGoodPathSet_measurable {J ι : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) {M : ℕ} (I : Finset ι)
    (a : ι → MarkedRawActive (markedRawActualPrimeBand e x) M) (d₀ Y U V : ℝ)
    (z w : ι → Fin 2 → ℝ) : MeasurableSet (markedRootGoodPathSet e x I a d₀ Y U V z w) := by
  have hd : MeasurableSet markedRootBoxDomain := measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)
  exact hd.inter (markedRootPhysicalGoodPath_measurable e x I a d₀ Y U V z w)

theorem markedRootGoodPath_indicator_replacement {J ι : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) {M : ℕ} (I : Finset ι)
    (a : ι → MarkedRawActive (markedRawActualPrimeBand e x) M) (d₀ Y U V H : ℝ)
    (z w : ι → Fin 2 → ℝ) {S : ℕ} (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (hU : 1 < U) (hV : 1 < V) (hH : 0 ≤ H)
    (hdet : ∀ k ∈ I,markedVectorDet (z k) (w k)=1)
    (hz : ∀ k ∈ I,∀ j,|z k j| ≤ H) (hw : ∀ k ∈ I,∀ j,|w k j| ≤ H)
    (hfirst : Y^(-7/10:ℝ) ≤ 1) (hbeta : ∀ j,100*Real.exp (-((Real.log x)^(e j))) ≤ 1)
    (N : ℕ) (hN : 0 < N) (hsmall : 20*H/(N:ℝ) ≤ 1/2) :
    |(markedRootIndicatorCount g₀ U V (markedRootGoodPathSet e x I a d₀ Y U V z w):ℝ)-
      (U*V/((riemannZeta 2).re*(Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)):ℝ)))*
        markedNormalizedRootMeasure.real (markedRootGoodPathSet e x I a d₀ Y U V z w)| ≤
      (∑ i : MarkedRootGridIndex N,markedRootPartitionCountError g₀ U V N i)+
      (U*V/((riemannZeta 2).re*(Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)):ℝ)))*
        (markedRootGoodPathBoundaryCost e x I a d₀ Y H z w/(N:ℝ)) := by
  have hUp : 0 < U := by linarith
  have hVp : 0 < V := by linarith
  have hUV : 1 ≤ U*V := by nlinarith
  have hd : 0 ≤ U*V/((riemannZeta 2).re*(Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)):ℝ)) :=
    div_nonneg (mul_nonneg hUp.le hVp.le) (mul_nonneg markedRoot_zeta_two_pos.le (Nat.cast_nonneg _))
  have hc (i : MarkedRootGridIndex N)
      (hi : i ∉ markedRootGoodPathBadIndices e x I a d₀ Y U V H z w N)
      (p : ℝ × (ℝ × ℝ)) (hp : p ∈ markedRootPartitionCell N i)
      (q : ℝ × (ℝ × ℝ)) (hq : q ∈ markedRootPartitionCell N i) :
      p ∈ markedRootGoodPathSet e x I a d₀ Y U V z w ↔ q ∈ markedRootGoodPathSet e x I a d₀ Y U V z w := by
    have hpd := markedRootGridCell_subset N hN i (markedRootPartitionCell_closed N i hp)
    have hqd := markedRootGridCell_subset N hN i (markedRootPartitionCell_closed N i hq)
    exact and_congr (iff_of_true hpd hqd)
      (markedRootPhysicalGoodPath_cell_constancy e x I a d₀ Y U V H z w hUp.ne' hVp.ne' hH hdet hw
        hfirst hbeta N hN i hi p q hp hq)
  apply (markedRootIndicator_discrepancy g₀ hU hV N hN _
    (markedRootGoodPathSet_measurable e x I a d₀ Y U V z w) Set.inter_subset_left _ hc hd).trans
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (markedRootGoodPathBadUnion_real_volume_le e x I a d₀ Y U V H z w N hN hUV hH hsmall hz) hd)

end ArtinMatthews

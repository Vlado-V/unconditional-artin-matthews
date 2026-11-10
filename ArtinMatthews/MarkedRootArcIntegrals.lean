module

public import ArtinMatthews.MarkedRootArcMajorant
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Haar integrals of the positive arc majorants. The union-bound and
Markov losses are explicit, including the true fresh probability weights. -/
namespace ArtinMatthews
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedFiniteIndicatorSum_integrable {ι : Type*} [Fintype ι]
    (E : ι → Set (AddCircle (1:ℝ))) (hE : ∀ i,MeasurableSet (E i)) :
    Integrable (fun θ => ∑ i,if θ ∈ E i then (1:ℝ) else 0) volume := by
  apply integrable_finsetSum
  intro i _
  exact (integrable_const (1:ℝ)).indicator (hE i)

theorem markedFiniteIndicatorSum_integral {ι : Type*} [Fintype ι]
    (E : ι → Set (AddCircle (1:ℝ))) (hE : ∀ i,MeasurableSet (E i)) :
    (∫ θ : AddCircle (1:ℝ),∑ i,if θ ∈ E i then (1:ℝ) else 0) = ∑ i,volume.real (E i) := by
  have hi (i : ι) : Integrable (fun θ => if θ ∈ E i then (1:ℝ) else 0) volume :=
    (integrable_const (1:ℝ)).indicator (hE i)
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  have hid : (fun θ : AddCircle (1:ℝ) => if θ ∈ E i then (1:ℝ) else 0) =
      (E i).indicator (fun _ => (1:ℝ)) := by
    funext θ
    by_cases h : θ ∈ E i <;> simp [h]
  rw [hid]
  simpa only [smul_eq_mul,mul_one] using
    integral_indicator_const (μ := (volume : Measure (AddCircle (1:ℝ)))) (1:ℝ) (hE i)

theorem markedBadRootMultiple_real_measure_le (q : ℤ) (hq : q ≠ 0)
    {ε : ℝ} (hε : 0 ≤ ε) : volume.real (markedBadRootMultiple q ε) ≤ 2*ε := by
  have h := ENNReal.toReal_mono (by finiteness : ENNReal.ofReal (2*ε) ≠ ⊤)
    (markedBadRootMultiple_measure_le q hq ε)
  change (volume (markedBadRootMultiple q ε)).toReal ≤ 2*ε
  rw [ENNReal.toReal_ofReal (show 0 ≤ 2*ε by positivity)] at h
  exact h

theorem markedPairRootArcSet_measurable (Q : Finset ℤ) (T : ℤ) (ε : ℝ) (p : Q × Q) :
    MeasurableSet (markedPairRootArcSet Q T ε p) := by
  unfold markedPairRootArcSet
  split_ifs
  · exact MeasurableSet.empty
  · exact measurableSet_markedBadRootMultiple _ _

theorem markedPairRootArcMajorant_integrable (Q : Finset ℤ) (T : ℤ) (ε : ℝ) :
    Integrable (markedPairRootArcMajorant Q T ε) volume :=
  markedFiniteIndicatorSum_integrable _ (markedPairRootArcSet_measurable Q T ε)

theorem markedPairRootArcMajorant_integral_le (Q : Finset ℤ) {T : ℤ} (hT : T ≠ 0)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (∫ θ : AddCircle (1:ℝ),markedPairRootArcMajorant Q T ε θ) ≤ 2*(Q.card:ℝ)^2*ε := by
  unfold markedPairRootArcMajorant
  rw [markedFiniteIndicatorSum_integral _ (markedPairRootArcSet_measurable Q T ε)]
  calc
    _ ≤ ∑ _p : Q × Q,2*ε := by
      apply Finset.sum_le_sum
      intro p _
      unfold markedPairRootArcSet
      split_ifs with h
      · simpa only [measureReal_empty] using mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hε
      · exact markedBadRootMultiple_real_measure_le _ (mul_ne_zero (sub_ne_zero.mpr h) hT) hε
    _ = _ := by simp [Fintype.card_prod]; ring

theorem markedWeightedPairRootArc_integrable {ι : Type*} [Fintype ι]
    (Q : Finset ℤ) (T : ι → ℤ) (w : ι → ℝ) (ε : ℝ) :
    Integrable (fun θ : AddCircle (1:ℝ) => ∑ i,w i*markedPairRootArcMajorant Q (T i) ε θ) volume := by
  apply integrable_finsetSum
  intro i _
  exact (markedPairRootArcMajorant_integrable Q (T i) ε).const_mul (w i)

theorem markedWeightedPairRootArc_integral_le {ι : Type*} [Fintype ι]
    (Q : Finset ℤ) (T : ι → ℤ) (hT : ∀ i,T i ≠ 0)
    (w : ι → ℝ) (hw : ∀ i,0 ≤ w i) (hwsum : ∑ i,w i = 1) {ε : ℝ} (hε : 0 ≤ ε) :
    (∫ θ : AddCircle (1:ℝ),∑ i,w i*markedPairRootArcMajorant Q (T i) ε θ) ≤ 2*(Q.card:ℝ)^2*ε := by
  rw [integral_finsetSum _ (fun i _ => (markedPairRootArcMajorant_integrable Q (T i) ε).const_mul (w i))]
  simp only [integral_const_mul]
  calc
    _ ≤ ∑ i,w i*(2*(Q.card:ℝ)^2*ε) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (markedPairRootArcMajorant_integral_le Q (hT i) hε) (hw i)
    _ = _ := by rw [← Finset.sum_mul,hwsum,one_mul]

theorem markedThresholdRootArc_integral_le {ι : Type*} [Fintype ι]
    (Q : Finset ℤ) (T : ι → ℤ) (hT : ∀ i,T i ≠ 0)
    (w : ι → ℝ) (hw : ∀ i,0 ≤ w i) (hwsum : ∑ i,w i = 1) (t : ℝ) :
    (∫ θ : AddCircle (1:ℝ),
      (∑ i,w i*markedPairRootArcMajorant Q (T i) (100*Real.exp (-t)) θ)/Real.exp (-t/4)) ≤
      200*(Q.card:ℝ)^2*Real.exp (-3*t/4) := by
  rw [integral_div]
  apply (div_le_div_of_nonneg_right
    (markedWeightedPairRootArc_integral_le Q T hT w hw hwsum (by positivity)) (Real.exp_pos _).le).trans_eq
  calc
    _ = 200*(Q.card:ℝ)^2*(Real.exp (-t)/Real.exp (-t/4)) := by ring
    _ = _ := by
      rw [show Real.exp (-t)/Real.exp (-t/4)=Real.exp (-3*t/4) by
        rw [← Real.exp_sub]; congr 1; ring]

end
end ArtinMatthews

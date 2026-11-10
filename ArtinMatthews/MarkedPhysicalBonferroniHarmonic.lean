module

public import ArtinMatthews.MarkedPhysicalBonferroniTailMean
public import ArtinMatthews.MarkedArrayBandStructure
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual marking bands control the performed residue-average tail.
Mertens bounds the full prime reciprocal mass; deleting used primes and
the true projective denominator p+1 only decrease it. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalInactiveProjectiveMass_le
    {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}
    (hP : ∀ j p,p∈P j → p.Prime) (I : Finset ι)
    (a : ι → MarkedPhysicalMarking P M) {K : ℝ}
    (hmass : (∑ p ∈ markedPhysicalBandPrimes P,1/(p:ℝ)) ≤ K) :
    (∑ p ∈ markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes I a,
      1/((p:ℝ)+1)) ≤ K := by
  calc
    _ ≤ ∑ p ∈ markedPhysicalBandPrimes P,1/((p:ℝ)+1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      intro p _ _
      positivity
    _ ≤ ∑ p ∈ markedPhysicalBandPrimes P,1/(p:ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨j,_,hjp⟩ := Finset.mem_biUnion.mp hp
      have hpos : (0:ℝ) < p := by exact_mod_cast (hP j p hjp).pos
      exact one_div_le_one_div_of_le hpos (by linarith)
    _ ≤ K := hmass

theorem markedPhysicalBonferroniTailMean_le_card_factorial
    {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}
    (hP : ∀ j p,p∈P j → p.Prime) (I : Finset ι)
    (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (hr : ∀ v ∈ I,0 ≤ r v ∧ r v ≤ 1)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (k : ℕ)
    {K : ℝ}
    (hmass : (∑ p ∈ markedPhysicalBandPrimes P,1/(p:ℝ)) ≤ K) :
    markedPhysicalBonferroniTailMean hP I a r z hz k ≤
      markedFactorialTail (K*(I.card:ℝ)) k := by
  have hη0 : 0 ≤ ∑ v ∈ I,(1-r v) :=
    Finset.sum_nonneg (fun v hv => sub_nonneg.mpr (hr v hv).2)
  have hη : (∑ v ∈ I,(1-r v)) ≤ (I.card:ℝ) := by
    calc
      _ ≤ ∑ _v ∈ I,(1:ℝ) := Finset.sum_le_sum (fun v hv => by linarith [(hr v hv).1])
      _ = _ := by simp
  have hp0 : 0 ≤ ∑ p ∈ markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes I a,
      1/((p:ℝ)+1) := Finset.sum_nonneg (fun _ _ => by positivity)
  have hbase : (∑ v ∈ I,(1-r v))*
      (∑ p ∈ markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes I a,1/((p:ℝ)+1)) ≤
      K*(I.card:ℝ) := by
    calc
      _ ≤ (I.card:ℝ)*K := mul_le_mul hη
        (markedPhysicalInactiveProjectiveMass_le hP I a hmass) hp0 (Nat.cast_nonneg _)
      _ = _ := mul_comm _ _
  apply (markedPhysicalBonferroniTailMean_le_factorial hP I a r hr z hz k).trans
  exact div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (mul_nonneg hη0 hp0) hbase k) (Nat.cast_nonneg _)

theorem markedPhysicalActualBonferroniTailMean_bound
    {J : Type*} [Fintype J] (e : J → ℝ)
    (he : ∀ j,0 < e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (hinj : Function.Injective e) :
    ∀ᶠ x : ℝ in atTop,∀ {ι : Type*} (M : ℕ) (I : Finset ι)
      (a : ι → MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) M)
      (r : ι → ℝ) (_hr : ∀ v ∈ I,0 ≤ r v ∧ r v ≤ 1)
      (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (k : ℕ),
      markedPhysicalBonferroniTailMean (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
        I a r z hz k ≤ markedFactorialTail ((Fintype.card J:ℝ)*(I.card:ℝ)) k := by
  filter_upwards [marked_actual_band_structure_eventually e he hinj
    (fun j => (he j).le) heUpper] with x hx
  intro ι M I a r hr z hz k
  exact markedPhysicalBonferroniTailMean_le_card_factorial _ I a r hr z hz k hx.2.2.2

end ArtinMatthews

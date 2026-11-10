module

public import ArtinMatthews.GiantComparisonMinorMultiplier
public import ArtinMatthews.GiantComparisonNatFourier
public import ArtinMatthews.GiantComparisonCirclePairing
public import ArtinMatthews.GiantComparisonCircleArcs
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Order.Interval.Finset.Box
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

/-! The free-label multiplier and the shifted integer endpoint sums
are transported to the same normalized circle, with the negative shift phase. -/
namespace ArtinMatthews
open MeasureTheory AddCircle Finset
open scoped BigOperators ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
local notation "Circle1" => AddCircle (1 : ℝ)

variable {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]

def giantComparisonNatShiftSum (P : I → Finset ℕ) (R : K → Finset ℕ)
    (f : IdealSelectedLabels P → ℂ) (g : IdealSelectedLabels R → ℂ)
    (S T : Finset ℕ) (U V : ℕ → ℂ) : ℂ :=
  ∑ a, (idealSelectedMass P a : ℂ) * f a *
    ∑ b, (idealSelectedMass R b : ℂ) * g b *
      ∑ w ∈ S, ∑ v ∈ T, if v = w + idealSelectedProduct a * idealSelectedProduct b
        then conj (U w) * V v else 0

theorem giantComparisonCircleMultiplier_eq_real (P : I → Finset ℕ) (R : K → Finset ℕ)
    (f : IdealSelectedLabels P → ℂ) (g : IdealSelectedLabels R → ℂ) (t : ℝ) :
    giantComparisonCircleMultiplier (idealSelectedMass P) (idealSelectedMass R)
      idealSelectedProduct idealSelectedProduct f g (t : Circle1) =
      giantComparisonMultiplier P R f g (-t) := by
  unfold giantComparisonCircleMultiplier giantComparisonMultiplier
  apply sum_congr rfl
  intro a _
  congr 1
  apply sum_congr rfl
  intro b _
  congr 1
  simp only [idealProductPhase, Complex.ofReal_zero, mul_zero, Complex.cpow_zero, one_mul,
    fourier_coe_apply, Real.fourierChar_apply, Complex.ofReal_one, div_one]
  congr 1
  push_cast
  ring

private theorem comparison_nat_shift (S T : Finset ℕ) (U V : ℕ → ℂ) (D : ℕ) :
    (∑ u : S.map (Nat.castEmbedding : ℕ ↪ ℤ), ∑ v : T.map (Nat.castEmbedding : ℕ ↪ ℤ),
      if v.val = u.val+(D : ℤ) then conj (U u.val.toNat)*V v.val.toNat else 0) =
    ∑ u ∈ S, ∑ v ∈ T, if v = u+D then conj (U u)*V v else 0 := by
  rw [sum_coe_sort (S.map (Nat.castEmbedding : ℕ ↪ ℤ))
    (fun u : ℤ => ∑ v : T.map (Nat.castEmbedding : ℕ ↪ ℤ),
      if v.val = u+(D : ℤ) then conj (U u.toNat)*V v.val.toNat else 0), sum_map]
  apply sum_congr rfl
  intro u _
  simp only [Nat.castEmbedding_apply, Int.toNat_natCast]
  rw [sum_coe_sort (T.map (Nat.castEmbedding : ℕ ↪ ℤ))
    (fun v : ℤ => if v = (u : ℤ)+(D : ℤ) then conj (U u)*V v.toNat else 0)]
  rw [sum_map]
  simp only [Nat.castEmbedding_apply, Int.toNat_natCast, ← Nat.cast_add, Nat.cast_inj]

theorem giantComparisonNatShiftSum_eq_integral (P : I → Finset ℕ) (R : K → Finset ℕ)
    (f : IdealSelectedLabels P → ℂ) (g : IdealSelectedLabels R → ℂ)
    (S T : Finset ℕ) (U V : ℕ → ℂ) :
    giantComparisonNatShiftSum P R f g S T U V =
      ∫ θ : Circle1, giantComparisonCircleMultiplier (idealSelectedMass P) (idealSelectedMass R)
        idealSelectedProduct idealSelectedProduct f g θ *
          conj (giantComparisonNatFourier S U θ) * giantComparisonNatFourier T V θ
        ∂AddCircle.haarAddCircle := by
  rw [giantComparisonNatFourier, giantComparisonNatFourier, giantComparisonCircle_pairing]
  unfold giantComparisonNatShiftSum
  simp only [comparison_nat_shift]

theorem giantComparisonNatShiftSum_norm_le (P : I → Finset ℕ) (R : K → Finset ℕ)
    (hP : ∀ i, 0 < bandReciprocalMass (P i)) (hR : ∀ i, 0 < bandReciprocalMass (R i))
    (f : IdealSelectedLabels P → ℂ) (g : IdealSelectedLabels R → ℂ)
    (hf : ∀ a, ‖f a‖ ≤ 1) (hg : ∀ b, ‖g b‖ ≤ 1)
    (S T : Finset ℕ) (U V : ℕ → ℂ) {Q ρ δ δarc : ℝ}
    (hQ : 1 ≤ Q) (hρ : ρ ≤ 1) (hδ : 0 ≤ δ) (hδarc : 0 ≤ δarc)
    (hminor : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ¬MarkedInRationalArc t Q ρ →
      ‖giantComparisonMultiplier P R f g (-t)‖ ≤ δ)
    (harc : ∀ r : ℚ, (r.den : ℝ) ≤ Q →
      (∫ t in Set.Icc ((r : ℝ)-ρ) ((r : ℝ)+ρ), ‖giantComparisonNatFourier S U (t : Circle1)‖^2) ≤ δarc) :
    ‖giantComparisonNatShiftSum P R f g S T U V‖ ≤
      δ*Real.sqrt ((∑ w ∈ S, ‖U w‖^2)*(∑ v ∈ T, ‖V v‖^2)) +
        Real.sqrt ((∑ v ∈ T, ‖V v‖^2)*(4*Q^2*δarc)) := by
  let m := giantComparisonCircleMultiplier (idealSelectedMass P) (idealSelectedMass R)
    idealSelectedProduct idealSelectedProduct f g
  have hm : Continuous m := giantComparisonCircleMultiplier_continuous _ _ _ _ _ _
  have hm1 (θ : Circle1) : ‖m θ‖ ≤ 1 := by
    induction θ using QuotientAddGroup.induction_on with
    | _ t =>
      dsimp only [m]
      rw [giantComparisonCircleMultiplier_eq_real P R f g t]
      exact giantComparisonMultiplier_norm_le_one P R hP hR f g hf hg _
  have hmminor (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) 1) (ha : ¬MarkedInRationalArc t Q ρ) :
      ‖m (t : Circle1)‖ ≤ δ := by
    dsimp only [m]
    rw [giantComparisonCircleMultiplier_eq_real P R f g t]
    exact hminor t ht ha
  have h := giantComparisonCircle_rational_major_minor_bound m hm
    (S.map Nat.castEmbedding) (T.map Nat.castEmbedding)
    (fun w => U w.val.toNat) (fun v => V v.val.toNat) hQ hρ hδ hδarc hm1 hmminor harc
  have hSum (Z : Finset ℕ) (F : ℕ → ℂ) :
      (∑ w : Z.map (Nat.castEmbedding : ℕ ↪ ℤ), ‖F w.val.toNat‖^2) =
        ∑ w ∈ Z, ‖F w‖^2 := by
    rw [sum_coe_sort _ (fun w : ℤ => ‖F w.toNat‖^2), sum_map]
    simp only [Nat.castEmbedding_apply, Int.toNat_natCast]
  rw [giantComparisonNatShiftSum_eq_integral]
  simpa only [hSum, m, giantComparisonNatFourier] using h

end
end ArtinMatthews

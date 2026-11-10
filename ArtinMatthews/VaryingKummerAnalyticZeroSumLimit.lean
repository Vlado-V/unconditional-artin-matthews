module

public import ArtinMatthews.VaryingKummerAnalyticZeroGrowth
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Normed.Group.Tannery
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exhaustion of actual zero sums by bounded rectangles. This is independent
of the choice of upper and lower zero-avoiding contour heights. -/
namespace OAI.PrimeDegreePackets.AnalyticGrowth
open ArtinMatthews.ReusedGrowth Complex Filter Set
open scoped Topology BigOperators
noncomputable section

theorem complex_summable_tendsto_finset_sum {α ι : Type*} {l : Filter ι}
    {a : α → ℂ} (ha : Summable a) (S : ι → Finset α)
    (hS : ∀ ρ, a ρ ≠ 0 → ∀ᶠ i in l, ρ ∈ S i) :
    Tendsto (fun i => ∑ ρ ∈ S i, a ρ) l (𝓝 (∑' ρ, a ρ)) := by
  classical
  have H := tendsto_tsum_of_dominated_convergence (𝓕 := l) (g := a)
    (f := fun i ρ => if ρ ∈ S i then a ρ else 0)
    ha.norm (fun ρ => ?_) (Filter.Eventually.of_forall (fun i ρ => ?_))
  · have he : (fun i => ∑' ρ, if ρ ∈ S i then a ρ else 0) =
        (fun i => ∑ ρ ∈ S i, a ρ) := by
      funext i
      simpa only [Set.indicator, Finset.mem_coe] using (sum_eq_tsum_indicator a (S i)).symm
    rwa [he] at H
  · by_cases h : a ρ = 0
    · simp only [h, ite_self]
      exact tendsto_const_nhds
    · apply tendsto_const_nhds.congr'
      filter_upwards [hS ρ h] with i hi
      simp [hi]
  · split_ifs
    · exact le_rfl
    · simpa only [norm_zero] using norm_nonneg (a ρ)

def zeroHeightRectangle (f : ℂ → ℂ) (a b : ℝ) : Finset ℂ :=
  (zeroDiskFinset f (|a|+|b|+2)).filter (fun ρ => a ≤ ρ.im ∧ ρ.im ≤ b)

lemma zero_in_rectangle_norm_le {ρ : ℂ} {a b : ℝ}
    (hρ0 : 0 ≤ ρ.re) (hρ1 : ρ.re ≤ 1) (ha : a ≤ ρ.im) (hb : ρ.im ≤ b) :
    ‖ρ‖ ≤ |a|+|b|+2 := by
  have him : |ρ.im| ≤ |a|+|b| := by
    apply abs_le.mpr
    constructor <;> linarith [le_abs_self b,neg_le_abs a,abs_nonneg a,abs_nonneg b]
  have H := norm_le_abs_re_add_abs_im ρ
  rw [abs_of_nonneg hρ0] at H
  linarith

lemma mem_zeroHeightRectangle_iff {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hstrip : ∀ ρ, f ρ = 0 → 0 ≤ ρ.re ∧ ρ.re ≤ 1) (a b : ℝ) (ρ : ℂ) :
    ρ ∈ zeroHeightRectangle f a b ↔ f ρ = 0 ∧ a ≤ ρ.im ∧ ρ.im ≤ b := by
  classical
  rw [zeroHeightRectangle,Finset.mem_filter]
  constructor
  · rintro ⟨hρ,ha,hb⟩
    refine ⟨?_,ha,hb⟩
    apply (zeroMultiplicity_ne_zero_iff hf h0 ρ).mp
    have H := (mem_zeroDiskFinset f (|a|+|b|+2) ρ).mp hρ
    rwa [divisor_closedBall_eq_multiplicity hf (zeroDiskFinset_norm_le hρ)] at H
  · rintro ⟨hρ,ha,hb⟩
    refine ⟨?_,ha,hb⟩
    rw [mem_zeroDiskFinset,divisor_closedBall_eq_multiplicity hf
      (zero_in_rectangle_norm_le (hstrip ρ hρ).1 (hstrip ρ hρ).2 ha hb)]
    exact (zeroMultiplicity_ne_zero_iff hf h0 ρ).mpr hρ

theorem weighted_zero_sum_tendsto_rectangles {f Φ : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hstrip : ∀ ρ, f ρ = 0 → 0 ≤ ρ.re ∧ ρ.re ≤ 1)
    (hΦ : Summable (fun ρ => (zeroMultiplicity f ρ : ℂ)*Φ ρ))
    {ι : Type*} {l : Filter ι} {a b : ι → ℝ}
    (ha : Tendsto a l atBot) (hb : Tendsto b l atTop) :
    Tendsto (fun i => ∑ ρ ∈ zeroHeightRectangle f (a i) (b i),
      (zeroMultiplicity f ρ : ℂ)*Φ ρ) l
        (𝓝 (∑' ρ, (zeroMultiplicity f ρ : ℂ)*Φ ρ)) := by
  apply complex_summable_tendsto_finset_sum hΦ
  intro ρ hρ
  have hm : zeroMultiplicity f ρ ≠ 0 := by
    intro H
    simp only [H,Int.cast_zero,zero_mul,ne_eq,not_true_eq_false] at hρ
  have hz := (zeroMultiplicity_ne_zero_iff hf h0 ρ).mp hm
  filter_upwards [ha.eventually_le_atBot ρ.im,hb.eventually_ge_atTop ρ.im] with i hai hbi
  exact (mem_zeroHeightRectangle_iff hf h0 hstrip _ _ ρ).mpr ⟨hz,hai,hbi⟩

end
end OAI.PrimeDegreePackets.AnalyticGrowth

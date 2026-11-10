module

public import ArtinMatthews.GiantPrimeExtractionArithmetic
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

/-! Composition at a fixed sieve depth. The analytic input is cancellation
of the displayed ordinary composite tuple sums. The proved arithmetic
remainder and the positive literal array mean transfer the actual rough
bound to the actual prime sum without changing the surviving error constant.
No composite cancellation or centered giant-factor law is claimed here. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators Asymptotics

theorem giant_ordinary_prime_sub_rough_isLittleO_of_tuple
    {J : Type*} [Fintype J] (e : J → ℝ) (he : ∀ j, 0 < e j)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    {CG : ℝ} (hCG : 0 ≤ CG) (hG : ∀ᶠ x : ℝ in atTop, ∀ u, ‖G x u‖ ≤ CG)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) {a b T γ : ℝ} (ha : 0 < a)
    (hsupp : Function.support Φ ⊆ Set.Icc a b) (hT : 0 ≤ T)
    (hγ : 0 < γ) (hγ1 : γ < 1) (A : ℝ)
    (htuple : ∀ j ∈ Finset.Icc 2 ⌈2/γ⌉₊,
      giantOrdinaryTupleSum e χ G Φ T γ j =o[atTop]
        (fun x : ℝ => x * (Real.log x)^(-A))) :
    (fun x => giantOrdinaryPrimeSum e χ G Φ T x - giantOrdinaryRoughSum e χ G Φ T γ x)
      =o[atTop] (fun x : ℝ => x * (Real.log x)^(-A)) := by
  have hs : (fun x => ∑ j ∈ Finset.Icc 2 ⌈2/γ⌉₊,
      giantOrdinaryTupleSum e χ G Φ T γ j x) =o[atTop]
        (fun x : ℝ => x * (Real.log x)^(-A)) := by
    apply (Asymptotics.IsLittleO.sum htuple).congr' _ Filter.EventuallyEq.rfl
    filter_upwards [] with x
    simp only [Finset.sum_apply]
  have hr := giant_ordinary_prime_rough_reduction e he χ G hCG hG Φ hΦ ha hsupp hT hγ hγ1 A
  apply (hr.add hs).neg_left.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [] with x
  ring

/-- Negligible prime-minus-rough errors preserve the constant in a normalized
rough bound. A fixed positive lower bound for the true mean is sufficient. -/
theorem giant_normalized_bound_transfer (P R : ℝ → ℂ) (m : ℝ → ℝ)
    {c : ℝ} (hc : 0 < c) (hm : ∀ᶠ x : ℝ in atTop, c ≤ m x)
    (herror : (fun x => P x-R x) =o[atTop] (fun x : ℝ => x/Real.log x))
    (E : ℝ)
    (hrough : ∀ δ : ℝ, 0 < δ → ∀ᶠ x : ℝ in atTop,
      Real.log x/(x*m x) * ‖R x‖ ≤ E+δ) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ x : ℝ in atTop,
      Real.log x/(x*m x) * ‖P x‖ ≤ E+δ := by
  intro δ hδ
  have hsmall := herror.bound (show 0 < c*(δ/2) by positivity)
  filter_upwards [hm, hsmall, hrough (δ/2) (by positivity),
    eventually_gt_atTop (1 : ℝ)] with x hmx hs hr hx
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hl : 0 < Real.log x := Real.log_pos hx
  have hm0 : 0 < m x := hc.trans_le hmx
  have he : Real.log x/(x*m x) * ‖P x-R x‖ ≤ δ/2 := by
    calc
      _ ≤ Real.log x/(x*m x) * (c*(δ/2)*(x/Real.log x)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [Real.norm_eq_abs, abs_of_pos (div_pos hx0 hl)] using hs
      _ ≤ Real.log x/(x*c) * (c*(δ/2)*(x/Real.log x)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact div_le_div_of_nonneg_left hl.le (mul_pos hx0 hc)
          (mul_le_mul_of_nonneg_left hmx hx0.le)
      _ = δ/2 := by field_simp
  have hp : ‖P x‖ ≤ ‖R x‖+‖P x-R x‖ := by
    simpa only [add_sub_cancel] using norm_add_le (R x) (P x-R x)
  calc
    _ ≤ Real.log x/(x*m x) * (‖R x‖+‖P x-R x‖) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = Real.log x/(x*m x) * ‖R x‖ + Real.log x/(x*m x) * ‖P x-R x‖ := mul_add ..
    _ ≤ (E+δ/2)+δ/2 := add_le_add hr he
    _ = E+δ := by ring

/-- Fixed-depth ordinary extraction with the literal model mean. The tuple
input is precisely the arithmetic output above, not the desired prime bound. -/
theorem giant_ordinary_prime_bound_of_rough_and_tuple
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (he : ∀ j, 0 < e j)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    {CG : ℝ} (hCG : 0 ≤ CG) (hG : ∀ᶠ x : ℝ in atTop, ∀ u, ‖G x u‖ ≤ CG)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) {a b T γ : ℝ} (ha : 0 < a)
    (hsupp : Function.support Φ ⊆ Set.Icc a b) (hT : 0 ≤ T)
    (hγ : 0 < γ) (hγ1 : γ < 1) (E : ℝ)
    (htuple : ∀ j ∈ Finset.Icc 2 ⌈2/γ⌉₊,
      giantOrdinaryTupleSum e χ G Φ T γ j =o[atTop]
        (fun x : ℝ => x/Real.log x))
    (hrough : ∀ δ : ℝ, 0 < δ → ∀ᶠ x : ℝ in atTop,
      Real.log x/(x*literalMarkedArrayMean e x) * ‖giantOrdinaryRoughSum e χ G Φ T γ x‖ ≤ E+δ) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ x : ℝ in atTop,
      Real.log x/(x*literalMarkedArrayMean e x) * ‖giantOrdinaryPrimeSum e χ G Φ T x‖ ≤ E+δ := by
  have heq (x : ℝ) : x*(Real.log x)^(-(1 : ℝ)) = x/Real.log x := by
    rw [Real.rpow_neg_one, div_eq_mul_inv]
  have herror := giant_ordinary_prime_sub_rough_isLittleO_of_tuple
    e he χ G hCG hG Φ hΦ ha hsupp hT hγ hγ1 1 (by simpa only [heq] using htuple)
  apply giant_normalized_bound_transfer _ _ (literalMarkedArrayMean e)
    (show 0 < (1/2 : ℝ)^Fintype.card J by positivity)
    (literalMarkedArrayMean_lower_eventually e he) _ E hrough
  simpa only [heq] using herror

end ArtinMatthews

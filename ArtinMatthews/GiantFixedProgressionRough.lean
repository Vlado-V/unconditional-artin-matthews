module

public import ArtinMatthews.GiantFixedResidueActualRough
public import ArtinMatthews.GiantBoundedProgression
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
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Summing the actual rough estimates over a finite set of unit classes
gives the exact fixed-progression density times the depth error. -/
namespace ArtinMatthews
open Filter
open scoped Topology BigOperators
noncomputable section

def giantFixedProgressionArrayRoughRaw {M : ℕ} (U : Finset (ZMod M)ˣ)
    {J : Type*} [Fintype J] (e : J → ℝ)
    (ε : ℝ) (Φ : ℝ → ℝ) (T x γ : ℝ) : ℂ := by
  classical
  exact ∑ u∈(Finset.Icc 0 ⌊T*x⌋₊).filter (fun u => MarkedRoughAbove (x^γ) (u+1)),
    (Φ ((u:ℝ)/x):ℂ)*giantFixedResidueLiteralCoefficient U ε x u*
      (literalMarkedArrayWeight e x u:ℂ)

theorem giantFixedResidueUnit_modEq {M : ℕ} [NeZero M] (a : (ZMod M)ˣ) (n : ℕ) :
    (a:ZMod M)=(n:ZMod M) ↔ Nat.ModEq M n (a:ZMod M).val := by
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
  exact eq_comm

theorem giantFixedProgressionArrayRoughRaw_eq_sum {M : ℕ} [NeZero M]
    (U : Finset (ZMod M)ˣ) {J : Type*} [Fintype J] (e : J → ℝ)
    (ε : ℝ) (Φ : ℝ → ℝ) (T x γ : ℝ) :
    giantFixedProgressionArrayRoughRaw U e ε Φ T x γ =
      ∑ a∈U,(giantFixedResidueCenteredRoughSum M (a:ZMod M).val e ε Φ T x γ:ℂ) := by
  classical
  unfold giantFixedProgressionArrayRoughRaw giantFixedResidueLiteralCoefficient
  simp only [giantUnitResidueIndicator_eq_sum,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  have hset : (giantFixedResidueSet M (a:ZMod M).val 1 (T*x)).filter
        (fun u => MarkedRoughAbove (x^γ) (u+1)) =
      ((Finset.Icc 0 ⌊T*x⌋₊).filter (fun u => MarkedRoughAbove (x^γ) (u+1))).filter
        (fun u => (a:ZMod M)=((u+1:ℕ):ZMod M)) := by
    ext u
    simp only [giantFixedResidueSet,Finset.mem_filter,one_dvd,true_and,giantFixedResidueUnit_modEq]
    tauto
  unfold giantFixedResidueCenteredRoughSum giantFixedResidueRoughSum
  rw [hset]
  push_cast
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u _
  split_ifs <;> ring

theorem giant_fixed_progression_array_rough_bound {M : ℕ} [NeZero M]
    (U : Finset (ZMod M)ˣ) {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ)
    (he : ∀ j,(1/10:ℝ)<e j ∧ e j<1/5) (hinj : Function.Injective e)
    (ε c : ℝ) (m : ℕ) (hε : 0<ε) (hεq : ε<1/4) (hc : 0<c) (hcε : c<ε/2)
    (hm : 20000 ≤ m) (Φ : ℝ → ℝ) {T : ℝ}
    (hT : 0≤T) (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ))
    (hΦT : Φ T=0) (hΦ0 : ∀ t,0≤Φ t) (hΦzero : Φ 0=0) {η : ℝ} (hη : 0<η) :
    ∀ᶠ x : ℝ in atTop,
      Real.log x/(x*literalMarkedArrayMean e x)*
        ‖giantFixedProgressionArrayRoughRaw U e ε Φ T x (markedSieveExponent c m)‖ ≤
        (U.card:ℝ)*giantFixedResidueRoughError M Φ T c m+η := by
  classical
  let η₀ := η/((U.card:ℝ)+1)
  have hη₀ : 0<η₀ := div_pos hη (by positivity)
  have hs : ∀ᶠ x : ℝ in atTop,∀ a : (ZMod M)ˣ,
      Real.log x/(x*literalMarkedArrayMean e x)*
        |giantFixedResidueCenteredRoughSum M (a:ZMod M).val e ε Φ T x (markedSieveExponent c m)| ≤
        giantFixedResidueRoughError M Φ T c m+η₀ := by
    exact eventually_all.mpr (fun a => giantFixedResidue_actual_centered_rough_bound M
      (a:ZMod M).val (NeZero.pos M) (ZMod.val_coe_unit_coprime a) e he hinj ε c m hε hεq
      hc hcε hm Φ hT hΦ hderiv hΦT hΦ0 hΦzero hη₀)
  filter_upwards [hs,eventually_gt_atTop (1:ℝ),
    literalMarkedArrayMean_lower_eventually e (fun j => lt_trans (by norm_num) (he j).1)]
    with x hx hxp hmean
  let γ := markedSieveExponent c m
  let scale := Real.log x/(x*literalMarkedArrayMean e x)
  let E := giantFixedResidueRoughError M Φ T c m
  have hs₀ : 0 ≤ scale :=
    div_nonneg (Real.log_pos hxp).le (mul_nonneg ((zero_lt_one.trans hxp).le) ((by positivity : 0≤(1/2:ℝ)^Fintype.card J).trans hmean))
  have hη' : (U.card:ℝ)*η₀≤η := by
    dsimp [η₀]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0<(U.card:ℝ)+1)).mpr
    nlinarith
  rw [giantFixedProgressionArrayRoughRaw_eq_sum]
  calc
    _ ≤ scale*∑ a∈U,|giantFixedResidueCenteredRoughSum M (a:ZMod M).val e ε Φ T x γ| := by
      apply mul_le_mul_of_nonneg_left _ hs₀
      simpa only [Complex.norm_real,Real.norm_eq_abs] using norm_sum_le U
        (fun a => (giantFixedResidueCenteredRoughSum M (a:ZMod M).val e ε Φ T x γ:ℂ))
    _ = ∑ a∈U,scale*|giantFixedResidueCenteredRoughSum M (a:ZMod M).val e ε Φ T x γ| :=
      Finset.mul_sum U _ _
    _ ≤ ∑ _a∈U,(E+η₀) := Finset.sum_le_sum (fun a _ => hx a)
    _ = (U.card:ℝ)*E+(U.card:ℝ)*η₀ := by
      rw [Finset.sum_const,nsmul_eq_mul,mul_add]
    _ ≤ _ := add_le_add le_rfl hη'

end
end ArtinMatthews

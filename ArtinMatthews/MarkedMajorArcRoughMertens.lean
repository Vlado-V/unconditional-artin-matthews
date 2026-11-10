module

public import ArtinMatthews.MarkedSieveMertens
public import ArtinMatthews.RoughBonferroniDivisors
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Actual Euler-product control of the reciprocal divisor mass and the
rough-number density normalization. -/
namespace ArtinMatthews
open Finset Filter
open scoped Topology

 theorem marked_rough_plus_product_le_inverse (y : ℝ) :
    (∏ p ∈ Nat.primesLE ⌊y⌋₊, (1+(p:ℝ)⁻¹)) ≤
      (markedSieveEulerProduct y)⁻¹ := by
  rw [markedSieveEulerProduct, ← prod_inv_distrib]
  apply Finset.prod_le_prod₀
  · intro p _
    positivity
  · intro p hp
    have hp1 : (1:ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt
    have hpp : (0:ℝ) < p := by linarith
    have hi : (p:ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
    have hpos : 0 < 1-1/(p:ℝ) := by simpa only [one_div] using sub_pos.mpr hi
    have hfac : (1+1/(p:ℝ))*(1-1/(p:ℝ)) ≤ 1 := by
      nlinarith [sq_nonneg (1/(p:ℝ))]
    simpa only [one_div] using (le_div_iff₀ hpos).mpr hfac


 theorem marked_rough_reciprocal_mass_le_inverse (y : ℝ) (r : ℕ) :
    (∑ S ∈ roughTruncationSubsets (Nat.primesLE ⌊y⌋₊) r,
      ‖(-1:ℂ)^S.card‖/(roughSubsetDivisor S:ℝ)) ≤
      (markedSieveEulerProduct y)⁻¹ :=
  (roughDivisorPolynomial_reciprocal_mass_le _ _).trans
    (marked_rough_plus_product_le_inverse y)

 theorem marked_rough_density_inverse_eventually :
    ∀ᶠ y : ℝ in atTop,
      (markedSieveEulerProduct y)⁻¹ ≤
        Real.exp (Real.eulerMascheroniConstant+1)*Real.log y := by
  have hE := (Asymptotics.isLittleO_one_iff ℝ).mp Mertens.E₃.bound'
  filter_upwards [hE.eventually (lt_mem_nhds (by norm_num : (-1:ℝ)<0)),
    eventually_gt_atTop (1:ℝ)] with y hE hy
  have hlog : 0 < Real.log y := Real.log_pos hy
  rw [markedSieveEulerProduct_eq hy]
  have hlower : Real.exp (-Real.eulerMascheroniConstant)*Real.exp (-1)/Real.log y ≤
      Real.exp (-Real.eulerMascheroniConstant)*Real.exp (Mertens.E₃ y)/Real.log y := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hE.le) (Real.exp_pos _).le) hlog.le
  have hp : 0 < Real.exp (-Real.eulerMascheroniConstant)*Real.exp (-1)/Real.log y := by positivity
  calc
    _ ≤ (Real.exp (-Real.eulerMascheroniConstant)*Real.exp (-1)/Real.log y)⁻¹ :=
      inv_anti₀ hp hlower
    _ = _ := by
      rw [← Real.exp_add, inv_div, div_eq_mul_inv, ← Real.exp_neg]
      rw [show -(-Real.eulerMascheroniConstant + -1) = Real.eulerMascheroniConstant+1 by ring]
      exact mul_comm _ _

 theorem marked_rough_density_inverse_cutoff (κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ L : ℝ in atTop,
      (markedSieveEulerProduct (Real.exp (L^κ)))⁻¹ ≤
        Real.exp (Real.eulerMascheroniConstant+1)*L^κ := by
  have ht := Real.tendsto_exp_atTop.comp (tendsto_rpow_atTop hκ)
  simpa only [Function.comp_apply, Real.log_exp] using ht.eventually marked_rough_density_inverse_eventually

 theorem marked_rough_prime_reciprocal_cutoff_le (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1) :
    ∀ᶠ L : ℝ in atTop,
      (∑ p ∈ Nat.primesLE ⌊Real.exp (L^κ)⌋₊, 1/(p:ℝ)) ≤ Real.log L := by
  obtain ⟨C,hC⟩ := Mertens.sum_prime_div_eq_log_log
  have ht := Real.tendsto_exp_atTop.comp (tendsto_rpow_atTop hκ)
  filter_upwards [ht.eventually (eventually_ge_atTop (2:ℝ)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (C/(1-κ))),
    eventually_gt_atTop (0:ℝ)] with L hL2 hLC hL
  have hset : Nat.primesLE ⌊Real.exp (L^κ)⌋₊ =
      (Ioc 0 ⌊Real.exp (L^κ)⌋₊).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesLE,mem_filter,mem_Ioc]
    constructor
    · rintro ⟨hp,hprime⟩
      exact ⟨⟨hprime.pos,hp⟩,hprime⟩
    · rintro ⟨⟨_,hp⟩,hprime⟩
      exact ⟨hp,hprime⟩
  have hh := (abs_le.mp (hC (Real.exp (L^κ)) hL2)).2
  rw [Real.log_exp,Real.log_rpow hL] at hh
  have hscale : C ≤ (1-κ)*Real.log L := by
    have hc := (div_le_iff₀ (by linarith : 0<1-κ)).mp hLC
    nlinarith
  rw [hset]
  linarith

end ArtinMatthews

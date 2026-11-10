module

public import ArtinMatthews.IdealProductDyadic
public import ArtinMatthews.IdealLogCellCount
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

/-! The source prime bounds control every occupied product dyad and
the total number of dyads, uniformly in the finite slot carrier. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem idealSelectedProduct_ge_prime (P : I → Finset ℕ)
    (hP : ∀ i p, p ∈ P i → p.Prime) (a : IdealSelectedLabels P) (i : I) :
    (a i).val ≤ idealSelectedProduct a :=
  Nat.le_of_dvd (idealSelectedProduct_pos hP a) (dvd_prod_of_mem _ (mem_univ i))

theorem idealSelectedProductDyad_range (P : I → Finset ℕ)
    (hP : ∀ i p, p ∈ P i → p.Prime) (Y Z : ℝ)
    (hlower : ∀ i p, p ∈ P i → Real.exp Y ≤ (p : ℝ))
    (hupper : ∀ i p, p ∈ P i → (p : ℝ) ≤ Real.exp Z) (i : I)
    {j : ℕ} (hj : j ∈ idealProductDyads (idealSelectedProduct (P := P))) :
    Real.exp Y/2 < ((2^j : ℕ) : ℝ) ∧
      ((2^j : ℕ) : ℝ) ≤ Real.exp ((Fintype.card I : ℝ)*Z) := by
  obtain ⟨a, _, rfl⟩ := mem_image.mp hj
  have hp := idealSelectedProduct_pos hP a
  have hdyad := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ))
    (idealSelectedProduct a)
  have hb : (idealSelectedProduct a : ℝ) < 2*((2^(Nat.log 2 (idealSelectedProduct a)) : ℕ) : ℝ) := by
    exact_mod_cast (show idealSelectedProduct a < 2*2^(Nat.log 2 (idealSelectedProduct a)) by
      simpa only [pow_succ'] using hdyad)
  have hlo : Real.exp Y ≤ (idealSelectedProduct a : ℝ) := by
    exact (hlower i _ (a i).property).trans (by exact_mod_cast idealSelectedProduct_ge_prime P hP a i)
  constructor
  · linarith
  · calc
      _ ≤ (idealSelectedProduct a : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hp.ne'
      _ = Real.exp (Real.log (idealSelectedProduct a)) := (Real.exp_log (by exact_mod_cast hp)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (idealSelectedProduct_log_le P hP hupper a)

universe u

theorem idealSelectedProductDyads_uniform (d C : ℝ) (hd : 0 ≤ d) :
    ∀ᶠ L : ℝ in atTop, ∀ (I : Type u) [Fintype I] [DecidableEq I],
      ∀ P : I → Finset ℕ, (∀ i p, p ∈ P i → p.Prime) →
      (∀ i p, p ∈ P i → (p : ℝ) ≤ Real.exp (L^d)) →
      (Fintype.card I : ℝ) ≤ C*Real.log L →
      ((idealProductDyads (idealSelectedProduct (P := P))).card : ℝ) ≤ L^(d+3) := by
  let K := 1+(Real.log 2)⁻¹
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [eventually_ge_atTop (max 2 (max C K))] with L hlarge
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hlarge
  have hL1 : 1 ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hCL : C ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hKL : K ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
  intro I _ _ P hP hupper hcard
  have hc : (Fintype.card I : ℝ) ≤ L^2 := by
    calc
      _ ≤ C*Real.log L := hcard
      _ ≤ L*L := mul_le_mul hCL (Real.log_le_self hL.le) (Real.log_nonneg hL1) hL.le
      _ = _ := (pow_two _).symm
  have hp : 1 ≤ L^(d+2) := Real.one_le_rpow hL1 (by linarith)
  calc
    _ ≤ 1+(Fintype.card I : ℝ)*L^d/Real.log 2 :=
      idealSelectedProductDyads_card_le P hP (Real.rpow_nonneg hL.le _) hupper
    _ ≤ 1+L^2*L^d/Real.log 2 := by
      have hh := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hL.le d)) hlog.le
      linarith
    _ = 1+L^(d+2)/Real.log 2 := by
      rw [← Real.rpow_two, ← Real.rpow_add hL]
      congr 2
      ring
    _ ≤ K*L^(d+2) := by dsimp only [K]; rw [div_eq_mul_inv]; nlinarith
    _ ≤ L*L^(d+2) := mul_le_mul_of_nonneg_right hKL (Real.rpow_nonneg hL.le _)
    _ = _ := by nth_rw 1 [← Real.rpow_one L]; rw [← Real.rpow_add hL]; congr 1; ring

end
end ArtinMatthews

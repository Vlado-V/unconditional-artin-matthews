module

public import ArtinMatthews.IdealProductDyadic
public import ArtinMatthews.IdealProductDyadicBounds
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

/-! Every occupied source product dyad has a positive half-scale,
with the exact lower and upper bounds needed by the Gram estimate. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable

def idealProductDyadicOrigin (j : ℕ) : ℕ := 2^(j-1)

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem idealSelectedProductDyad_positive (P : I → Finset ℕ)
    (hP : ∀ i p, p ∈ P i → p.Prime) (i : I) {j : ℕ}
    (hj : j ∈ idealProductDyads (idealSelectedProduct (P := P))) : 0 < j := by
  obtain ⟨x, _, rfl⟩ := mem_image.mp hj
  apply Nat.log_pos (by norm_num)
  exact (hP i _ (x i).property).two_le.trans (idealSelectedProduct_ge_prime P hP x i)

theorem idealProductDyadicOrigin_double {j : ℕ} (hj : 0 < j) :
    2*idealProductDyadicOrigin j = 2^j := by
  unfold idealProductDyadicOrigin
  rw [← pow_succ']
  congr 1
  omega

theorem idealSelectedProductDyadicPart_origin_support (P : I → Finset ℕ)
    (hP : ∀ i p, p ∈ P i → p.Prime) (i : I) {j : ℕ}
    (hj : j ∈ idealProductDyads (idealSelectedProduct (P := P)))
    (f : IdealSelectedLabels P → ℂ) :
    ∀ x, idealSelectedProduct x ∉ Ico (2*idealProductDyadicOrigin j) (4*idealProductDyadicOrigin j) →
      idealProductDyadicPart idealSelectedProduct j f x = 0 := by
  intro x hx
  by_contra hn
  have hs := idealProductDyadicPart_support idealSelectedProduct (idealSelectedProduct_pos hP) j f x hn
  have he := idealProductDyadicOrigin_double (idealSelectedProductDyad_positive P hP i hj)
  apply hx
  rw [he, show 4*idealProductDyadicOrigin j = 2^j+2^j by omega]
  exact hs

theorem idealSelectedProductDyadicOrigin_bounds (P : I → Finset ℕ)
    (hP : ∀ i p, p ∈ P i → p.Prime) (Y Z : ℝ)
    (hlower : ∀ i p, p ∈ P i → Real.exp Y ≤ (p : ℝ))
    (hupper : ∀ i p, p ∈ P i → (p : ℝ) ≤ Real.exp Z) (i : I) {j : ℕ}
    (hj : j ∈ idealProductDyads (idealSelectedProduct (P := P))) :
    0 < idealProductDyadicOrigin j ∧ Real.exp Y/4 ≤ (idealProductDyadicOrigin j : ℝ) ∧
      Real.log (idealProductDyadicOrigin j : ℝ) ≤ (Fintype.card I : ℝ)*Z := by
  have hjp := idealSelectedProductDyad_positive P hP i hj
  have he := idealProductDyadicOrigin_double hjp
  have hb := idealSelectedProductDyad_range P hP Y Z hlower hupper i hj
  have hpos : 0 < idealProductDyadicOrigin j := by unfold idealProductDyadicOrigin; positivity
  refine ⟨hpos, ?_, ?_⟩
  · have her : 2*(idealProductDyadicOrigin j : ℝ) = ((2^j : ℕ) : ℝ) := by exact_mod_cast he
    linarith [hb.1]
  · apply (Real.log_le_iff_le_exp (by exact_mod_cast hpos)).mpr
    apply le_trans _ hb.2
    exact_mod_cast (show idealProductDyadicOrigin j ≤ 2^j by omega)

universe u

theorem idealSelectedProductDyadicOrigin_uniform (c d C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (I : Type u) [Fintype I] [DecidableEq I],
      ∀ (P : I → Finset ℕ), (∀ i p, p ∈ P i → p.Prime) →
      (∀ i p, p ∈ P i → Real.exp (L^c) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L^d)) →
      (Fintype.card I : ℝ) ≤ C*Real.log L →
      ∀ (_i : I) (j : ℕ), j ∈ idealProductDyads (idealSelectedProduct (P := P)) →
      0 < idealProductDyadicOrigin j ∧
      Real.exp (L^c)/4 ≤ (idealProductDyadicOrigin j : ℝ) ∧
      Real.log (idealProductDyadicOrigin j : ℝ) ≤ L^(d+2) := by
  filter_upwards [eventually_ge_atTop (max 2 C)] with L hlarge
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hlarge
  have hL1 : 1 ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hCL : C ≤ L := (le_max_right _ _).trans hlarge
  intro I _ _ P hP hbounds hcard i j hj
  have hb := idealSelectedProductDyadicOrigin_bounds P hP (L^c) (L^d)
    (fun i p hp => (hbounds i p hp).1) (fun i p hp => (hbounds i p hp).2) i hj
  refine ⟨hb.1, hb.2.1, hb.2.2.trans ?_⟩
  have hcard2 : (Fintype.card I : ℝ) ≤ L^2 := by
    calc
      _ ≤ C*Real.log L := hcard
      _ ≤ L*L := mul_le_mul hCL (Real.log_le_self hL.le) (Real.log_nonneg hL1) hL.le
      _ = _ := (pow_two _).symm
  calc
    _ ≤ L^2*L^d := mul_le_mul_of_nonneg_right hcard2 (Real.rpow_nonneg hL.le d)
    _ = _ := by rw [← Real.rpow_two, ← Real.rpow_add hL]; congr 1; ring

end
end ArtinMatthews

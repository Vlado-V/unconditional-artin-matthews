module

public import ArtinMatthews.IdealFiniteFrame
public import ArtinMatthews.IdealSelectedLabels
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact dyadic partition of arbitrary tests on the full ordered-label
space, with the number of pieces bounded by the actual product range. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [Fintype Ω]

def idealProductDyads (p : Ω → ℕ) : Finset ℕ :=
  univ.image (fun x => Nat.log 2 (p x))

def idealProductDyadicPart (p : Ω → ℕ) (j : ℕ) (f : Ω → ℂ) (x : Ω) : ℂ :=
  if Nat.log 2 (p x) = j then f x else 0

theorem idealProductDyadicPart_sum (p : Ω → ℕ) (f : Ω → ℂ) (x : Ω) :
    (∑ j ∈ idealProductDyads p, idealProductDyadicPart p j f x) = f x := by
  rw [sum_eq_single (Nat.log 2 (p x))]
  · simp only [idealProductDyadicPart, ite_true]
  · intro j _ hj
    exact ite_eq_right (fun h => hj h.symm)
  · intro h
    exact (h (mem_image.mpr ⟨x, mem_univ x, rfl⟩)).elim

omit [Fintype Ω] in
theorem idealProductDyadicPart_support (p : Ω → ℕ) (hp : ∀ x, 0 < p x)
    (j : ℕ) (f : Ω → ℂ) (x : Ω) (hx : idealProductDyadicPart p j f x ≠ 0) :
    p x ∈ Ico (2^j) (2^j+2^j) := by
  have he : Nat.log 2 (p x) = j := by
    by_contra h
    exact hx (ite_eq_right h)
  have hb := (Nat.log_eq_iff (b := 2) (m := j) (n := p x)
    (Or.inr ⟨by norm_num, (hp x).ne'⟩)).mp he
  simpa only [mem_Ico, pow_succ, mul_two] using hb

theorem idealProductDyadicPart_energy (μ : Ω → ℝ) (p : Ω → ℕ) (f : Ω → ℂ) :
    (∑ j ∈ idealProductDyads p, idealFrameEnergy μ (idealProductDyadicPart p j f)) =
      idealFrameEnergy μ f := by
  unfold idealFrameEnergy
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  rw [sum_eq_single (Nat.log 2 (p x))]
  · simp only [idealProductDyadicPart, ite_true]
  · intro j _ hj
    have he : Nat.log 2 (p x) ≠ j := Ne.symm hj
    rw [idealProductDyadicPart, ite_eq_right he, norm_zero, zero_pow (by decide), mul_zero]
  · intro h
    exact (h (mem_image.mpr ⟨x, mem_univ x, rfl⟩)).elim

theorem idealProductDyads_card_le (p : Ω → ℕ) (hp : ∀ x, 0 < p x)
    {Y : ℝ} (hY : 0 ≤ Y) (hupper : ∀ x, Real.log (p x) ≤ Y) :
    ((idealProductDyads p).card : ℝ) ≤ 1+Y/Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsub : idealProductDyads p ⊆ range (⌊Y/Real.log 2⌋₊+1) := by
    intro j hj
    obtain ⟨x, _, rfl⟩ := mem_image.mp hj
    have hpow : (2 : ℝ)^(Nat.log 2 (p x)) ≤ (p x : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (hp x).ne'
    have hb := Real.log_le_log (by positivity : (0 : ℝ) < 2^(Nat.log 2 (p x))) hpow
    rw [Real.log_pow] at hb
    have hj : (Nat.log 2 (p x) : ℝ) ≤ Y/Real.log 2 :=
      (le_div_iff₀ hlog).mpr (hb.trans (hupper x))
    exact mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_floor_iff (by positivity)).mpr hj))
  calc
    _ ≤ ((range (⌊Y/Real.log 2⌋₊+1)).card : ℝ) := by exact_mod_cast card_le_card hsub
    _ = (⌊Y/Real.log 2⌋₊ : ℝ)+1 := by simp only [card_range, Nat.cast_add, Nat.cast_one]
    _ ≤ 1+Y/Real.log 2 := by
      have hh := Nat.floor_le (div_nonneg hY hlog.le)
      linarith

theorem idealSelectedProductDyads_card_le {I : Type*} [Fintype I] [DecidableEq I]
    (P : I → Finset ℕ) (hP : ∀ i p, p ∈ P i → p.Prime)
    {Y : ℝ} (hY : 0 ≤ Y) (hupper : ∀ i p, p ∈ P i → (p : ℝ) ≤ Real.exp Y) :
    ((idealProductDyads (idealSelectedProduct (P := P))).card : ℝ) ≤
      1+(Fintype.card I : ℝ)*Y/Real.log 2 :=
  idealProductDyads_card_le _ (idealSelectedProduct_pos hP) (by positivity)
    (idealSelectedProduct_log_le P hP hupper)

end
end ArtinMatthews

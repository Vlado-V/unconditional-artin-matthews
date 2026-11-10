module

public import ArtinMatthews.IdealProductDyadic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Exact finite dyadic reassembly and its energy cost are independent
of the kernel and therefore apply to the literal comparison difference. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem fourSum_comm {A B C D M : Type*} [AddCommMonoid M]
    (s : Finset A) (t : Finset B) (u : Finset C) (v : Finset D)
    (F : A → B → C → D → M) :
    (∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, ∑ d ∈ v, F a b c d) =
      ∑ c ∈ u, ∑ d ∈ v, ∑ a ∈ s, ∑ b ∈ t, F a b c d := by
  calc
    _ = ∑ a ∈ s, ∑ c ∈ u, ∑ b ∈ t, ∑ d ∈ v, F a b c d := by
      apply sum_congr rfl
      intro a _
      exact sum_comm
    _ = ∑ c ∈ u, ∑ a ∈ s, ∑ b ∈ t, ∑ d ∈ v, F a b c d := sum_comm
    _ = ∑ c ∈ u, ∑ a ∈ s, ∑ d ∈ v, ∑ b ∈ t, F a b c d := by
      apply sum_congr rfl
      intro c _
      apply sum_congr rfl
      intro a _
      exact sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro c _
      exact sum_comm

theorem idealProductDyadic_pairing {A B : Type*} [Fintype A] [Fintype B]
    (p : A → ℕ) (q : B → ℕ) (μ : A → ℝ) (ν : B → ℝ)
    (f : A → ℂ) (g : B → ℂ) (K : A → B → ℂ) :
    (∑ x, (μ x : ℂ)*f x*∑ y, (ν y : ℂ)*g y*K x y) =
      ∑ j ∈ idealProductDyads p, ∑ k ∈ idealProductDyads q,
        ∑ x, (μ x : ℂ)*idealProductDyadicPart p j f x*
          ∑ y, (ν y : ℂ)*idealProductDyadicPart q k g y*K x y := by
  symm
  simp only [mul_sum]
  rw [fourSum_comm]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  calc
    _ = (μ x : ℂ)*(∑ j ∈ idealProductDyads p, idealProductDyadicPart p j f x)*
        (ν y : ℂ)*(∑ k ∈ idealProductDyads q, idealProductDyadicPart q k g y)*K x y := by
      simp only [mul_sum, sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [idealProductDyadicPart_sum, idealProductDyadicPart_sum]; ring

theorem idealFinitePairing_sq_le {A B : Type*} (s : Finset A) (t : Finset B)
    (F : A → B → ℂ) {E : ℝ}
    (hF : ∀ a ∈ s, ∀ b ∈ t, ‖F a b‖^2 ≤ E) :
    ‖∑ a ∈ s, ∑ b ∈ t, F a b‖^2 ≤ (s.card : ℝ)^2*(t.card : ℝ)^2*E := by
  have hsum : (∑ z ∈ s ×ˢ t, F z.1 z.2) = ∑ a ∈ s, ∑ b ∈ t, F a b :=
    sum_product s t (fun z => F z.1 z.2)
  rw [← hsum]
  have hn := (sq_le_sq₀ (norm_nonneg _) (sum_nonneg fun _ _ => norm_nonneg _)).mpr
    (norm_sum_le (s ×ˢ t) (fun z => F z.1 z.2))
  have hc := sq_sum_le_card_mul_sum_sq (s := s ×ˢ t) (f := fun z => ‖F z.1 z.2‖)
  have hs : (∑ z ∈ s ×ˢ t, ‖F z.1 z.2‖^2) ≤ (s ×ˢ t).card*E := by
    calc
      _ ≤ ∑ _z ∈ s ×ˢ t, E := sum_le_sum fun z hz =>
        hF z.1 (mem_product.mp hz).1 z.2 (mem_product.mp hz).2
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  calc
    _ ≤ ((s ×ˢ t).card : ℝ)*((s ×ˢ t).card*E) := hn.trans
      (hc.trans (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)))
    _ = _ := by rw [card_product, Nat.cast_mul]; ring

end
end ArtinMatthews

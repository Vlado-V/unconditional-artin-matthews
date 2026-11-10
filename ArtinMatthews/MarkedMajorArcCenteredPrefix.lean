module

public import ArtinMatthews.MarkedMajorArcCenteredPartialSummation
public import ArtinMatthews.MarkedMajorArcLowMangoldt
public import ArtinMatthews.MarkedMajorArcLowParameters
public import ArtinMatthews.MarkedMajorArcRoughLow
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
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

/-! Actual cancellation of the principal linear terms in the centered
sharp arithmetic prefix. Both input distributions are proved locally. -/
namespace ArtinMatthews
open Finset Filter
open scoped Topology

 theorem marked_major_centered_prefix_low (a η τ P : ℝ)
    (ha : 0 ≤ a) (hη : 0 < η) (hτ : 0 < τ) (hP : 0 ≤ P) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ),
        (q:ℝ) ≤ L^a → Real.exp (τ*L) ≤ x → x ≤ Real.exp (η*L) →
        ‖∑ n ∈ Ioc 0 ⌊x⌋₊, markedCenteredMangoldt χ (Real.exp (L^(6/25:ℝ))) n‖ ≤
          K*x*L^(-P) := by
  classical
  obtain ⟨K,hK,hprime⟩ := marked_major_mangoldt_prefix_low a η τ P ha hη hτ hP
  refine ⟨K+2,by linarith,?_⟩
  filter_upwards [hprime,marked_major_rough_prefix_low a τ P 1 ha hτ hP (by norm_num),
    marked_polynomial_le_exponential_length 1 0 τ P hτ] with L hp hr hconst
  intro q _ χ x hq hlo hhi
  let W := Real.exp (L^(6/25:ℝ))
  let V := markedSieveEulerProduct W
  let ψ : ℂ := ∑ n ∈ Ioc 0 ⌊x⌋₊, χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ)
  let R := roughCharacterIocSum χ (Nat.primesLE ⌊W⌋₊) 0 ⌊x⌋₊
  have hxp : 0 < x := (Real.exp_pos _).trans_le hlo
  have hψ : ‖ψ-(if χ=1 then (x:ℂ) else 0)‖ ≤ K*x*L^(-P) := hp q χ x hq hlo hhi
  have hR : ‖(V:ℂ)⁻¹*R-(if χ=1 then ((⌊x⌋₊:ℝ):ℂ) else 0)‖ ≤ x*L^(-P) := by
    simpa only [one_mul] using hr q χ x hq hlo
  have hround : ‖(if χ=1 then ((x-(⌊x⌋₊:ℝ):ℝ):ℂ) else 0)‖ ≤ 1 := by
    split_ifs
    · rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (Nat.floor_le hxp.le))]
      linarith [Nat.lt_floor_add_one x]
    · simp
  have hs : (∑ n ∈ Ioc 0 ⌊x⌋₊, markedCenteredMangoldt χ W n) = ψ-(V:ℂ)⁻¹*R := by
    dsimp [ψ,R,roughCharacterIocSum]
    rw [mul_sum,← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    dsimp [markedCenteredMangoldt,V]
    ring
  have he : (∑ n ∈ Ioc 0 ⌊x⌋₊, markedCenteredMangoldt χ W n) =
      (ψ-(if χ=1 then (x:ℂ) else 0))-
        ((V:ℂ)⁻¹*R-(if χ=1 then ((⌊x⌋₊:ℝ):ℂ) else 0))+
        (if χ=1 then ((x-(⌊x⌋₊:ℝ):ℝ):ℂ) else 0) := by
    rw [hs]
    split_ifs <;> push_cast <;> ring
  have h1 : 1 ≤ x*L^(-P) := by simpa using hconst x hlo
  rw [he]
  calc
    _ ≤ (‖ψ-(if χ=1 then (x:ℂ) else 0)‖+
      ‖(V:ℂ)⁻¹*R-(if χ=1 then ((⌊x⌋₊:ℝ):ℂ) else 0)‖)+
      ‖(if χ=1 then ((x-(⌊x⌋₊:ℝ):ℝ):ℂ) else 0)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (K*x*L^(-P)+x*L^(-P))+x*L^(-P) :=
      add_le_add (add_le_add hψ hR) (hround.trans h1)
    _ = _ := by ring

end ArtinMatthews

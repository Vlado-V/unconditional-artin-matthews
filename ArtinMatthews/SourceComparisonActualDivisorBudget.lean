module

public import ArtinMatthews.SourceComparisonActualBands
public import ArtinMatthews.SourceComparisonLowTime
public import ArtinMatthews.SourceComparisonMarkBounds
public import ArtinMatthews.SourceComparisonDivisorErrorSaving
public import ArtinMatthews.SourceComparisonGroupBudget
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! The actual depth and prime scales give the fixed logarithmic and
subpower envelopes in the marked-divisor model. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators Topology
noncomputable section

universe u v
variable {J : Type u} [Fintype J]

theorem sourceComparisonActualDivisorBudget_eventually (e : J → ℝ)
    (he : ∀ j, (1/10 : ℝ) < e j ∧ e j < 1/5) (heinj : Function.Injective e)
    (m : ℕ) {r : ℝ} (hr : 0 < r) (hr₁ : r < 1) (A : ℝ) :
    ∃ D E K : ℝ, 0 ≤ D ∧ 0 ≤ E ∧ 0 ≤ K ∧
      ∀ᶠ x : ℝ in atTop, ∀ {G : Type v} [Fintype G] (i : G ↪ GiantCandidateGroupIndex x)
        (t : G → ℕ), (∀ g, t g ≤ m) →
        let P := sourceComparisonActualBands e x i
        let u := Sum.elim (fun _ => 1) t
        let L := Real.log x
        let j := ⌊L ^ (1/100:ℝ)⌋₊
        let Z := Real.exp (L ^ (46/100:ℝ))
        (∑ p ∈ univ.biUnion P, 1 / (p : ℝ)) ≤ E * Real.log L ∧
        sourceComparisonMarkFactorialMass P u ≤ L ^ D ∧
        sourceComparisonMarkDampedMass P u r ≤ L ^ D ∧
        sourceComparisonDivisorErrorBudget P u j ≤ L ^ (-A) ∧
        Real.exp (∑ p ∈ univ.biUnion P, 1 / (p : ℝ)) * Z ^ ((∑ g, u g) + j) ≤
          Real.exp (K * L ^ (47/100:ℝ)) := by
  let E := (Fintype.card J : ℝ) + giantCandidateGroupLogRate
  have hE : 0 ≤ E := by unfold E giantCandidateGroupLogRate; positivity
  let K := E + (m + 1 : ℕ) * E + 1
  have hK : 0 ≤ K := by unfold K; positivity
  have hv : 0 < Real.log 2 / 2 := by positivity
  obtain ⟨D, hD, hMass⟩ := sourceComparisonMarkMass_log_bounds.{max u v} (m + 1) hv hr hr₁ hE
  refine ⟨D, E, K, hD, hE, hK, ?_⟩
  have hsmall := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/100)).bound
    (zero_lt_one : (0:ℝ) < 1)
  filter_upwards [sourceComparisonActualBands_geometry_eventually.{u, v} e he heinj,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    Real.tendsto_log_atTop.eventually (sourceComparison_divisorErrorBudget_log_saving D E A),
    Real.tendsto_log_atTop.eventually hsmall] with x hG hL hsave hsmall
  intro G _ i t ht
  let P := sourceComparisonActualBands e x i
  let u : J ⊕ G → ℕ := Sum.elim (fun _ => 1) t
  let L := Real.log x
  let j := ⌊L ^ (1/100:ℝ)⌋₊
  let Z := Real.exp (L ^ (46/100:ℝ))
  let V := ∑ p ∈ univ.biUnion P, 1 / (p : ℝ)
  let N := Fintype.card (J ⊕ G)
  have hL₀ : 0 < L := zero_lt_one.trans_le hL
  obtain ⟨hdis, hV, _, hN⟩ := hG i
  have hu (g : J ⊕ G) : u g ≤ m + 1 := by
    rcases g with g | g
    · exact Nat.le_add_left 1 m
    · exact (ht g).trans (Nat.le_succ m)
  have hV' : V ≤ E * Real.log L :=
    (sourceComparisonMarkUnionMass_le_card P hdis (fun g => (hV g).2.le)).trans hN
  obtain ⟨hA, hB⟩ := hMass P u hu (fun g => (hV g).1.le) L hL hN
  have hA₀ := sourceComparisonMarkFactorialMass_nonneg P u (fun g => hv.trans (hV g).1)
  refine ⟨hV', hA, hB, hsave _ V hA₀ hA hV', ?_⟩
  have hsmall' : Real.log L ≤ L ^ (1/100:ℝ) := by
    change ‖Real.log L‖ ≤ 1 * ‖L ^ (1/100:ℝ)‖ at hsmall
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hL₀.le _), one_mul] at hsmall
    exact (le_abs_self _).trans hsmall
  have hj : (j : ℝ) ≤ L ^ (1/100:ℝ) := Nat.floor_le (Real.rpow_nonneg hL₀.le _)
  have hN' : (N : ℝ) ≤ E * L ^ (1/100:ℝ) :=
    hN.trans (mul_le_mul_of_nonneg_left hsmall' hE)
  have hS : (↑(∑ g, u g) : ℝ) ≤ (m + 1 : ℕ) * (N : ℝ) := by
    have h := sum_le_sum (s := (univ : Finset (J ⊕ G))) (fun g _ => hu g)
    have h' : (∑ g, u g) ≤ (m+1) * N := by simpa [N, Nat.mul_comm] using h
    exact_mod_cast h'
  have hsum : (((∑ g, u g) + j : ℕ) : ℝ) ≤ ((m + 1 : ℕ) * E + 1) * L ^ (1/100:ℝ) := by
    rw [Nat.cast_add]
    have hS' := hS.trans (mul_le_mul_of_nonneg_left hN' (Nat.cast_nonneg (m+1)))
    exact (add_le_add hS' hj).trans_eq (by ring)
  have hV'' : V ≤ E * L ^ (47/100:ℝ) :=
    hV'.trans (mul_le_mul_of_nonneg_left (hsmall'.trans
      (Real.rpow_le_rpow_of_exponent_le hL (by norm_num))) hE)
  have hsum' := mul_le_mul_of_nonneg_right hsum (Real.rpow_nonneg hL₀.le (46/100:ℝ))
  have hp : L ^ (1/100:ℝ) * L ^ (46/100:ℝ) = L ^ (47/100:ℝ) := by
    rw [← Real.rpow_add hL₀]
    norm_num
  rw [mul_assoc, hp] at hsum'
  change Real.exp V * Z ^ ((∑ g, u g) + j) ≤ _
  rw [show Z = Real.exp (L ^ (46/100:ℝ)) from rfl, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  change V + (((∑ g, u g) + j : ℕ) : ℝ) * L ^ (46/100:ℝ) ≤ K * L ^ (47/100:ℝ)
  unfold K
  exact (add_le_add hV'' hsum').trans_eq (by ring)

end
end ArtinMatthews

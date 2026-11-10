module

public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Order.Real
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite orbit multiplicities on a separated invariant slice. -/
namespace ArtinMatthews
open Set
open scoped ENNReal Pointwise Classical
noncomputable section

variable {Γ X : Type*} [Group Γ] [MulAction Γ X]

theorem sourceFiniteSlice_hit_iff (H : Subgroup Γ) (E : Set X)
    (hstable : ∀ h : H, ∀ x ∈ E, (h : Γ) • x ∈ E)
    (hsep : ∀ γ : Γ, ∀ x ∈ E, γ • x ∈ E → γ ∈ H)
    {x : X} (hx : x ∈ E) (γ : Γ) : γ • x ∈ E ↔ γ ∈ H := by
  exact ⟨hsep γ x hx, fun hγ => hstable ⟨γ, hγ⟩ x hx⟩

theorem sourceFiniteSlice_indicator_tsum (H : Subgroup Γ) [Finite H] (E : Set X)
    (hstable : ∀ h : H, ∀ x ∈ E, (h : Γ) • x ∈ E)
    (hsep : ∀ γ : Γ, ∀ x ∈ E, γ • x ∈ E → γ ∈ H) (x : X) :
    (∑' γ : Γ, E.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x)) =
      if (Quotient.mk (MulAction.orbitRel Γ X) x) ∈
        (Quotient.mk (MulAction.orbitRel Γ X) '' E) then (Nat.card H : ℝ≥0∞) else 0 := by
  classical
  by_cases hx : (Quotient.mk (MulAction.orbitRel Γ X) x) ∈
      (Quotient.mk (MulAction.orbitRel Γ X) '' E)
  · rw [ite_eq_left hx]
    obtain ⟨y, hy, hxy⟩ := hx
    obtain ⟨γ₀, hγ₀⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact hxy)
    have hhit : γ₀ • x ∈ E := by simpa only [hγ₀] using hy
    calc
      (∑' γ : Γ, E.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x)) =
          ∑' γ : Γ, E.indicator (fun _ => (1 : ℝ≥0∞)) ((γ * γ₀) • x) :=
        ((Equiv.mulRight γ₀).tsum_eq _).symm
      _ = ∑' γ : Γ, (H : Set Γ).indicator (fun _ => (1 : ℝ≥0∞)) γ := by
        apply tsum_congr
        intro γ
        rw [mul_smul]
        have hh := sourceFiniteSlice_hit_iff H E hstable hsep hhit γ
        change (if γ • (γ₀ • x) ∈ E then (1 : ℝ≥0∞) else 0) =
          if γ ∈ H then 1 else 0
        simp only [hh]
      _ = ∑' _ : H, (1 : ℝ≥0∞) := (tsum_subtype (H : Set Γ) _).symm
      _ = (Nat.card H : ℝ≥0∞) := by
        let : Fintype H := Fintype.ofFinite H
        simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          mul_one, Nat.card_eq_fintype_card]
  · rw [ite_eq_right hx]
    have hz (γ : Γ) : E.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x) = 0 := by
      have hh : γ • x ∉ E := by
        intro hγ
        apply hx
        refine ⟨γ • x, hγ, ?_⟩
        apply Quotient.sound
        exact MulAction.mem_orbit_iff.mpr ⟨γ, rfl⟩
      exact Set.indicator_of_notMem hh _
    simp only [hz, tsum_zero]

end
end ArtinMatthews

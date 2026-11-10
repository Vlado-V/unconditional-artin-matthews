module

public import ArtinMatthews.MarkedMinorArcRawEdgeChargedAction
public import ArtinMatthews.MarkedMinorArcRawEdgeSymmetryCoefficients
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Exact whole-choice multipliers for arbitrary independent promotion
and storage charges. The fresh atoms and indexed caps are unchanged. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

def markedRawEdgeChoiceChargeMultiplier {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (V : J → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (c : MarkedRawEdgeChoice hZ s) : ℂ :=
  ∏ j, (if (c.promotions j).isSome then δ j*(V j:ℂ) else 1)*
    (if c.store j then γ j else 1)

theorem markedRawEdgeChoiceChargeMultiplier_eq {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (V : J → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (c : MarkedRawEdgeChoice hZ s) :
    markedRawEdgeChoiceChargeMultiplier V δ γ hZ s c =
      markedRawEdgeChoiceCharge (fun j => δ j*(V j:ℂ)) γ hZ s c := by
  unfold markedRawEdgeChoiceChargeMultiplier markedRawEdgeChoiceCharge
  apply Finset.prod_congr rfl
  intro j _
  by_cases hp : (c.promotions j).isSome <;> by_cases hs : c.store j <;> simp [hp,hs]

theorem markedRawEdgeChoiceChargeMultiplier_one {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (c : MarkedRawEdgeChoice hZ s) :
    markedRawEdgeChoiceChargeMultiplier (fun _ => 1) δ γ hZ s c =
      markedRawEdgeChoiceCharge δ γ hZ s c := by
  rw [markedRawEdgeChoiceChargeMultiplier_eq]
  simp only [Complex.ofReal_one,mul_one]

theorem markedRawEdgeChoiceCharge_norm_le {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (δ γ : J → ℂ) {D G : ℝ}
    (hD : 1 ≤ D) (hG : 1 ≤ G) (hδ : ∀ j,‖δ j‖ ≤ D) (hγ : ∀ j,‖γ j‖ ≤ G)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (c : MarkedRawEdgeChoice hZ s) :
    ‖markedRawEdgeChoiceCharge δ γ hZ s c‖ ≤ (D*G)^(Fintype.card J) := by
  unfold markedRawEdgeChoiceCharge
  rw [norm_prod]
  calc
    _ ≤ ∏ _j : J,D*G := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro j _
      rw [norm_mul]
      have hd : ‖δ j^(if (c.promotions j).isSome then 1 else 0)‖ ≤ D := by
        by_cases hp : (c.promotions j).isSome
        · simpa only [hp,ite_true,pow_one] using hδ j
        · simpa only [hp,Bool.false_eq_true,ite_false,pow_zero,norm_one] using hD
      have hg : ‖γ j^(if c.store j then 1 else 0)‖ ≤ G := by
        by_cases hs : c.store j
        · simpa only [hs,ite_true,pow_one] using hγ j
        · simpa only [hs,Bool.false_eq_true,ite_false,pow_zero,norm_one] using hG
      exact mul_le_mul hd hg (norm_nonneg _) (zero_le_one.trans hD)
    _ = _ := by simp

/-- Every promoted coordinate cancels the original V^-1 factor against
the multiplier's V. No prime atom is divided or normalized. -/
theorem markedRawEdgeChoiceCharge_factor {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    (V : J → ℝ) (δ γ : J → ℂ) (hV : ∀ j,V j ≠ 0)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (c : MarkedRawEdgeChoice hZ s) :
    markedRawEdgeChoiceCharge δ γ hZ s c*markedRawEdgeChoiceFreshMass ν hZ s c =
      (markedRawEdgeChoicePrimeMass ν V hZ s c:ℂ)*
        markedRawEdgeChoiceChargeMultiplier V δ γ hZ s c := by
  unfold markedRawEdgeChoiceCharge markedRawEdgeChoiceFreshMass markedRawEdgeChoiceChargeMultiplier
  simp only [markedRawEdgeChoicePrimeMass_eq_targetLast,Complex.ofReal_prod]
  rw [← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  have hv : (V j:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hV j)
  by_cases hp : (c.promotions j).isSome <;>
    by_cases hs : c.store j <;> simp [hp,hs,hv,mul_comm,mul_left_comm,mul_assoc]

theorem markedRawEdgeChoiceChargeMultiplier_norm_le {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (V : J → ℝ) (δ γ : J → ℂ) {D G C : ℝ}
    (hD : 1 ≤ D) (hG : 1 ≤ G) (hC : 1 ≤ C)
    (hδ : ∀ j,‖δ j‖ ≤ D) (hγ : ∀ j,‖γ j‖ ≤ G) (hV : ∀ j,|V j| ≤ C)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (c : MarkedRawEdgeChoice hZ s) :
    ‖markedRawEdgeChoiceChargeMultiplier V δ γ hZ s c‖ ≤ (D*C*G)^(Fintype.card J) := by
  rw [markedRawEdgeChoiceChargeMultiplier_eq]
  have hDC : 1 ≤ D*C := by
    simpa only [one_mul] using mul_le_mul hD hC zero_le_one (zero_le_one.trans hD)
  apply markedRawEdgeChoiceCharge_norm_le _ _ hDC hG _ hγ
  intro j
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul (hδ j) (hV j) (abs_nonneg _) (zero_le_one.trans hD)

end
end ArtinMatthews

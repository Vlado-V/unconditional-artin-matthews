module

public import ArtinMatthews.MarkedMinorArcRawSlotAverage
public import ArtinMatthews.MarkedMinorArcRawMemoryAmbient
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

/-! Exact transpose and invariance of the original uniform slot average.
Pending memory and its factorial weight are untouched by every slot action. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

theorem markedRawSlotEquiv_comp_apply {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (σ τ : (j : J) → Equiv.Perm (Fin M)) (s : MarkedRawState P M B Z) :
    markedRawSlotEquiv τ (markedRawSlotEquiv σ s) = markedRawSlotEquiv (σ * τ) s := rfl

theorem markedRawSlotEquiv_pairing {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} (σ : (j : J) → Equiv.Perm (Fin M))
    (f g : MarkedRawState P M B Z → ℂ) :
    (∑ s, (markedRawStateMass ν s : ℂ) * g s * f (markedRawSlotEquiv σ s)) =
      ∑ s, (markedRawStateMass ν s : ℂ) * f s * g (markedRawSlotEquiv σ⁻¹ s) := by
  classical
  rw [← (markedRawSlotEquiv σ).symm.sum_comp
    (fun s => (markedRawStateMass ν s : ℂ) * g s * f (markedRawSlotEquiv σ s))]
  apply Finset.sum_congr rfl
  intro s _
  have hi : (markedRawSlotEquiv σ).symm s = markedRawSlotEquiv σ⁻¹ s := rfl
  rw [Equiv.apply_symm_apply, hi, markedRawStateMass_slots]
  ring

theorem markedRawSlotAverage_transpose {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} (f g : MarkedRawState P M B Z → ℂ) :
    (∑ s, (markedRawStateMass ν s : ℂ) * g s * markedRawSlotAverage f s) =
      ∑ s, (markedRawStateMass ν s : ℂ) * f s * markedRawSlotAverage g s := by
  classical
  let C : ℂ := (Fintype.card ((j : J) → Equiv.Perm (Fin M)) : ℂ)⁻¹
  calc
    _ = C * ∑ σ : (j : J) → Equiv.Perm (Fin M),
        ∑ s, (markedRawStateMass ν s : ℂ) * g s * f (markedRawSlotEquiv σ s) := by
      simp only [markedRawSlotAverage, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.sum_congr rfl
      intro s _
      dsimp only [C]
      ring
    _ = C * ∑ σ : (j : J) → Equiv.Perm (Fin M),
        ∑ s, (markedRawStateMass ν s : ℂ) * f s * g (markedRawSlotEquiv σ⁻¹ s) := by
      apply congrArg (fun u : ℂ => C * u)
      exact Finset.sum_congr rfl (fun σ _ => markedRawSlotEquiv_pairing ν σ f g)
    _ = C * ∑ σ : (j : J) → Equiv.Perm (Fin M),
        ∑ s, (markedRawStateMass ν s : ℂ) * f s * g (markedRawSlotEquiv σ s) := by
      congr 1
      exact Equiv.sum_comp (Equiv.inv ((j : J) → Equiv.Perm (Fin M)))
        (fun σ => ∑ s, (markedRawStateMass ν s : ℂ) * f s * g (markedRawSlotEquiv σ s))
    _ = _ := by
      simp only [markedRawSlotAverage, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.sum_congr rfl
      intro s _
      dsimp only [C]
      ring

theorem markedRawSlotAverage_slots {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (f : MarkedRawState P M B Z → ℂ) (σ : (j : J) → Equiv.Perm (Fin M))
    (s : MarkedRawState P M B Z) :
    markedRawSlotAverage f (markedRawSlotEquiv σ s) = markedRawSlotAverage f s := by
  unfold markedRawSlotAverage
  apply congrArg (fun u : ℂ => (Fintype.card ((j : J) → Equiv.Perm (Fin M)) : ℂ)⁻¹ * u)
  simp only [markedRawSlotEquiv_comp_apply]
  exact Equiv.sum_comp (Equiv.mulLeft σ) (fun τ => f (markedRawSlotEquiv τ s))

theorem markedRawSlotAverage_symmetric {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (f : MarkedRawState P M B Z → ℂ)
    (hf : ∀ z a, MarkedRawMemorySymmetric (fun m => f (z,(a,m))))
    (z : Z) (a : MarkedRawActive P M) :
    MarkedRawMemorySymmetric (fun m => markedRawSlotAverage f (z,(a,m))) := by
  classical
  intro m τ
  unfold markedRawSlotAverage
  apply congrArg (fun u : ℂ => (Fintype.card ((j : J) → Equiv.Perm (Fin M)) : ℂ)⁻¹ * u)
  apply Finset.sum_congr rfl
  intro σ _
  exact hf z (markedRawActiveSlotEquiv σ a) m τ

theorem markedRawSlotAverage_eq_of_invariant {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (f : MarkedRawState P M B Z → ℂ)
    (hf : ∀ σ s, f (markedRawSlotEquiv σ s) = f s) : markedRawSlotAverage f = f := by
  classical
  funext s
  have hN : (Fintype.card ((j : J) → Equiv.Perm (Fin M)) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [markedRawSlotAverage, hf, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hN, one_mul]

def markedRawSlotAverageReal {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (f : MarkedRawState P M B Z → ℝ) (s : MarkedRawState P M B Z) : ℝ :=
  (Fintype.card ((j : J) → Equiv.Perm (Fin M)) : ℝ)⁻¹ *
    ∑ σ : (j : J) → Equiv.Perm (Fin M), f (markedRawSlotEquiv σ s)

theorem markedRawSlotAverageReal_complex {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (f : MarkedRawState P M B Z → ℝ) (s : MarkedRawState P M B Z) :
    (markedRawSlotAverageReal f s : ℂ) = markedRawSlotAverage (fun t => (f t : ℂ)) s := by
  simp only [markedRawSlotAverageReal,markedRawSlotAverage,Complex.ofReal_mul,
    Complex.ofReal_inv,Complex.ofReal_sum,Complex.ofReal_natCast]

theorem markedRawSlotAverage_weighted_invariant {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} (F R : MarkedRawState P M B Z → ℝ)
    (hF : ∀ σ s, F (markedRawSlotEquiv σ s) = F s) :
    (∑ s, markedRawStateMass ν s * F s * R s) =
      ∑ s, markedRawStateMass ν s * F s * markedRawSlotAverageReal R s := by
  apply Complex.ofReal_injective
  have hfix := markedRawSlotAverage_eq_of_invariant (fun s => (F s : ℂ))
    (fun σ s => congrArg (fun x : ℝ => (x : ℂ)) (hF σ s))
  have h := markedRawSlotAverage_transpose ν (fun s => (R s : ℂ)) (fun s => (F s : ℂ))
  rw [hfix] at h
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, markedRawSlotAverageReal_complex]
  rw [h]
  apply Finset.sum_congr rfl
  intro s _
  ring

end
end ArtinMatthews

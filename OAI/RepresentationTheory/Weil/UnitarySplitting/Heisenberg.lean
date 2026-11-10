module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.UnitarySplitting.Oscillator
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! # Heisenberg -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.Heisenberg.Construction

noncomputable section

/-! Weyl commutation relations for the actual Schrödinger operators.
These identities are independent of any metaplectic lift or splitting. -/

open scoped BigOperators

variable {F : Type} [NormedField F] [CharZero F] {d : ℕ}

omit [CharZero F] in
theorem standardSymplecticPairing_neg_right (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) :
    Oscillator.Construction.standardSymplecticPairing d v (-v) = 0 := by
  unfold Oscillator.Construction.standardSymplecticPairing
  apply Finset.sum_eq_zero
  intro i hi
  simp only [Pi.neg_apply]
  ring

omit [CharZero F] in
theorem standardSymplecticPairing_neg_left (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) :
    Oscillator.Construction.standardSymplecticPairing d (-v) v = 0 := by
  unfold Oscillator.Construction.standardSymplecticPairing
  apply Finset.sum_eq_zero
  intro i hi
  simp only [Pi.neg_apply]
  ring

omit [CharZero F] in
theorem heisenbergFunction_zero (ψ : AddChar F ℂ) (f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ) :
    Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (0 : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) f = f := by
  funext x
  simp [Local.FunctionsMetaplectic.Construction.heisenbergFunction]

theorem heisenbergFunction_composition (ψ : AddChar F ℂ)
    (v w : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ) :
    Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v (Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ w f) =
      ψ (Oscillator.Construction.standardSymplecticPairing d v w / 2) • Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (v + w) f := by
  funext x
  have hphase :
      (∑ i, v (Sum.inr i) * (x i - v (Sum.inl i) / 2)) +
          (∑ i, w (Sum.inr i) * (x i - v (Sum.inl i) - w (Sum.inl i) / 2)) =
        Oscillator.Construction.standardSymplecticPairing d v w / 2 +
          ∑ i, (v (Sum.inr i) + w (Sum.inr i)) *
            (x i - (v (Sum.inl i) + w (Sum.inl i)) / 2) := by
    unfold Oscillator.Construction.standardSymplecticPairing
    rw [Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp
    ring
  have harg : (fun i => x i - v (Sum.inl i) - w (Sum.inl i)) =
      (fun i => x i - (v (Sum.inl i) + w (Sum.inl i))) := by
    funext i
    ring
  change ψ _ * (ψ _ * f _) = ψ _ * (ψ _ * f _)
  rw [← mul_assoc, ← ψ.map_add_eq_mul, ← mul_assoc, ← ψ.map_add_eq_mul,
    hphase, harg]
  simp only [Pi.add_apply]

theorem heisenbergFunction_neg_left_cancel (ψ : AddChar F ℂ)
    (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ) :
    Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (-v) (Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f) = f := by
  rw [heisenbergFunction_composition, standardSymplecticPairing_neg_left]
  simp [heisenbergFunction_zero]

theorem heisenbergFunction_neg_right_cancel (ψ : AddChar F ℂ)
    (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ) :
    Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v (Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (-v) f) = f := by
  rw [heisenbergFunction_composition, standardSymplecticPairing_neg_right]
  simp [heisenbergFunction_zero]

/-- Weyl operators are genuine complex-linear automorphisms on functions.
Restriction to the Bruhat space is a separate analytic assertion. -/
def heisenbergLinearEquiv (ψ : AddChar F ℂ) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) :
    (Local.FunctionsMetaplectic.Construction.Position F d → ℂ) ≃ₗ[ℂ] (Local.FunctionsMetaplectic.Construction.Position F d → ℂ) where
  toFun := Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v
  invFun := Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (-v)
  left_inv := heisenbergFunction_neg_left_cancel ψ v
  right_inv := heisenbergFunction_neg_right_cancel ψ v
  map_add' f g := by
    funext x
    exact mul_add _ _ _
  map_smul' a f := by
    exact Oscillator.Construction.heisenbergFunction_smul d ψ v a f

theorem heisenbergFunction_ne_zero (ψ : AddChar F ℂ)
    (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ) (hf : f ≠ 0) :
    Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f ≠ 0 := by
  intro h
  apply hf
  apply (heisenbergLinearEquiv ψ v).injective
  rw [map_zero]
  exact h

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.Heisenberg.Construction

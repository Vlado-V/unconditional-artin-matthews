module

public import ArtinMatthews.MarkedMinorArcDirtyMajorChoiceWeighted
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

/-! Actual major comparison source symmetrization preserves the explicit
finite row bound, with only the true v0^K memory-weight cost. -/
noncomputable section
namespace ArtinMatthews
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false in
theorem markedDirtyMajorSymWeightedRow_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (hV : ∀ j, 0 < V j) {C : ℝ} (hC : 1 ≤ C) (hVC : ∀ j, (V j)⁻¹ ≤ C)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (η ψ : ℝ → ℂ)
    (r d₀ Y Q ρ v₀ : ℝ) {c Bτ K H W pmin : ℝ}
    (hY : 1 ≤ Y) (hQ : 0 ≤ Q) (hc : 0 < c) (hBτ : 0 ≤ Bτ) (hpmin : 0 < pmin)
    (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (hv₀ : 1 ≤ v₀) (hH : 0 ≤ H) (hW : 0 ≤ W)
    (hη : ∀ t, ‖η t‖ ≤ H) (hψ : ∀ t, ‖ψ t‖ ≤ W) (hsupp : Function.support ψ ⊆ Set.Icc (-K) K)
    (w : Z → ℤ × ℤ) (hw : ∀ z, markedMinorIntegerDet z.1 (w z)=1)
    (hτ : ∀ z ∈ Z, c ≤ |markedMinorIntegerTau r z| ∧ |markedMinorIntegerTau r z| ≤ Bτ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (hχ : ∀ s, ‖χ s‖ ≤ 1)
    (s : MarkedRawState P (pads+1) B Z) (I : Finset J) (jstar : I)
    (hp : ∀ k : Fin (s.2.2.1.1 jstar.1:ℕ), pmin ≤ ((s.2.2.2 jstar.1 k).1.1:ℕ)) :
    markedDirtyMajorSymWeightedRow ν V hZ η ψ r d₀ Y Q ρ v₀ w χ s I ≤
      v₀^(Fintype.card J)*1200*(max 1 (max (Bτ/c) K))^2*C^(Fintype.card J)*H^2*W*(2:ℝ)^(Fintype.card J)*
        (B+1:ℝ)^(Fintype.card J)*
        (∑ fresh : (j : ↥(Finset.univ \ I)) → ↥(P j.1),
          finiteProductMass (fun j : ↥(Finset.univ \ I) => ν j.1) fresh)*
        Q^3*(1/pmin+Y^(-1/10:ℝ)) := by
  classical
  let R : ℝ := 1200*(max 1 (max (Bτ/c) K))^2*C^(Fintype.card J)*H^2*W*(2:ℝ)^(Fintype.card J)*
    (B+1:ℝ)^(Fintype.card J)*
    (∑ fresh : (j : ↥(Finset.univ \ I)) → ↥(P j.1), finiteProductMass (fun j : ↥(Finset.univ \ I) => ν j.1) fresh)*
    Q^3*(1/pmin+Y^(-1/10:ℝ))
  have hpσ (σ : J → Equiv.Perm (Fin (pads+1))) :
      markedDirtyMajorChoiceWeightedRow ν V hZ η ψ r d₀ Y Q ρ v₀ w χ (markedRawSlotEquiv σ s) I ≤
        v₀^(Fintype.card J)*R := by
    apply (markedDirtyMajorChoiceWeightedRow_le ν V hν hV hZ η ψ r d₀ Y Q ρ v₀ hv₀ w χ
      (markedRawSlotEquiv σ s) I).trans
    exact mul_le_mul_of_nonneg_left (markedDirtyMajorChoiceRow_le ν V hν hV hC hVC hZ η ψ r d₀ Y Q ρ
      hY hQ hc hBτ hpmin hρ₀ hρ₁ hH hW hη hψ hsupp w hw hτ χ hχ (markedRawSlotEquiv σ s) I jstar hp)
      (pow_nonneg (by linarith) _)
  unfold markedDirtyMajorSymWeightedRow
  calc
    _ ≤ ∑ σ : J → Equiv.Perm (Fin (pads+1)), markedDirtySourceSlotWeight pads σ*(v₀^(Fintype.card J)*R) :=
      Finset.sum_le_sum (fun σ _ => mul_le_mul_of_nonneg_left (hpσ σ) (by unfold markedDirtySourceSlotWeight; positivity))
    _ = (∑ σ : J → Equiv.Perm (Fin (pads+1)), markedDirtySourceSlotWeight pads σ)*(v₀^(Fintype.card J)*R) :=
      (Finset.sum_mul _ _ _).symm
    _ = v₀^(Fintype.card J)*R := by rw [markedDirtySourceSlotWeight_total,one_mul]
    _ = _ := by dsimp [R]; ring

end ArtinMatthews

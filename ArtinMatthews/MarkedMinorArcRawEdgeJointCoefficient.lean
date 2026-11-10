module

public import ArtinMatthews.MarkedMinorArcRawEdgeAction
public import ArtinMatthews.MarkedMinorArcRawMemoryAmbient
public import ArtinMatthews.MarkedMinorArcRawGhostSymmetryBoundary
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

/-! The original edge coefficient as a joint function of its two actual
endpoint states.  This exact form separates the physical kernel from the
store/promote choice indexing without dropping a cutoff or damping factor. -/
namespace ArtinMatthews
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedRawEdgeJointCoefficient {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s t : MarkedRawState P (pads+1) B Z) : ℂ :=
  let sourceLast := ((markedRawActiveSplit pads) s.2.1).2
  let targetLast := ((markedRawActiveSplit pads) t.2.1).2
  let D := markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1
  let determinant := markedMinorIntegerDet s.1.1 t.1.1 / (D : ℤ)
  if d₀ ≤ (D : ℝ) ∧ (D : ℝ) < 2*d₀ then
    if (D : ℤ) ∣ markedMinorIntegerDet s.1.1 t.1.1 then
      if MarkedRawFullCrossBan s.2.1 targetLast then 0 else
        ((d₀/(D : ℝ) : ℝ) : ℂ) * markedRawEndpointFactor hZ ρ χ s *
          η ((markedRawLastProduct sourceLast : ℝ)/Y) *
          η ((markedRawLastProduct targetLast : ℝ)/Y) *
          ψ ((determinant : ℝ)/Y) *
          (∫ θ : AddCircle (1 : ℝ) in (markedMinorCircleMajor Q Y)ᶜ,
            fourier (determinant - (markedRawLastProduct sourceLast : ℤ) +
              (markedRawLastProduct targetLast : ℤ)) θ ∂AddCircle.haarAddCircle) *
          markedRawEndpointFactor hZ ρ χ t
    else 0 else 0

/-- The joint endpoint coefficient is the original literal coefficient,
including the exact target memory, both old-hit dampings and the full ban. -/
theorem markedRawEdgeChoiceCoefficient_eq_joint
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (c : MarkedRawEdgeChoice hZ s) :
    markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s c =
      markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ s
        (markedRawEdgeTargetState hZ s c) := by
  have hlast : ((markedRawActiveSplit pads)
      (markedRawEdgeTargetState hZ s c).2.1).2 =
      markedRawEdgeTargetLast s.2.2 c.promotions c.fresh := by
    change ((markedRawActiveSplit pads) ((markedRawActiveSplit pads).symm _)).2 = _
    rw [Equiv.apply_symm_apply]
  unfold markedRawEdgeChoiceCoefficient markedRawEdgeJointCoefficient
  dsimp only
  rw [hlast]
  split_ifs <;> try rfl
  rw [← markedRawEndpointFactor_damping hZ ρ χ s,
    ← markedRawEndpointFactor_damping hZ ρ χ (markedRawEdgeTargetState hZ s c)]
  ring

/-- Permuting source pending indices leaves every physical coefficient
unchanged, for independently symmetric endpoint tests. -/
theorem markedRawEdgeJointCoefficient_source_permute
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (hχ : ∀ z a, MarkedRawMemorySymmetric (fun m => χ (z, (a,m))))
    (z : Z) (a : MarkedRawActive P (pads+1)) (m : MarkedRawMemory P B)
    (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j : ℕ)))
    (t : MarkedRawState P (pads+1) B Z) :
    markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ
      (z, (a, markedRawMemoryPermute m σ)) t =
      markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ (z, (a,m)) t := by
  have he : markedRawEndpointFactor hZ ρ χ (z, (a, markedRawMemoryPermute m σ)) =
      markedRawEndpointFactor hZ ρ χ (z, (a,m)) :=
    markedRawEndpointFactor_symmetric hZ ρ χ hχ z a m σ
  unfold markedRawEdgeJointCoefficient
  dsimp only
  rw [he]

/-- Target pending indices can likewise be permuted independently. -/
theorem markedRawEdgeJointCoefficient_target_permute
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (hχ : ∀ z a, MarkedRawMemorySymmetric (fun m => χ (z, (a,m))))
    (s : MarkedRawState P (pads+1) B Z)
    (z : Z) (a : MarkedRawActive P (pads+1)) (m : MarkedRawMemory P B)
    (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j : ℕ))) :
    markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ
      s (z, (a, markedRawMemoryPermute m σ)) =
      markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ s (z, (a,m)) := by
  have he : markedRawEndpointFactor hZ ρ χ (z, (a, markedRawMemoryPermute m σ)) =
      markedRawEndpointFactor hZ ρ χ (z, (a,m)) :=
    markedRawEndpointFactor_symmetric hZ ρ χ hχ z a m σ
  unfold markedRawEdgeJointCoefficient
  dsimp only
  rw [he]

end
end ArtinMatthews

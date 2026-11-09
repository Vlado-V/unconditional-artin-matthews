module

public import ArtinMatthews.MarkedMinorArcRawEdgeAction
public import ArtinMatthews.MarkedMinorArcBanAdjoint


set_option backward.privateInPublic true
@[expose] public section

/-! Exact delta/major separation in the actual signed store/promote edge.
Only the delta branch forces the literal determinant equation. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators

/-- Literal raw edge coefficient for an arbitrary explicit detector. -/
noncomputable def markedRawEdgeChoiceDetectorCoefficient {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (η : ℝ → ℂ) (d₀ Y ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (detector : ℤ → ℤ → ℤ → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (choice : MarkedRawEdgeChoice hZ s) : ℂ := by
  classical
  let target := markedRawEdgeTargetState hZ s choice
  let lastSource := ((markedRawActiveSplit pads) s.2.1).2
  let lastTarget := markedRawEdgeTargetLast s.2.2 choice.promotions choice.fresh
  let D := markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1
  let t := markedMinorIntegerDet s.1.1 target.1.1/(D : ℤ)
  exact if d₀ ≤ (D : ℝ) ∧ (D : ℝ) < 2*d₀ then
    if (D : ℤ) ∣ markedMinorIntegerDet s.1.1 target.1.1 then
      if MarkedRawFullCrossBan s.2.1 lastTarget then 0 else
        ((d₀/(D : ℝ) : ℝ) : ℂ)*
          ((ρ^(markedRawPendingHits s.2.2 s.1.1 (hZ _ s.1.2)) : ℝ) : ℂ)*
          markedRawEndpointFactor hZ 1 χ s*
          η ((markedRawLastProduct lastSource : ℝ)/Y)*η ((markedRawLastProduct lastTarget : ℝ)/Y)*
          detector (markedRawLastProduct lastSource) (markedRawLastProduct lastTarget) t*
          ((ρ^(markedRawPendingHits target.2.2 target.1.1 (hZ _ target.1.2)) : ℝ) : ℂ)*
          markedRawEndpointFactor hZ 1 χ target
    else 0 else 0

noncomputable def markedRawEdgeDeltaDetector (ψ : ℝ → ℂ) (Y : ℝ) (b a t : ℤ) : ℂ :=
  ψ ((t : ℝ)/Y)*(if t=b-a then 1 else 0)

noncomputable def markedRawEdgeMajorDetector (ψ : ℝ → ℂ) (Q Y : ℝ) (b a t : ℤ) : ℂ :=
  ψ ((t : ℝ)/Y)*markedBanMajorKernel Q Y (t-b+a)

/-- The literal full minor coefficient is the actual delta-minus-major
detector with all store/promote choices and physical factors unchanged. -/
theorem markedRawEdgeChoiceCoefficient_detector {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (choice : MarkedRawEdgeChoice hZ s) :
    markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s choice=
      markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ (markedBanEdgeKernel ψ Q Y) s choice := by
  classical
  unfold markedRawEdgeChoiceCoefficient markedRawEdgeChoiceDetectorCoefficient
  dsimp only
  split_ifs <;> try rfl
  rw [← markedBan_edge_minor_identity]
  ring

/-- Finite detector subtraction commutes with every literal raw edge factor. -/
theorem markedRawEdgeChoiceDetectorCoefficient_sub {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (η : ℝ → ℂ) (d₀ Y ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (first second : ℤ → ℤ → ℤ → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (choice : MarkedRawEdgeChoice hZ s) :
    markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ (first-second) s choice=
      markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ first s choice-
      markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ second s choice := by
  classical
  unfold markedRawEdgeChoiceDetectorCoefficient
  dsimp only [Pi.sub_apply]
  split_ifs <;> ring

/-- Actual full signed edge coefficient has the exact two detector branches;
no major branch is silently assigned the delta determinant support. -/
theorem markedRawEdgeChoiceCoefficient_delta_sub_major {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (choice : MarkedRawEdgeChoice hZ s) :
    markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s choice=
      markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ (markedRawEdgeDeltaDetector ψ Y) s choice-
      markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ (markedRawEdgeMajorDetector ψ Q Y) s choice := by
  rw [markedRawEdgeChoiceCoefficient_detector]
  have hd : markedBanEdgeKernel ψ Q Y=markedRawEdgeDeltaDetector ψ Y-markedRawEdgeMajorDetector ψ Q Y := by
    funext b a t
    dsimp only [markedBanEdgeKernel,markedRawEdgeDeltaDetector,markedRawEdgeMajorDetector,Pi.sub_apply]
    ring
  rw [hd,markedRawEdgeChoiceDetectorCoefficient_sub]

/-- The literal actual edge row for one of the two explicit detectors. -/
noncomputable def markedRawEdgeApplyDetector {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (η : ℝ → ℂ) (d₀ Y ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (detector : ℤ → ℤ → ℤ → ℂ)
    (f : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) : ℂ :=
  ∑ choice : MarkedRawEdgeChoice hZ s,
    (markedRawEdgeChoicePrimeMass ν V hZ s choice : ℂ)*
      markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ detector s choice*
      f (markedRawEdgeTargetState hZ s choice)

/-- Exact delta-minus-major partition of the full literal store/promote
row operation, with all actual choice multiplicities unchanged. -/
theorem markedRawEdgeApply_delta_sub_major {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (f : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) :
    markedRawEdgeApply ν V hZ ψ η d₀ Y Q ρ χ f s=
      markedRawEdgeApplyDetector ν V hZ η d₀ Y ρ χ (markedRawEdgeDeltaDetector ψ Y) f s-
      markedRawEdgeApplyDetector ν V hZ η d₀ Y ρ χ (markedRawEdgeMajorDetector ψ Q Y) f s := by
  unfold markedRawEdgeApply markedRawEdgeApplyDetector
  simp only [markedRawEdgeChoiceCoefficient_delta_sub_major,mul_sub,sub_mul,Finset.sum_sub_distrib]

end ArtinMatthews

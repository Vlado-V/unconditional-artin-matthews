module

public import ArtinMatthews.MarkedPhysicalCanonicalBad
public import ArtinMatthews.MarkedPhysicalCanonicalWeightSum


set_option backward.privateInPublic true
@[expose] public section

/-! Literal canonical summands and their absolute finite block. Naming
these expressions keeps the coefficient opaque during bound elaboration. -/
noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedPhysicalSourceBadTerm
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y Q : ℝ) (V : J → ℝ)
    (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (w : Z → ℤ × ℤ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (f g : MarkedPhysicalState (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) Z → ℂ)
    (u : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) (markedPadSlots x+1))
    [NeZero (markedPhysicalMarkingProduct u)] (hS : Squarefree (markedPhysicalMarkingProduct u))
    {A B C D : ℝ} (hA : 1 < A) (hC : 1 < C)
    (r : MarkedPhysicalCanonicalRoot (markedPhysicalMarkingProduct u) A B C D) (z : ℤ × ℤ) : ℂ :=
  if markedPhysicalEdgeRootLineEvent u hS r.1 z then
    markedPhysicalEdgePositionTerm (fun j => markedLogPowerBand (e j) x)
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V
      ⌊(Real.log x)^(1/100 : ℝ)⌋₊ Z hZ ψ η d₀ Y Q 1
      (markedPhysicalBadVector (MarkedPhysicalActualGood e x d₀ Y w) f) g
      (markedPhysicalEdgeSource u) (markedPhysicalEdgeTarget u)
      (markedPhysicalCanonicalRootPosition r) ((markedPhysicalCanonicalTargetEquiv hA hC r).symm z)
  else 0

def markedPhysicalSourceBadBlock
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y Q : ℝ) (V : J → ℝ)
    (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (w : Z → ℤ × ℤ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (f g : MarkedPhysicalState (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) Z → ℂ)
    (u : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) (markedPadSlots x+1))
    [NeZero (markedPhysicalMarkingProduct u)] (hS : Squarefree (markedPhysicalMarkingProduct u))
    {A B C D : ℝ} (hA : 1 < A) (hC : 1 < C) : ℝ :=
  ∑ r : MarkedPhysicalCanonicalRoot (markedPhysicalMarkingProduct u) A B C D,
    ∑ z ∈ markedPhysicalCanonicalTargets hA hC r Z,
      ‖markedPhysicalSourceBadTerm e x d₀ Y Q V Z hZ w ψ η f g u hS hA hC r z‖

end ArtinMatthews

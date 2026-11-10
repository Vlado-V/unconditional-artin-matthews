module

public import ArtinMatthews.MarkedPhysicalPadCofactorTerm
public import ArtinMatthews.MarkedPhysicalDetectorHarmonicSum
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

/-! Exact fixed-pad and harmonic sums in the genuine natural cofactor
fibers. All box, state, roughness and collision tests remain visible. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J]
  (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime)
  (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
  (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,0 ≤ z.1 ∧ 0 ≤ z.2)
  (η : ℝ → ℂ) (Y : ℝ) (detector : ℤ → ℤ → ℤ → ℂ) (α β : ℕ → ℂ)
  (c : MarkedPhysicalMarking P pads) (b a : (j : J) → ↥(P j))

def markedPhysicalPadCofactorBlock : ℂ :=
  let B := (markedPhysicalMarkingSplit pads).symm (c,b)
  let A := (markedPhysicalMarkingSplit pads).symm (c,a)
  letI := markedPhysicalCofactorCoordinates_fintype hP hdis hZ B
  letI := markedPhysicalCofactorCoordinates_fintype hP hdis hZ A
  ∑ v : MarkedPhysicalCofactorCoordinates (Z := Z) B,
    ∑ u : MarkedPhysicalCofactorCoordinates (Z := Z) A,
      markedPhysicalPadCofactorTerm P pads η Y detector α β c b a v.1 u.1

theorem markedPhysicalPadDetectorResidual_cofactors :
    (∑ z : Z,∑ w : Z,markedPhysicalPadDetectorResidual P pads Z η Y detector
      (fun s => markedPhysicalEndpointVector P (pads+1) α β s.1.1.1)
      (fun s => markedPhysicalEndpointVector P (pads+1) α β s.1.1.1) c b a z w)=
      markedPhysicalPadCofactorBlock P hP hdis pads Z hZ η Y detector α β c b a := by
  rw [markedPhysicalPadDetectorResidual_positions]
  let B := (markedPhysicalMarkingSplit pads).symm (c,b)
  let A := (markedPhysicalMarkingSplit pads).symm (c,a)
  let _ := markedPhysicalCofactorCoordinates_fintype hP hdis hZ B
  let _ := markedPhysicalCofactorCoordinates_fintype hP hdis hZ A
  let EB := markedPhysicalPositionCofactorEquiv hP hdis hZ B
  let EA := markedPhysicalPositionCofactorEquiv hP hdis hZ A
  let F := markedPhysicalPadValidPositionTerm P pads Z η Y detector α β c b a
  change (∑ z : MarkedPhysicalPositions Z B,∑ w : MarkedPhysicalPositions Z A,F z w)=
    markedPhysicalPadCofactorBlock P hP hdis pads Z hZ η Y detector α β c b a
  calc
    _ = ∑ v : MarkedPhysicalCofactorCoordinates (Z := Z) B,
        ∑ w : MarkedPhysicalPositions Z A,F (EB.symm v) w :=
      markedPhysicalPositions_cofactor_sum hP hdis hZ B _
    _ = ∑ v : MarkedPhysicalCofactorCoordinates (Z := Z) B,
        ∑ u : MarkedPhysicalCofactorCoordinates (Z := Z) A,F (EB.symm v) (EA.symm u) := by
      apply Finset.sum_congr rfl
      intro v _
      exact markedPhysicalPositions_cofactor_sum hP hdis hZ A _
    _ = _ := by
      unfold markedPhysicalPadCofactorBlock
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro u _
      exact markedPhysicalPadValidPositionTerm_cofactor P hP hdis pads Z hZ η Y detector α β c b a v u

end

section
open scoped BigOperators
variable {J : Type*} [Fintype J] [DecidableEq J]

theorem markedPhysicalHarmonicPaddedDetectorSum_eq_cofactors
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (pads : ℕ) (Z : ℕ → Finset (ℤ × ℤ)) (hZ : ∀ j z,z ∈ Z j → 0 ≤ z.1 ∧ 0 ≤ z.2)
    (η : ℝ → ℂ) (Y : ℝ) (detector : ℤ → ℤ → ℤ → ℂ) (α β : ℕ → ℂ) :
    markedPhysicalHarmonicPaddedDetectorSum P pads Z η Y detector α β =
      (markedPhysicalMass (fun j => bandReciprocalMass (P j)) 2:ℂ)*
        ∑ c : MarkedPhysicalMarking P pads,((∏ j,∏ k,markedHarmonicAtom (P j) (c j k):ℝ):ℂ)*
          ∑ b : (j : J) → ↥(P j),∑ a : (j : J) → ↥(P j),
            let j := Nat.log 2 (markedPhysicalMarkingProduct c)
            markedPhysicalPadCofactorBlock P hP hdis pads (Z j) (hZ j) η Y detector α β c b a := by
  unfold markedPhysicalHarmonicPaddedDetectorSum markedPhysicalPadDetectorBlock
  simp_rw [markedPhysicalPadDetectorResidual_cofactors P hP hdis pads _ (hZ _) η Y detector α β]

end
end ArtinMatthews

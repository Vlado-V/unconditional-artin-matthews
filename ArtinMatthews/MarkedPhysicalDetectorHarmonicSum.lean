module

public import ArtinMatthews.MarkedPhysicalPadDetector
public import ArtinMatthews.MarkedPhysicalPadHarmonic
public import ArtinMatthews.MarkedPhysicalDetectorKernel
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

/-! Actual physical detector pairings disintegrate into the harmonic law
of the ordered auxiliary pads. Primitive, box, endpoint-support and full
cross-ban restrictions are retained, including for dyad-dependent boxes. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]

def markedPhysicalPadDetectorBlock (P : J → Finset ℕ) (pads : ℕ)
    (Z : Finset (ℤ × ℤ)) (η : ℝ → ℂ) (Y : ℝ) (detector : ℤ → ℤ → ℤ → ℂ)
    (f g : MarkedPhysicalState P (pads+1) Z → ℂ) (c : MarkedPhysicalMarking P pads) : ℂ :=
  ∑ b : (j : J) → ↥(P j),∑ a : (j : J) → ↥(P j),∑ z : Z,∑ w : Z,
    markedPhysicalPadDetectorResidual P pads Z η Y detector f g c b a z w

theorem markedPhysicalEdgeDetectorPairing_pad_blocks
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (η : ℝ → ℂ) (d₀ Y : ℝ) (detector : ℤ → ℤ → ℤ → ℂ)
    (f g : MarkedPhysicalState P (pads+1) Z → ℂ) :
    markedPhysicalEdgeDetectorPairing P hP V pads Z hZ η d₀ Y 1 detector f g=
      ∑ c : MarkedPhysicalMarking P pads,
        if d₀≤(markedPhysicalMarkingProduct c:ℝ) ∧ (markedPhysicalMarkingProduct c:ℝ)<2*d₀ then
          (markedPhysicalMass V (pads+2):ℂ)*((d₀/(markedPhysicalMarkingProduct c:ℝ):ℝ):ℂ)*
            markedPhysicalPadDetectorBlock P pads Z η Y detector f g c else 0 := by
  rw [markedPhysicalEdgeDetectorPairing_shared_pads]
  apply Finset.sum_congr rfl
  intro c _
  simp_rw [markedPhysicalDetectorPairTerm_pad_factor P hP pads Z η Y detector f g hZ V d₀ c]
  by_cases hd : d₀≤(markedPhysicalMarkingProduct c:ℝ) ∧ (markedPhysicalMarkingProduct c:ℝ)<2*d₀
  · simp only [ite_eq_left hd,markedPhysicalPadDetectorBlock,Finset.mul_sum]
  · simp only [ite_eq_right hd,Finset.sum_const_zero]

def markedPhysicalHarmonicPaddedDetectorSum (P : J → Finset ℕ) (pads : ℕ)
    (Z : ℕ → Finset (ℤ × ℤ)) (η : ℝ → ℂ) (Y : ℝ)
    (detector : ℤ → ℤ → ℤ → ℂ) (α β : ℕ → ℂ) : ℂ :=
  (markedPhysicalMass (fun j => bandReciprocalMass (P j)) 2:ℂ)*
    ∑ c : MarkedPhysicalMarking P pads,((∏ j,∏ k,markedHarmonicAtom (P j) (c j k):ℝ):ℂ)*
      markedPhysicalPadDetectorBlock P pads (Z (Nat.log 2 (markedPhysicalMarkingProduct c))) η Y detector
        (fun s => markedPhysicalEndpointVector P (pads+1) α β s.1.1.1)
        (fun s => markedPhysicalEndpointVector P (pads+1) α β s.1.1.1) c

theorem markedPhysicalEdgeDetectorPairing_dyad_harmonic
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (pads : ℕ)
    (Z : ℕ → Finset (ℤ × ℤ)) (hZ : ∀ j z,z ∈ Z j → IsCoprime z.1 z.2)
    (η : ℝ → ℂ) (Y q : ℝ) (detector : ℤ → ℤ → ℤ → ℂ) (α β : ℕ → ℂ) :
    (∑ j ∈ markedPhysicalPadDyadIndices P pads,(((2:ℕ)^j:ℝ):ℂ)⁻¹*
      markedPhysicalEdgeDetectorPairing P hP (fun i => bandReciprocalMass (P i)) pads (Z j) (hZ j)
        η ((2:ℕ)^j) Y q detector
        (fun s => markedPhysicalEndpointVector P (pads+1) α β s.1.1.1)
        (fun s => markedPhysicalEndpointVector P (pads+1) α β s.1.1.1))=
      markedPhysicalHarmonicPaddedDetectorSum P pads Z η Y detector α β := by
  let F (j : ℕ) (c : MarkedPhysicalMarking P pads) :=
    markedPhysicalPadDetectorBlock P pads (Z j) η Y detector
      (fun s => markedPhysicalEndpointVector P (pads+1) α β s.1.1.1)
      (fun s => markedPhysicalEndpointVector P (pads+1) α β s.1.1.1) c
  calc
    _ = ∑ j ∈ markedPhysicalPadDyadIndices P pads,(((2:ℕ)^j:ℝ):ℂ)⁻¹*
        ∑ c : MarkedPhysicalMarking P pads,
          if ((2:ℕ)^j:ℝ)≤(markedPhysicalMarkingProduct c:ℝ) ∧
              (markedPhysicalMarkingProduct c:ℝ)<2*((2:ℕ)^j:ℝ) then
            (markedPhysicalMass (fun i => bandReciprocalMass (P i)) (pads+2):ℂ)*
              (((((2:ℕ)^j:ℝ)/(markedPhysicalMarkingProduct c:ℝ)):ℝ):ℂ)*F j c else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      rw [markedPhysicalEdgeDetectorPairing_endpoint_damping,
        markedPhysicalEdgeDetectorPairing_pad_blocks]
    _ = _ := markedPhysicalPad_dyad_actual_harmonic P hP pads F

theorem markedPhysicalEdgePairing_dyad_delta_sub_major
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (pads : ℕ)
    (Z : ℕ → Finset (ℤ × ℤ)) (hZ : ∀ j z,z ∈ Z j → IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (Y Q q : ℝ) (α β : ℕ → ℂ) :
    (∑ j ∈ markedPhysicalPadDyadIndices P pads,(((2:ℕ)^j:ℝ):ℂ)⁻¹*
      markedPhysicalEdgePairing P hP (fun i => bandReciprocalMass (P i)) pads (Z j) (hZ j)
        ψ η ((2:ℕ)^j) Y Q q
        (fun s => markedPhysicalEndpointVector P (pads+1) α β s.1.1.1)
        (fun s => markedPhysicalEndpointVector P (pads+1) α β s.1.1.1))=
      markedPhysicalHarmonicPaddedDetectorSum P pads Z η Y (markedRawEdgeDeltaDetector ψ Y) α β-
        markedPhysicalHarmonicPaddedDetectorSum P pads Z η Y (markedRawEdgeMajorDetector ψ Q Y) α β := by
  simp_rw [markedPhysicalEdgePairing_eq_delta_sub_major,mul_sub,Finset.sum_sub_distrib]
  rw [markedPhysicalEdgeDetectorPairing_dyad_harmonic,markedPhysicalEdgeDetectorPairing_dyad_harmonic]

end
end ArtinMatthews

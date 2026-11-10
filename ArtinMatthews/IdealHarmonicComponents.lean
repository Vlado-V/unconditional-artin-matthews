module

public import ArtinMatthews.IdealProbeRemainder
public import ArtinMatthews.IdealProbeComponents
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

/-! The complete harmonic probe decomposition and its contractions
are intrinsic to the original full-label product law. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealHarmonicBasis_exists {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (hV : ∀ g,0 < bandReciprocalMass (P g))
    (hP : ∀ g p,p∈P g → 0 < p) :
    ∃ (a₀ : ∀ g,↥(P g)) (b : ∀ g,OrthonormalBasis ↥(P g) ℂ (EuclideanSpace ℂ ↥(P g))),
      ∀ g,b g (a₀ g)=idealProbabilityRoot (markedHarmonicAtom (P g)) := by
  have hN (g : G) : Nonempty ↥(P g) := by
    by_contra h
    have he : P g=∅ := eq_empty_iff_forall_notMem.mpr fun p hp => h ⟨⟨p,hp⟩⟩
    have hv := hV g
    simp only [he,bandReciprocalMass,sum_empty] at hv
    exact (lt_irrefl 0 hv)
  let a₀ : ∀ g,↥(P g) := fun g => Classical.choice (hN g)
  choose b hb using fun g => idealCoordinateBasis_exists (markedHarmonicAtom (P g))
    (fun p => (idealHarmonicAtom_pos (P g) (hV g) (hP g) p).le)
    (markedHarmonicAtom_sum (P g) (hV g)) (a₀ g)
  exact ⟨a₀,b,hb⟩

theorem idealProbeComponents_sum_harmonic {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (hV : ∀ g,0 < bandReciprocalMass (P g))
    (hP : ∀ g p,p∈P g → 0 < p) (probes tail : Finset (G × Fin M))
    (f : MarkedPhysicalMarking P M → ℂ) :
    (fun a => ∑ S∈probes.powerset,idealProbeComponent P probes S tail f a)=idealAverageSet P tail f := by
  obtain ⟨a₀,b,hb⟩ := idealHarmonicBasis_exists P hV hP
  exact idealProbeComponents_sum P hV (fun g p => idealHarmonicAtom_pos (P g) (hV g) (hP g) p)
    b a₀ hb probes tail f

theorem idealProbeProjection_energy_le {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (hV : ∀ g,0 < bandReciprocalMass (P g))
    (hP : ∀ g p,p∈P g → 0 < p) (probes tail : Finset (G × Fin M))
    (f : MarkedPhysicalMarking P M → ℂ) :
    idealLabelEnergy P M (idealProbeProjection P probes tail f) ≤ idealLabelEnergy P M f := by
  obtain ⟨a₀,b,hb⟩ := idealHarmonicBasis_exists P hV hP
  rw [idealProbeProjection_energy P hV (fun g p => idealHarmonicAtom_pos (P g) (hV g) (hP g) p) b a₀ hb,
    ← idealHoeffdingTransform_energy P hV b f]
  apply sum_le_sum
  intro t _
  split_ifs
  · rfl
  · positivity

theorem idealProbeComponent_energy_le {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (hV : ∀ g,0 < bandReciprocalMass (P g))
    (hP : ∀ g p,p∈P g → 0 < p) (probes S tail : Finset (G × Fin M))
    (f : MarkedPhysicalMarking P M → ℂ) :
    idealLabelEnergy P M (idealProbeComponent P probes S tail f) ≤ idealLabelEnergy P M f :=
  idealProbeProjection_energy_le P hV hP S (tail ∪ (probes \ S)) f

theorem idealProbeRemainder_energy_le_harmonic {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (hV : ∀ g,0 < bandReciprocalMass (P g))
    (hP : ∀ g p,p∈P g → 0 < p) (probes tail : Finset (G × Fin M))
    (f : MarkedPhysicalMarking P M → ℂ) :
    idealLabelEnergy P M (idealProbeRemainder P probes tail f) ≤ idealLabelEnergy P M f := by
  obtain ⟨a₀,b,hb⟩ := idealHarmonicBasis_exists P hV hP
  exact idealProbeRemainder_energy_le P hV
    (fun g p => idealHarmonicAtom_pos (P g) (hV g) (hP g) p) b a₀ hb probes tail f

end
end ArtinMatthews

module

public import ArtinMatthews.GiantSignedStatePairingEnergy
public import ArtinMatthews.GiantSignedProjectedWord
public import ArtinMatthews.GiantSignedBoundaryDomain
public import ArtinMatthews.GiantSignedProjectedWordEnergy
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

/-! The literal boundary sum is the weighted pairing with the original
empty-memory vector. Its norm uses the same state energy as every local step. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B I : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

theorem giantSignedStatePairing_boundary_eq {M : ℕ} (ν : ∀ g, PB g → ℝ)
    (w : GiantSignedState PS PB M → ℂ) :
    giantSignedStatePairing PS ν giantSignedBoundary w =
      ∑ y : GiantTwoSidedResidueState PS M, ∑ a : MarkedPhysicalMarking PB M,
        ((giantTwoSidedResidueHaarStateMass PS M * giantSignedActiveMass ν a : ℝ) : ℂ) *
          w (y,a,giantSignedEmptyMemory PB) := by
  rw [giantSignedStatePairing, tsum_eq_single (giantSignedEmptyMemory PB)]
  · simp only [giantSignedStateFiberPairing, Fintype.sum_prod_type, giantSignedStateMass,
      giantSignedEmptyMemory_mass, mul_one, giantSignedBoundary_empty, star_one]
  · intro m hm
    simp only [giantSignedStateFiberPairing, giantSignedBoundary, hm, ite_false, star_zero,
      mul_zero, zero_mul, Finset.sum_const_zero]

variable {k ell : ℕ} [∀ g, ∀ p : PB g, NeZero p.val]

theorem giantSignedProjectedBoundaryPairing_eq_statePairing
    (N : ℕ) (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ)
    (n : ℕ) (patterns : Fin n → Finset I)
    (C : Fin n → I → B → Finset (Fin k)) (κ : Fin n → ℤ)
    (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (p : I) → GiantTwoSidedPatternCoefficient PB (C i p) ell)
    (η : (i : Fin n) → (p : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i p) s.2.2 → ℂ) :
    giantSignedProjectedChronologicalBoundaryPairing N ν V q ρ θ n patterns C κ visitQ ζ K η =
      giantSignedStatePairing PS ν giantSignedBoundary
        (giantSignedProjectedChronologicalWord N ν V q ρ θ giantSignedBoundary
          n patterns C κ visitQ ζ K η) :=
  (giantSignedStatePairing_boundary_eq PS ν _).symm

theorem giantSignedProjectedBoundaryPairing_energy_of_local
    (N : ℕ) (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (V : B → ℝ) (q ρ θ G A : ℝ)
    (n : ℕ) (patterns : Fin n → Finset I)
    (C : Fin n → I → B → Finset (Fin k)) (κ : Fin n → ℤ)
    (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (p : I) → GiantTwoSidedPatternCoefficient PB (C i p) ell)
    (hboundary : giantSignedStateEnergy PS ν (giantSignedBoundary (M := k+ell)) ≤ 2)
    (hvisit : ∀ (i : Fin (n+1)) (w : GiantSignedState PS PB (k+ell) → ℂ),
      (∀ s a, GiantSignedMemorySymmetric (fun m => w (s,a,m))) →
      giantSignedStateEnergy PS ν (giantSignedProjectedVisit N ν V (visitQ i) ρ w) ≤
        ENNReal.ofReal G * giantSignedStateEnergy PS ν w)
    (hedge : ∀ (i : Fin n) (w : GiantSignedState PS PB (k+ell) → ℂ),
      (∀ s a, GiantSignedMemorySymmetric (fun m => w (s,a,m))) →
      giantSignedStateEnergy PS ν (giantSignedProjectedRawEdgeFamilyApply N ν V
        (patterns i) (C i) (κ i) q ρ θ (ζ i) (K i) (fun _ _ _ => 1) w) ≤
        ENNReal.ofReal A * giantSignedStateEnergy PS ν w) :
    ENNReal.ofReal (‖giantSignedProjectedChronologicalBoundaryPairing (PS := PS) N ν V q ρ θ
      n patterns C κ visitQ ζ K (fun _ _ _ _ => 1)‖ ^ 2) ≤
      4 * (ENNReal.ofReal G) ^ (n+1) * (ENNReal.ofReal A) ^ n := by
  let b : GiantSignedState PS PB (k+ell) → ℂ := giantSignedBoundary
  let w := giantSignedProjectedChronologicalWord N ν V q ρ θ b
    n patterns C κ visitQ ζ K (fun _ _ _ _ => 1)
  let G' := (ENNReal.ofReal G) ^ (n+1)
  let A' := (ENNReal.ofReal A) ^ n
  have hword : giantSignedStateEnergy PS ν w ≤ G' * A' * giantSignedStateEnergy PS ν b :=
    (giantSignedProjectedChronologicalWord_energy_of_local N ν hν V q ρ θ
      (ENNReal.ofReal G) (ENNReal.ofReal A) b (fun s a => giantSignedBoundary_memorySymmetric s a)
      n patterns C κ visitQ ζ K (fun _ _ _ _ => 1) (fun _ _ _ _ _ _ => rfl) hvisit hedge).2
  have hb : giantSignedStateEnergy PS ν b ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofNat_ne_top hboundary
  have hw : giantSignedStateEnergy PS ν w ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ?_) hb) hword
    · exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    · exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  rw [giantSignedProjectedBoundaryPairing_eq_statePairing PS]
  calc
    _ ≤ giantSignedStateEnergy PS ν b * giantSignedStateEnergy PS ν w :=
      giantSignedStatePairing_energy PS hVS ν hν b w hb hw
    _ ≤ 2 * (G' * A' * 2) :=
      mul_le_mul' hboundary (hword.trans (mul_le_mul_right hboundary _))
    _ = _ := by
      change 2 * (G' * A' * 2) = 4 * G' * A'
      ring

end
end ArtinMatthews

module

public import ArtinMatthews.GiantSignedBirthMixedEdges
public import ArtinMatthews.GiantSignedProjectedBirthWord
public import ArtinMatthews.GiantSignedRawOldPermutation
public import ArtinMatthews.GiantSignedBoundaryDomain
public import ArtinMatthews.GiantSignedInitialBirthBoundary
public import ArtinMatthews.GiantSignedProjectedBirthWordEnergy
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Unaffected edges use the original signed family. The other edges use
its absolute estimate with the literal local birth multipliers. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
universe u

def giantSignedUniformBirthRank {B : Type*} [Fintype B] {M n H : ℕ}
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B M n H)) : ℕ :=
  markedBirthPermutationRank σ

variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

theorem giantSignedProjectedBirthBoundaryPairing_norm_of_mixed_local
    (H : ℕ) (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (V : B → ℝ) (q ρ θ g a b : ℝ) (hg : 0 ≤ g) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hb : 1 ≤ b) (n : ℕ) (patterns : Fin n → Finset I)
    (C : Fin n → I → B → Finset (Fin k)) (κ : Fin n → ℤ)
    (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (p : I) → GiantTwoSidedPatternCoefficient PB (C i p) ell)
    (η : (i : Fin n) → (p : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i p) s.2.2 → ℂ)
    (φ : Fin (n+1) → GiantSignedGhostBirthMultiplier PB)
    (φ₀ : MarkedPhysicalMarking PB (k+ell) → ℂ) (hφ₀ : ∀ x, ‖φ₀ x‖ ≤ 1)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H))
    (hr : 2 * giantSignedUniformBirthRank σ ≤ n)
    (hη : ∀ i p, p ∈ patterns i → ∀ (s : GiantSignedState PS PB (k+ell))
      (τ : ∀ g, Equiv.Perm (Fin (s.2.2.1 g)))
      (r : GiantSignedRawEdgeMove PS PB ell (C i p) (giantSignedMemoryPermute s.2.2 τ)),
      η i p (s.1,s.2.1,giantSignedMemoryPermute s.2.2 τ) r =
        η i p s (giantSignedRawEdgeOldEquiv s.2.2 τ r))
    (hηone : ∀ i, i ∉ giantSignedUniformBirthModifiedEdges σ →
      ∀ p ∈ patterns i, ∀ s r, η i p s r = 1)
    (hboundary : giantSignedStateEnergy PS ν (giantSignedBoundary (M := k+ell)) ≤ 2)
    (hvisit : ∀ (i : Fin (n+1)) (w : GiantSignedState PS PB (k+ell) → ℂ),
      (∀ s a, GiantSignedMemorySymmetric (fun m => w (s,a,m))) →
      let z := giantSignedProjectedBirthVisit H ν V (visitQ i) ρ (φ i) w
      (∀ s a, GiantSignedMemorySymmetric (fun m => z (s,a,m))) ∧
      giantSignedStateEnergy PS ν z ≤ ENNReal.ofReal (g^2) * giantSignedStateEnergy PS ν w)
    (hsigned : ∀ (i : Fin n) (w : GiantSignedState PS PB (k+ell) → ℂ),
      (∀ s a, GiantSignedMemorySymmetric (fun m => w (s,a,m))) →
      giantSignedStateEnergy PS ν (giantSignedProjectedRawEdgeFamilyApply H ν V
        (patterns i) (C i) (κ i) q ρ θ (ζ i) (K i) (fun _ _ _ => 1) w) ≤
        ENNReal.ofReal (a^2) * giantSignedStateEnergy PS ν w)
    (habsolute : ∀ (i : Fin n) (w : GiantSignedState PS PB (k+ell) → ℂ),
      (∀ s a, GiantSignedMemorySymmetric (fun m => w (s,a,m))) →
      giantSignedStateEnergy PS ν (giantSignedProjectedRawEdgeFamilyApply H ν V
        (patterns i) (C i) (κ i) q ρ θ (ζ i) (K i) (η i) w) ≤
        ENNReal.ofReal (b^2) * giantSignedStateEnergy PS ν w) :
    let r := giantSignedUniformBirthRank σ
    ‖giantSignedProjectedBirthBoundaryPairing (PS := PS) H ν V q ρ θ
      n patterns C κ visitQ ζ K η φ φ₀‖ ≤ 2*g^(n+1)*a^(n-2*r)*b^(2*r) := by
  let edges := giantSignedUniformBirthModifiedEdges σ
  let m := edges.card
  let A (i : Fin n) := if i ∈ edges then ENNReal.ofReal (b^2) else ENNReal.ofReal (a^2)
  let z : GiantSignedState PS PB (k+ell) → ℂ := giantSignedBoundary
  let word := giantSignedProjectedBirthChronologicalWord H ν V q ρ θ z n
    patterns C κ visitQ ζ K η φ
  have hedge (i : Fin n) (w : GiantSignedState PS PB (k+ell) → ℂ)
      (hsym : ∀ s a, GiantSignedMemorySymmetric (fun m => w (s,a,m))) :
      giantSignedStateEnergy PS ν (giantSignedProjectedRawEdgeFamilyApply H ν V
        (patterns i) (C i) (κ i) q ρ θ (ζ i) (K i) (η i) w) ≤
        A i * giantSignedStateEnergy PS ν w := by
    by_cases hi : i ∈ edges
    · simpa only [A, if_pos hi] using habsolute i w hsym
    · rw [giantSignedProjectedRawEdgeFamilyApply_multiplier_congr H ν V (patterns i)
        (C i) (κ i) q ρ θ (ζ i) (K i) (η i) (fun _ _ _ => 1) (hηone i hi) w]
      simpa only [A, if_neg hi] using hsigned i w hsym
  have hword := (giantSignedProjectedBirthChronologicalWord_energy_of_local H ν V q ρ θ
    (ENNReal.ofReal (g^2)) z (fun s a => giantSignedBoundary_memorySymmetric s a)
    n patterns C κ visitQ ζ K η φ A hη hvisit hedge).2
  let cost := g^(n+1)*a^(n-m)*b^m
  have hprod : (ENNReal.ofReal (g^2))^(n+1) * (∏ i, A i) = ENNReal.ofReal (cost^2) := by
    rw [giantSignedUniformBirth_edge_product σ]
    rw [← ENNReal.ofReal_pow (sq_nonneg g), ← ENNReal.ofReal_pow (sq_nonneg a),
      ← ENNReal.ofReal_pow (sq_nonneg b), ← ENNReal.ofReal_mul (pow_nonneg (sq_nonneg a) _),
      ← ENNReal.ofReal_mul (pow_nonneg (sq_nonneg g) _)]
    congr 1
    dsimp only [cost, m, edges]
    rw [pow_right_comm g 2 (n+1), pow_right_comm a 2 _, pow_right_comm b 2 _]
    ring
  rw [hprod] at hword
  have hcost : 0 ≤ cost := by dsimp only [cost]; positivity
  have hnorm := giantSignedInitialBirthBoundary_norm_of_energy PS hVS ν hν φ₀ hφ₀
    word hcost hboundary hword
  have hcount := giantSignedUniformBirth_edge_norm_budget σ ha ha1 hb hr
  rw [giantSignedUniformBirth_edge_product σ] at hcount
  let r := giantSignedUniformBirthRank σ
  change a^(n-m)*b^m ≤ a^(n-2*r)*b^(2*r) at hcount
  refine hnorm.trans ?_
  change 2*cost ≤ 2*g^(n+1)*a^(n-2*r)*b^(2*r)
  calc
    _ = (2*g^(n+1))*(a^(n-m)*b^m) := by dsimp only [cost]; ac_rfl
    _ ≤ (2*g^(n+1))*(a^(n-2*r)*b^(2*r)) :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = _ := by ac_rfl

end
end ArtinMatthews

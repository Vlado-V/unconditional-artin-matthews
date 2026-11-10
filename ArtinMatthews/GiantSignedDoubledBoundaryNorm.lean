module

public import ArtinMatthews.GiantSignedDoubledChronologicalWord
public import ArtinMatthews.GiantSignedProjectedBoundaryEnergy
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

/-! The doubled word is paired with the original empty boundary and keeps
the exact square-root scale of its energy bound. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B I : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

theorem giantSignedDoubledBoundaryPairing_norm_of_energy
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (V : B → ℝ) (q ρ θ L Cv Cₐ : ℝ) (hL : 0 < L)
    (n : ℕ) (patterns : Fin n → Finset I)
    (C : Fin n → I → B → Finset (Fin k)) (κ : Fin n → ℤ)
    (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (p : I) → GiantTwoSidedPatternCoefficient PB (C i p) ell)
    (η : (i : Fin n) → (p : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i p) s.2.2 → ℂ)
    (hboundary : giantSignedStateEnergy PS ν (giantSignedBoundary (M := k+ell)) ≤ 2)
    (hword : giantSignedStateEnergy PS ν
        (giantSignedDoubledChronologicalWord ν V q ρ θ
          (giantSignedBoundary (PS := PS)) n patterns C κ visitQ ζ K η) ≤
      (ENNReal.ofReal ((L ^ Cv) ^ (2 : ℕ))) ^ (n+1) *
        (ENNReal.ofReal ((L ^ Cₐ) ^ (2 : ℕ))) ^ n *
          giantSignedStateEnergy PS ν (giantSignedBoundary (M := k+ell))) :
    ‖giantSignedDoubledChronologicalBoundaryPairing ν V q ρ θ n patterns C κ visitQ ζ K η‖ ≤
      2 * (L ^ Cv) ^ (n+1) * (L ^ Cₐ) ^ n := by
  let b : GiantSignedState PS PB (k+ell) → ℂ := giantSignedBoundary
  let w := giantSignedDoubledChronologicalWord ν V q ρ θ b n patterns C κ visitQ ζ K η
  let P := giantSignedDoubledChronologicalBoundaryPairing ν V q ρ θ n patterns C κ visitQ ζ K η
  let G := (ENNReal.ofReal ((L ^ Cv) ^ (2 : ℕ))) ^ (n+1)
  let A := (ENNReal.ofReal ((L ^ Cₐ) ^ (2 : ℕ))) ^ n
  have hb : giantSignedStateEnergy PS ν b ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofNat_ne_top hboundary
  have hw : giantSignedStateEnergy PS ν w ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)) hb) hword
  have heq : giantSignedStatePairing PS ν b w = P := giantSignedStatePairing_boundary_eq PS ν w
  have he : ENNReal.ofReal (‖P‖^2) ≤ 4 * G * A := by
    have h := giantSignedStatePairing_energy PS hVS ν hν b w hb hw
    rw [heq] at h
    calc
      _ ≤ _ := h
      _ ≤ 2 * (G * A * 2) :=
        mul_le_mul' hboundary (hword.trans (mul_le_mul_right hboundary _))
      _ = _ := by ring
  have hR : 0 ≤ 2 * (L ^ Cv) ^ (n+1) * (L ^ Cₐ) ^ n := by positivity
  apply (sq_le_sq₀ (norm_nonneg _) hR).mp
  apply (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp
  refine he.trans_eq ?_
  dsimp only [G, A]
  rw [← ENNReal.ofReal_pow (sq_nonneg (L ^ Cv)), ← ENNReal.ofReal_pow (sq_nonneg (L ^ Cₐ)),
    show (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
    ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) (pow_nonneg (sq_nonneg _) _))]
  congr 1
  rw [pow_right_comm (L ^ Cv) 2 (n+1), pow_right_comm (L ^ Cₐ) 2 n]
  ring

end
end ArtinMatthews

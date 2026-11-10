module

public import ArtinMatthews.GiantSignedFockMoments
public import ArtinMatthews.GiantSignedGhostPointwise
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

/-! The actual ghost row preserves exponential growth. Consequently its
full factorial pairings are absolutely summable on that class. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedGhostZeroIndices_card_le {P : Finset ℕ} (m : GiantSignedGroupMemory P) :
    (giantSignedGhostZeroIndices m).card ≤ m.1 := by
  simpa only [giantSignedGhostZeroIndices, Finset.card_univ, Fintype.card_fin] using
    Finset.card_le_card (Finset.filter_subset (fun i => (m.2 i).2 = 0) Finset.univ)

theorem giantSignedGhostGroupApply_exponential_bound {P : Finset ℕ}
    (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p) (A C D : ℂ)
    (f : GiantSignedGroupMemory P → ℂ) (B v : ℝ) (hB : 0 ≤ B) (hv : 0 < v)
    (hf : ∀ m, ‖f m‖ ≤ B * v ^ m.1) (m : GiantSignedGroupMemory P) :
    ‖giantSignedGhostGroupApply ν A C D f m‖ ≤
      (B * Real.exp (‖C‖ * (∑ p : P, ν p) * v)) *
        (v * max 1 (‖A‖ + ‖D‖ / v)) ^ m.1 := by
  let t := max 1 (‖A‖ + ‖D‖ / v)
  have ht : 1 ≤ t := le_max_left _ _
  have ha : 0 ≤ ‖A‖ + ‖D‖ / v := add_nonneg (norm_nonneg _) (div_nonneg (norm_nonneg _) hv.le)
  have hp : (‖A‖ + ‖D‖ / v) ^ (giantSignedGhostZeroIndices m).card ≤ t ^ m.1 :=
    (pow_le_pow_left₀ ha (le_max_right _ _) _).trans
      (pow_le_pow_right₀ ht (giantSignedGhostZeroIndices_card_le m))
  calc
    _ ≤ B * v ^ m.1 * Real.exp (‖C‖ * (∑ p : P, ν p) * v) *
        (‖A‖ + ‖D‖ / v) ^ (giantSignedGhostZeroIndices m).card :=
      giantSignedGhostGroupApply_norm_le ν hν A C D f B v hv hf m
    _ ≤ B * v ^ m.1 * Real.exp (‖C‖ * (∑ p : P, ν p) * v) * t ^ m.1 :=
      mul_le_mul_of_nonneg_left hp
        (mul_nonneg (mul_nonneg hB (pow_nonneg hv.le _)) (Real.exp_nonneg _))
    _ = _ := by rw [mul_pow]; ring

theorem giantSignedGroupPairing_summable_norm {P : Finset ℕ} [∀ p : P, NeZero p.val]
    (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p)
    (f g : GiantSignedGroupMemory P → ℂ) (B F u v : ℝ)
    (hB : 0 ≤ B) (_hF : 0 ≤ F) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hf : ∀ m, ‖f m‖ ≤ B * u ^ m.1) (hg : ∀ m, ‖g m‖ ≤ F * v ^ m.1) :
    Summable (fun m => ‖(giantSignedGroupMemoryMass ν m : ℂ) * star (f m) * g m‖) := by
  apply ((giantSignedFock_exponential_summable ν hν (u * v) (mul_nonneg hu hv)).mul_left
    (B * F)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro m
  rw [norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (giantSignedGroupMemoryMass_nonneg ν hν m), norm_star]
  calc
    _ = giantSignedGroupMemoryMass ν m * (‖f m‖ * ‖g m‖) := by ring
    _ ≤ giantSignedGroupMemoryMass ν m * ((B * u ^ m.1) * (F * v ^ m.1)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (hf m) (hg m) (norm_nonneg _) (mul_nonneg hB (pow_nonneg hu _)))
        (giantSignedGroupMemoryMass_nonneg ν hν m)
    _ = _ := by rw [mul_pow]; ring

theorem giantSignedGroupPairing_summable {P : Finset ℕ} [∀ p : P, NeZero p.val]
    (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p)
    (f g : GiantSignedGroupMemory P → ℂ) (B F u v : ℝ)
    (hB : 0 ≤ B) (hF : 0 ≤ F) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hf : ∀ m, ‖f m‖ ≤ B * u ^ m.1) (hg : ∀ m, ‖g m‖ ≤ F * v ^ m.1) :
    Summable (fun m => (giantSignedGroupMemoryMass ν m : ℂ) * star (f m) * g m) :=
  (giantSignedGroupPairing_summable_norm ν hν f g B F u v hB hF hu hv hf hg).of_norm

end
end ArtinMatthews

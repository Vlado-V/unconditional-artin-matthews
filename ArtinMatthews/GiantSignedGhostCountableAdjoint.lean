module

public import ArtinMatthews.GiantSignedGhostRawPairing
public import ArtinMatthews.GiantSignedGhostAbsoluteSeries
public import ArtinMatthews.GiantSignedGhostGrowth
public import ArtinMatthews.GiantSignedGhostRawSeries
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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual countable ghost pairing is the sum of all finite-degree
blocks. Its adjoint exchanges births and deletions in the factorial measure. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {P : Finset ℕ} [∀ p : P, NeZero p.val]

def giantSignedGhostAllDegreeBlock (ν : P → ℝ) (A C D : ℂ)
    (f h : GiantSignedGroupMemory P → ℂ) (d : GiantSignedGhostDegrees) : ℂ :=
  giantSignedGhostDegreePairing ν A C D d.survivors d.deleted d.born
    (fun a => f ⟨d.survivors + d.deleted, a⟩)
    (fun a => h ⟨d.survivors + d.born, a⟩)

def giantSignedGhostSwapDegrees : GiantSignedGhostDegrees ≃ GiantSignedGhostDegrees where
  toFun d := ⟨d.survivors, d.born, d.deleted⟩
  invFun d := ⟨d.survivors, d.born, d.deleted⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem giantSignedGhost_pairing_eq_raw
    (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p) (A C D : ℂ)
    (f h : GiantSignedGroupMemory P → ℂ) (B F u v : ℝ)
    (hB : 0 ≤ B) (hF : 0 ≤ F) (hu : 0 ≤ u) (hv : 0 < v)
    (hf : ∀ m, ‖f m‖ ≤ B * u ^ m.1) (hh : ∀ m, ‖h m‖ ≤ F * v ^ m.1) :
    giantSignedGroupPairing ν f (giantSignedGhostGroupApply ν A C D h) =
      ∑' r, giantSignedGhostRawPairingBlock ν A C D f h r := by
  classical
  have hs := giantSignedGhostRawPairingBlock_summable ν hν A C D f h B F u v
    hB hF hu hv hf hh
  rw [hs.tsum_sigma]
  have hi : ∀ k, (∑' s : Finset (Fin k) × ℕ,
      giantSignedGhostRawPairingBlock ν A C D f h ⟨k, s⟩) =
      ∑ a : Fin k → GiantSignedParticle P,
        (giantSignedGroupMemoryMass ν ⟨k, a⟩ : ℂ) * star (f ⟨k, a⟩) *
          giantSignedGhostGroupApply ν A C D h ⟨k, a⟩ := by
    intro k
    rw [(hs.sigma_factor k).tsum_prod]
    simpa only [tsum_fintype] using
      giantSignedGhostRawPairingBlock_source_degree ν hν A C D f h F v hh k
  simp_rw [hi]
  unfold giantSignedGroupPairing
  symm
  have hp := giantSignedGroupPairing_summable ν hν f (giantSignedGhostGroupApply ν A C D h)
    B (F * Real.exp (‖C‖ * (∑ p : P, ν p) * v)) u
    (v * max 1 (‖A‖ + ‖D‖ / v)) hB (mul_nonneg hF (Real.exp_nonneg _)) hu
    (mul_nonneg hv.le (le_trans zero_le_one (le_max_left _ _))) hf
    (giantSignedGhostGroupApply_exponential_bound ν hν A C D h F v hF hv hh)
  simpa only [tsum_fintype] using hp.tsum_sigma.symm

theorem giantSignedGhost_pairing_eq_degrees
    (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p) (A C D : ℂ)
    (f h : GiantSignedGroupMemory P → ℂ) (B F u v : ℝ)
    (hB : 0 ≤ B) (hF : 0 ≤ F) (hu : 0 ≤ u) (hv : 0 < v)
    (hf : ∀ m, ‖f m‖ ≤ B * u ^ m.1) (hh : ∀ m, ‖h m‖ ≤ F * v ^ m.1) :
    giantSignedGroupPairing ν f (giantSignedGhostGroupApply ν A C D h) =
      ∑' d, giantSignedGhostAllDegreeBlock ν A C D f h d := by
  classical
  rw [giantSignedGhost_pairing_eq_raw ν hν A C D f h B F u v hB hF hu hv hf hh,
    ← giantSignedGhostDegree_tsum]
  have hd := (giantSignedGhostRawPairingBlock_summable ν hν A C D f h B F u v
    hB hF hu hv hf hh).comp_injective giantSignedGhostDegreeToRaw_injective
  calc
    _ = ∑' d : GiantSignedGhostDegrees,
        ∑' S : MarkedRawDeletionBatch (d.survivors + d.deleted) d.deleted,
          giantSignedGhostRawPairingBlock ν A C D f h (giantSignedGhostDegreeToRaw ⟨d, S⟩) := by
      simpa only [Function.comp_apply] using hd.tsum_sigma
    _ = _ := by
      apply tsum_congr
      intro d
      simpa only [tsum_fintype, giantSignedGhostDegreeToRaw, giantSignedGhostAllDegreeBlock] using
        giantSignedGhostRawPairingBlock_degree ν A C D f h d.survivors d.deleted d.born

theorem giantSignedGhostGroupPairing_adjoint
    (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p) (A C D : ℂ)
    (f h : GiantSignedGroupMemory P → ℂ)
    (hfs : GiantSignedGroupSymmetric f) (hhs : GiantSignedGroupSymmetric h)
    (B F u v : ℝ) (hB : 0 ≤ B) (hF : 0 ≤ F) (hu : 0 < u) (hv : 0 < v)
    (hf : ∀ m, ‖f m‖ ≤ B * u ^ m.1) (hh : ∀ m, ‖h m‖ ≤ F * v ^ m.1) :
    giantSignedGroupPairing ν f (giantSignedGhostGroupApply ν A C D h) =
      star (giantSignedGroupPairing ν h
        (giantSignedGhostGroupApply ν (star A) (star D) (star C) f)) := by
  rw [giantSignedGhost_pairing_eq_degrees ν hν A C D f h B F u v hB hF hu.le hv hf hh,
    giantSignedGhost_pairing_eq_degrees ν hν (star A) (star D) (star C) h f
      F B v u hF hB hv.le hu hh hf]
  have he : ∀ d, giantSignedGhostAllDegreeBlock ν A C D f h d =
      star (giantSignedGhostAllDegreeBlock ν (star A) (star D) (star C) h f
        (giantSignedGhostSwapDegrees d)) := by
    intro d
    exact giantSignedGhostDegreePairing_adjoint ν A C D d.survivors d.deleted d.born
      (fun a => f ⟨d.survivors + d.deleted, a⟩) (hfs _)
      (fun a => h ⟨d.survivors + d.born, a⟩) (hhs _)
  simp_rw [he]
  calc
    _ = ∑' d, star (giantSignedGhostAllDegreeBlock ν (star A) (star D) (star C) h f d) :=
      giantSignedGhostSwapDegrees.tsum_eq _
    _ = _ := (Complex.conj_tsum _).symm

end
end ArtinMatthews

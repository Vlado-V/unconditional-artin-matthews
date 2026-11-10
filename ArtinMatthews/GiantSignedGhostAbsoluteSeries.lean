module

public import ArtinMatthews.GiantSignedGhostRawPairing
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

/-! Absolute convergence of the complete deletion and birth expansion,
with its original factorial measure. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {P : Finset ℕ} [∀ p : P, NeZero p.val]

theorem giantSignedGhostPositivePairingBlock_birth_summable
    (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p) (A C D : ℝ)
    (f h : GiantSignedGroupMemory P → ℝ) (F v : ℝ)
    (hh : ∀ m, ‖(h m : ℂ)‖ ≤ F * v ^ m.1)
    (k : ℕ) (S : Finset (Fin k)) :
    Summable (fun b : ℕ => giantSignedGhostPositivePairingBlock ν A C D f h ⟨k, S, b⟩) := by
  apply Complex.summable_ofReal.mp
  simp_rw [giantSignedGhostPositivePairingBlock_coe]
  exact giantSignedGhostRawPairingBlock_birth_summable ν hν
    (A : ℂ) (C : ℂ) (D : ℂ) (fun m => (f m : ℂ)) (fun m => (h m : ℂ)) F v hh k S

theorem giantSignedGhostPositivePairingBlock_summable
    (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p) (A C D : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (f h : GiantSignedGroupMemory P → ℝ)
    (hf0 : ∀ m, 0 ≤ f m) (hh0 : ∀ m, 0 ≤ h m)
    (B F u v : ℝ) (hB : 0 ≤ B) (hF : 0 ≤ F) (hu : 0 ≤ u) (hv : 0 < v)
    (hf : ∀ m, f m ≤ B * u ^ m.1) (hh : ∀ m, h m ≤ F * v ^ m.1) :
    Summable (giantSignedGhostPositivePairingBlock ν A C D f h) := by
  classical
  let φ := giantSignedGhostPositivePairingBlock ν A C D f h
  have hφ : ∀ r, 0 ≤ φ r :=
    giantSignedGhostPositivePairingBlock_nonneg ν hν A C D hA hC hD f h hf0 hh0
  have hhc : ∀ m, ‖(h m : ℂ)‖ ≤ F * v ^ m.1 := by
    intro m
    simpa only [Complex.norm_real, Real.norm_of_nonneg (hh0 m)] using hh m
  have hfc : ∀ m, ‖(f m : ℂ)‖ ≤ B * u ^ m.1 := by
    intro m
    simpa only [Complex.norm_real, Real.norm_of_nonneg (hf0 m)] using hf m
  have hinner : ∀ k, Summable (fun s : Finset (Fin k) × ℕ => φ ⟨k, s⟩) := by
    intro k
    apply (summable_prod_of_nonneg (fun s => hφ ⟨k, s⟩)).mpr
    refine ⟨?_, (hasSum_fintype _).summable⟩
    intro S
    exact giantSignedGhostPositivePairingBlock_birth_summable ν hν A C D f h F v hhc k S
  let g := giantSignedGhostGroupApply ν (A : ℂ) (C : ℂ) (D : ℂ) (fun m => (h m : ℂ))
  let F' := F * Real.exp (‖(C : ℂ)‖ * (∑ p : P, ν p) * v)
  let v' := v * max 1 (‖(A : ℂ)‖ + ‖(D : ℂ)‖ / v)
  have hg : ∀ m, ‖g m‖ ≤ F' * v' ^ m.1 :=
    giantSignedGhostGroupApply_exponential_bound ν hν (A : ℂ) (C : ℂ) (D : ℂ)
      (fun m => (h m : ℂ)) F v hF hv hhc
  have hv' : 0 ≤ v' := mul_nonneg hv.le (le_trans zero_le_one (le_max_left _ _))
  have hnorm := giantSignedGroupPairing_summable_norm ν hν
    (fun m => (f m : ℂ)) g B F' u v' hB
    (mul_nonneg hF (Real.exp_nonneg _)) hu hv' hfc hg
  have houter : Summable (fun k : ℕ => ∑ a : Fin k → GiantSignedParticle P,
      ‖(giantSignedGroupMemoryMass ν ⟨k, a⟩ : ℂ) * star (f ⟨k, a⟩ : ℂ) * g ⟨k, a⟩‖) := by
    simpa only [tsum_fintype] using
      ((summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mp hnorm).2
  apply (summable_sigma_of_nonneg hφ).mpr
  refine ⟨hinner, houter.of_nonneg_of_le (fun k => tsum_nonneg (fun s => hφ ⟨k, s⟩)) ?_⟩
  intro k
  have heq : ((∑' s : Finset (Fin k) × ℕ, φ ⟨k, s⟩ : ℝ) : ℂ) =
      ∑ a : Fin k → GiantSignedParticle P,
        (giantSignedGroupMemoryMass ν ⟨k, a⟩ : ℂ) * star (f ⟨k, a⟩ : ℂ) * g ⟨k, a⟩ := by
    rw [(hinner k).tsum_prod]
    simp only [tsum_fintype, Complex.ofReal_sum, Complex.ofReal_tsum]
    simp_rw [show ∀ S b, (φ ⟨k, S, b⟩ : ℂ) =
      giantSignedGhostRawPairingBlock ν (A : ℂ) (C : ℂ) (D : ℂ)
        (fun m => (f m : ℂ)) (fun m => (h m : ℂ)) ⟨k, S, b⟩ from
      fun S b => giantSignedGhostPositivePairingBlock_coe ν A C D f h ⟨k, S, b⟩]
    exact giantSignedGhostRawPairingBlock_source_degree ν hν (A : ℂ) (C : ℂ) (D : ℂ)
      (fun m => (f m : ℂ)) (fun m => (h m : ℂ)) F v hhc k
  have hn := congrArg norm heq
  rw [Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg (fun s => hφ ⟨k, s⟩))] at hn
  rw [hn]
  exact norm_sum_le _ _

theorem giantSignedGhostRawPairingBlock_summable_norm
    (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p) (A C D : ℂ)
    (f h : GiantSignedGroupMemory P → ℂ) (B F u v : ℝ)
    (hB : 0 ≤ B) (hF : 0 ≤ F) (hu : 0 ≤ u) (hv : 0 < v)
    (hf : ∀ m, ‖f m‖ ≤ B * u ^ m.1) (hh : ∀ m, ‖h m‖ ≤ F * v ^ m.1) :
    Summable (fun r => ‖giantSignedGhostRawPairingBlock ν A C D f h r‖) := by
  exact (giantSignedGhostPositivePairingBlock_summable ν hν ‖A‖ ‖C‖ ‖D‖
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (fun m => ‖f m‖) (fun m => ‖h m‖) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    B F u v hB hF hu hv hf hh).of_nonneg_of_le (fun _ => norm_nonneg _)
      (giantSignedGhostRawPairingBlock_norm_le ν hν A C D f h)

theorem giantSignedGhostRawPairingBlock_summable
    (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p) (A C D : ℂ)
    (f h : GiantSignedGroupMemory P → ℂ) (B F u v : ℝ)
    (hB : 0 ≤ B) (hF : 0 ≤ F) (hu : 0 ≤ u) (hv : 0 < v)
    (hf : ∀ m, ‖f m‖ ≤ B * u ^ m.1) (hh : ∀ m, ‖h m‖ ≤ F * v ^ m.1) :
    Summable (giantSignedGhostRawPairingBlock ν A C D f h) :=
  (giantSignedGhostRawPairingBlock_summable_norm ν hν A C D f h B F u v
    hB hF hu hv hf hh).of_norm

end
end ArtinMatthews

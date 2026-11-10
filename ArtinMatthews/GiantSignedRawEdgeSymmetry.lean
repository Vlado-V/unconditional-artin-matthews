module

public import ArtinMatthews.GiantSignedRawOldPermutation
public import ArtinMatthews.GiantSignedRawEdgeSplit
public import ArtinMatthews.GiantSignedEdgeTargetSymmetry
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

/-! The original raw edge and its literal clean/dirty restrictions preserve
pending-index symmetry. The transfer ban is retained on both sides. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedEdgeMoveCoefficient_old_permute
    {B : Type*} [Fintype B] [DecidableEq B] {P : B → Finset ℕ} {t : B → ℕ}
    (ν : ∀ g, P g → ℂ) (V : B → ℝ) (ρ : ℝ) (d : ℤ) (D : ℕ)
    (source target : GiantSignedPrimeTuple P t) (m : GiantSignedMemory P)
    (c : GiantSignedEdgeChoice t m.1) (σ : ∀ g, Equiv.Perm (Fin (m.1 g))) :
    giantSignedEdgeMoveCoefficient ν V ρ d D source target (giantSignedMemoryPermute m σ) c =
      giantSignedEdgeMoveCoefficient ν V ρ d D source target m
        (giantSignedEdgeOldChoiceEquiv σ c) := by
  rw [giantSignedEdgeOldChoiceEquiv_apply]
  have htarget : (giantSignedPendingDamping ρ
      (giantSignedEdgeTarget d (giantSignedMemoryPermute m σ) source c) : ℂ) =
      (giantSignedPendingDamping ρ (giantSignedEdgeTarget d m source
        ⟨c.1, c.2.1, fun g => giantSignedMovedPromotion (σ g) (c.2.2 g)⟩) : ℂ) :=
    giantSignedEdgeTarget_symmetric_test d m source c σ
    (fun out => (giantSignedPendingDamping ρ out : ℂ))
    (fun out τ => congrArg (fun x : ℝ => (x : ℂ)) (giantSignedPendingDamping_permute ρ out τ))
  unfold giantSignedEdgeMoveCoefficient
  rw [giantSignedEdgeHits_permute, giantSignedPendingDamping_permute, htarget]

variable {S B I : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [Fintype (GiantTwoSidedResidueState PS (k+ell))]

omit [Fintype (GiantTwoSidedResidueState PS (k+ell))] in
theorem giantSignedRawEdgeCoefficient_old_permute {C : B → Finset (Fin k)}
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell)
    (s : GiantSignedState PS PB (k+ell)) (σ : ∀ g, Equiv.Perm (Fin (s.2.2.1 g)))
    (r : GiantSignedRawEdgeMove PS PB ell C (giantSignedMemoryPermute s.2.2 σ)) :
    giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ K
        (s.1,s.2.1,giantSignedMemoryPermute s.2.2 σ) r =
      giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ K s (giantSignedRawEdgeOldEquiv s.2.2 σ r) := by
  unfold giantSignedRawEdgeCoefficient
  have hcondition := giantSignedRawEdgeOldEquiv_condition κ s σ r
  by_cases h : GiantSignedRawEdgeCondition κ (s.1,s.2.1,giantSignedMemoryPermute s.2.2 σ) r
  · rw [if_pos h, if_pos (hcondition.mp h)]
    congr 1
    exact giantSignedEdgeMoveCoefficient_old_permute (fun g p => (ν g p : ℂ)) V ρ
      (κ * (giantSignedRawEdgeProduct (s.1,s.2.1,giantSignedMemoryPermute s.2.2 σ) r : ℤ))
      (giantSignedRawEdgeProduct (s.1,s.2.1,giantSignedMemoryPermute s.2.2 σ) r)
      (giantSignedPatternFreeLabels C (giantSignedRawEdgeBigSource
        (s.1,s.2.1,giantSignedMemoryPermute s.2.2 σ) r))
      (giantSignedPatternFreeLabels C r.bigTarget) s.2.2 r.choice σ
  · rw [if_neg h, if_neg (mt hcondition.mpr h)]

theorem giantSignedRawEdgeApply_symmetric_of_equivariant {C : B → Finset (Fin k)}
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell)
    (η : (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell C s.2.2 → ℂ)
    (hη : ∀ (s : GiantSignedState PS PB (k+ell)) (σ : ∀ g, Equiv.Perm (Fin (s.2.2.1 g)))
      (r : GiantSignedRawEdgeMove PS PB ell C (giantSignedMemoryPermute s.2.2 σ)),
      η (s.1,s.2.1,giantSignedMemoryPermute s.2.2 σ) r =
        η s (giantSignedRawEdgeOldEquiv s.2.2 σ r))
    (f : GiantSignedState PS PB (k+ell) → ℂ)
    (hf : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m))) :
    ∀ s a, GiantSignedMemorySymmetric (fun m => giantSignedRawEdgeApply ν V κ q ρ θ ζ K η f (s,a,m)) := by
  intro z a m σ
  change giantSignedRawEdgeApply ν V κ q ρ θ ζ K η f (z,a,giantSignedMemoryPermute m σ) =
    giantSignedRawEdgeApply ν V κ q ρ θ ζ K η f (z,a,m)
  unfold giantSignedRawEdgeApply
  conv_rhs => rw [← (giantSignedRawEdgeOldEquiv (PS := PS) (C := C) m σ).sum_comp]
  apply Finset.sum_congr rfl
  intro r _
  rw [giantSignedRawEdgeCoefficient_old_permute ν V κ q ρ θ ζ K (z,a,m) σ r,
    hη (z,a,m) σ r, giantSignedRawEdgeOldEquiv_target_test κ (z,a,m) σ r f hf]

theorem giantSignedRawEdgeApply_symmetric {C : B → Finset (Fin k)}
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell)
    (f : GiantSignedState PS PB (k+ell) → ℂ)
    (hf : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m))) :
    ∀ s a, GiantSignedMemorySymmetric
      (fun m => giantSignedRawEdgeApply ν V κ q ρ θ ζ K (fun _ _ => 1) f (s,a,m)) :=
  giantSignedRawEdgeApply_symmetric_of_equivariant ν V κ q ρ θ ζ K (fun _ _ => 1)
    (fun _ _ _ => rfl) f hf

theorem giantSignedRawEdgeApply_clean_symmetric {C : B → Finset (Fin k)}
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell)
    (f : GiantSignedState PS PB (k+ell) → ℂ)
    (hf : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m))) :
    ∀ s a, GiantSignedMemorySymmetric
      (fun m => giantSignedRawEdgeApply ν V κ q ρ θ ζ K giantSignedRawEdgeCleanMultiplier f (s,a,m)) :=
  giantSignedRawEdgeApply_symmetric_of_equivariant ν V κ q ρ θ ζ K giantSignedRawEdgeCleanMultiplier
    (fun _ _ _ => rfl) f hf

theorem giantSignedRawEdgeApply_dirty_symmetric {C : B → Finset (Fin k)}
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell)
    (f : GiantSignedState PS PB (k+ell) → ℂ)
    (hf : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m))) :
    ∀ s a, GiantSignedMemorySymmetric
      (fun m => giantSignedRawEdgeApply ν V κ q ρ θ ζ K giantSignedRawEdgeDirtyMultiplier f (s,a,m)) :=
  giantSignedRawEdgeApply_symmetric_of_equivariant ν V κ q ρ θ ζ K giantSignedRawEdgeDirtyMultiplier
    (fun _ _ _ => rfl) f hf

theorem giantSignedRawEdgeFamilyApply_symmetric_of_equivariant
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (η : (i : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i) s.2.2 → ℂ)
    (hη : ∀ i ∈ patterns, ∀ (s : GiantSignedState PS PB (k+ell))
      (σ : ∀ g, Equiv.Perm (Fin (s.2.2.1 g)))
      (r : GiantSignedRawEdgeMove PS PB ell (C i) (giantSignedMemoryPermute s.2.2 σ)),
      η i (s.1,s.2.1,giantSignedMemoryPermute s.2.2 σ) r =
        η i s (giantSignedRawEdgeOldEquiv s.2.2 σ r))
    (f : GiantSignedState PS PB (k+ell) → ℂ)
    (hf : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m))) :
    ∀ s a, GiantSignedMemorySymmetric
      (fun m => giantSignedRawEdgeFamilyApply ν V patterns C κ q ρ θ ζ K η f (s,a,m)) := by
  intro s a m σ
  unfold giantSignedRawEdgeFamilyApply
  exact Finset.sum_congr rfl (fun i hi =>
    giantSignedRawEdgeApply_symmetric_of_equivariant ν V κ q ρ θ ζ (K i) (η i) (hη i hi) f hf s a m σ)

theorem giantSignedRawEdgeFamilyApply_symmetric
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (f : GiantSignedState PS PB (k+ell) → ℂ)
    (hf : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m))) :
    ∀ s a, GiantSignedMemorySymmetric
      (fun m => giantSignedRawEdgeFamilyApply ν V patterns C κ q ρ θ ζ K (fun _ _ _ => 1) f (s,a,m)) :=
  giantSignedRawEdgeFamilyApply_symmetric_of_equivariant ν V patterns C κ q ρ θ ζ K
    (fun _ _ _ => 1) (fun _ _ _ _ _ => rfl) f hf

end
end ArtinMatthews

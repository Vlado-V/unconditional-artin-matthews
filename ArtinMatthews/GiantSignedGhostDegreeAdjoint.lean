module

public import ArtinMatthews.GiantSignedGhostJoint
public import ArtinMatthews.GiantSignedGhostCounts
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

/-! The finite degree blocks of the actual ghost pairing, including its
factorial adjoint. Birth and termination coefficients are exchanged. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {P : Finset ℕ} [∀ p : P, NeZero p.val]

omit [∀ p : P, NeZero p.val] in
theorem giantSignedGhost_survivor_zero_count_cast {k n t : ℕ}
    (a : Fin k → GiantSignedParticle P) (S : Finset (Fin k))
    (ht : S.card = t) (hn : (Sᶜ).card = n)
    (hzero : ∀ i, (markedRawDeletedTupleCast S ht a i).2 = 0) :
    giantSignedGroupZeroCount (markedRawSurvivorTupleCast S hn a) =
      giantSignedGroupZeroCount a - t := by
  cases ht
  cases hn
  simp only [markedRawDeletedTupleCast] at hzero
  exact giantSignedGhost_survivor_zero_count a S
    ((giantSignedGhost_deleted_zero_iff a S).mp hzero)

def giantSignedGhostJointBlock (ν : P → ℝ) (A C D : ℂ) (n t b : ℕ)
    (f : (Fin (n+t) → GiantSignedParticle P) → ℂ)
    (h : (Fin (n+b) → GiantSignedParticle P) → ℂ) : ℂ :=
  ∑ u : Fin n → GiantSignedParticle P, ∑ α : Fin t → P, ∑ β : Fin b → P,
    ((∏ i, (ν (u i).1 : ℂ)) / (Nat.factorial n : ℂ)) *
      ((∏ i, (ν (α i) : ℂ)) / (Nat.factorial t : ℂ)) *
      ((∏ i, (ν (β i) : ℂ)) / (Nat.factorial b : ℂ)) *
      A ^ giantSignedGroupZeroCount u * D ^ t * C ^ b *
      star (f (Fin.append u (giantSignedZeroTuple α))) *
      h (Fin.append u (giantSignedZeroTuple β))

def giantSignedGhostDegreePairing (ν : P → ℝ) (A C D : ℂ) (n t b : ℕ)
    (f : (Fin (n+t) → GiantSignedParticle P) → ℂ)
    (h : (Fin (n+b) → GiantSignedParticle P) → ℂ) : ℂ :=
  ∑ a : Fin (n+t) → GiantSignedParticle P,
    ((∏ i, (ν (a i).1 : ℂ)) / (Nat.factorial (n+t) : ℂ)) * star (f a) *
      ∑ S : MarkedRawDeletionBatch (n+t) t,
        let deleted := markedRawDeletedTupleCast S.1 (markedRawDeletionBatch_deleted_card S) a
        let u := markedRawSurvivorTupleCast S.1 (markedRawDeletionBatch_survivor_card rfl S) a
        if ∀ i, (deleted i).2 = 0 then
          A ^ giantSignedGroupZeroCount u * D ^ t * (C ^ b / (Nat.factorial b : ℂ)) *
            ∑ β : Fin b → P, (∏ i, (ν (β i) : ℂ)) * h (Fin.append u (giantSignedZeroTuple β))
        else 0

theorem giantSignedGhostDegreePairing_original (ν : P → ℝ) (A C D : ℂ) (n t b : ℕ)
    (f : (Fin (n+t) → GiantSignedParticle P) → ℂ)
    (h : (Fin (n+b) → GiantSignedParticle P) → ℂ) :
    giantSignedGhostDegreePairing ν A C D n t b f h =
      ∑ a : Fin (n+t) → GiantSignedParticle P,
        ((∏ i, (ν (a i).1 : ℂ)) / (Nat.factorial (n+t) : ℂ)) * star (f a) *
          ∑ S : MarkedRawDeletionBatch (n+t) t,
            let deleted := markedRawDeletedTupleCast S.1 (markedRawDeletionBatch_deleted_card S) a
            let u := markedRawSurvivorTupleCast S.1 (markedRawDeletionBatch_survivor_card rfl S) a
            if ∀ i, (deleted i).2 = 0 then
              A ^ (giantSignedGroupZeroCount a - t) * D ^ t * (C ^ b / (Nat.factorial b : ℂ)) *
                ∑ β : Fin b → P, (∏ i, (ν (β i) : ℂ)) * h (Fin.append u (giantSignedZeroTuple β))
            else 0 := by
  classical
  unfold giantSignedGhostDegreePairing
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  apply Finset.sum_congr rfl
  intro S _
  dsimp only
  split_ifs with hz
  · rw [giantSignedGhost_survivor_zero_count_cast a S.1
      (markedRawDeletionBatch_deleted_card S) (markedRawDeletionBatch_survivor_card rfl S) hz]
  · rfl

theorem giantSignedGhostDegreePairing_eq_joint (ν : P → ℝ) (A C D : ℂ) (n t b : ℕ)
    (f : (Fin (n+t) → GiantSignedParticle P) → ℂ)
    (hf : MarkedRawTupleSymmetric (n+t) f)
    (h : (Fin (n+b) → GiantSignedParticle P) → ℂ) :
    giantSignedGhostDegreePairing ν A C D n t b f h =
      giantSignedGhostJointBlock ν A C D n t b f h := by
  classical
  unfold giantSignedGhostDegreePairing
  rw [giantSignedGhost_fixed_joint (fun p => (ν p : ℂ)) n t (fun a => star (f a))
    (fun a σ => congrArg star (hf a σ))
    (fun _ u => A ^ giantSignedGroupZeroCount u * D ^ t * (C ^ b / (Nat.factorial b : ℂ)) *
      ∑ β : Fin b → P, (∏ i, (ν (β i) : ℂ)) * h (Fin.append u (giantSignedZeroTuple β)))]
  unfold giantSignedGhostJointBlock
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  ring

theorem giantSignedGhostJointBlock_conjugate_swap (ν : P → ℝ) (A C D : ℂ) (n t b : ℕ)
    (f : (Fin (n+t) → GiantSignedParticle P) → ℂ)
    (h : (Fin (n+b) → GiantSignedParticle P) → ℂ) :
    giantSignedGhostJointBlock ν A C D n t b f h =
      star (giantSignedGhostJointBlock ν (star A) (star D) (star C) n b t h f) := by
  classical
  unfold giantSignedGhostJointBlock
  simp only [star_sum, star_mul, star_div₀, star_pow, star_prod, star_natCast, star_star]
  simp only [Complex.star_def, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  ring

theorem giantSignedGhostDegreePairing_adjoint (ν : P → ℝ) (A C D : ℂ) (n t b : ℕ)
    (f : (Fin (n+t) → GiantSignedParticle P) → ℂ)
    (hf : MarkedRawTupleSymmetric (n+t) f)
    (h : (Fin (n+b) → GiantSignedParticle P) → ℂ)
    (hh : MarkedRawTupleSymmetric (n+b) h) :
    giantSignedGhostDegreePairing ν A C D n t b f h =
      star (giantSignedGhostDegreePairing ν (star A) (star D) (star C) n b t h f) := by
  rw [giantSignedGhostDegreePairing_eq_joint ν A C D n t b f hf h,
    giantSignedGhostDegreePairing_eq_joint ν (star A) (star D) (star C) n b t h hh f]
  exact giantSignedGhostJointBlock_conjugate_swap ν A C D n t b f h

theorem giantSignedGhostSourceDegreePairing_adjoint (ν : P → ℝ) (V q ρ : ℝ) (n t b : ℕ)
    (f : (Fin (n+t) → GiantSignedParticle P) → ℂ)
    (hf : MarkedRawTupleSymmetric (n+t) f)
    (h : (Fin (n+b) → GiantSignedParticle P) → ℂ)
    (hh : MarkedRawTupleSymmetric (n+b) h) :
    giantSignedGhostDegreePairing ν ((q / ρ ^ 2 : ℝ) : ℂ)
      ((-(1-q) * V / ρ : ℝ) : ℂ) ((-(1-q) / ρ : ℝ) : ℂ) n t b f h =
      star (giantSignedGhostDegreePairing ν ((q / ρ ^ 2 : ℝ) : ℂ)
        ((-(1-q) / ρ : ℝ) : ℂ) ((-(1-q) * V / ρ : ℝ) : ℂ) n b t h f) := by
  simpa only [Complex.star_def, Complex.conj_ofReal] using
    giantSignedGhostDegreePairing_adjoint ν ((q / ρ ^ 2 : ℝ) : ℂ)
      ((-(1-q) * V / ρ : ℝ) : ℂ) ((-(1-q) / ρ : ℝ) : ℂ) n t b f hf h hh

end
end ArtinMatthews

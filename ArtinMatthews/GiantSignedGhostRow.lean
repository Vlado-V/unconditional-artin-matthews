module

public import ArtinMatthews.GiantSignedMemoryState
public import ArtinMatthews.MarkedMinorArcRawMemoryBulkIndices
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Ring.IsFormallyReal
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

/-! The actual indexed ghost row deletes only old zero residues, then
appends the ordered fresh zero-residue batch. Numerical coincidences are retained. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

abbrev GiantSignedGroupMemory (P : Finset ℕ) := Σ n : ℕ, Fin n → GiantSignedParticle P

instance giantSignedParticle_fintype (P : Finset ℕ) [∀ p : P, NeZero p.val] :
    Fintype (GiantSignedParticle P) := by
  classical
  letI : ∀ p : P, Fintype (ZMod p.val) := fun p => by
    let : NeZero p.val := ‹∀ p : P, NeZero p.val› p
    infer_instance
  change Fintype (Σ p : P, ZMod p.val)
  infer_instance

def giantSignedGhostZeroIndices {P : Finset ℕ} (m : GiantSignedGroupMemory P) :
    Finset (Fin m.1) := by
  classical
  exact Finset.univ.filter (fun i => (m.2 i).2 = 0)

def giantSignedGhostTarget {P : Finset ℕ} (m : GiantSignedGroupMemory P)
    (deleted : Finset (Fin m.1)) {b : ℕ} (born : Fin b → P) : GiantSignedGroupMemory P :=
  ⟨(deletedᶜ).card + b,
    Fin.append (markedRawSubsetTupleEquiv deleted m.2).2 (fun i => ⟨born i, 0⟩)⟩

theorem giantSignedGhostTarget_degree {P : Finset ℕ} (m : GiantSignedGroupMemory P)
    (deleted : Finset (Fin m.1)) {b : ℕ} (born : Fin b → P) :
    (giantSignedGhostTarget m deleted born).1 = m.1 - deleted.card + b := by
  classical
  change (deletedᶜ).card + b = _
  rw [Finset.card_compl, Fintype.card_fin]

theorem giantSignedGhostTarget_survivor {P : Finset ℕ} (m : GiantSignedGroupMemory P)
    (deleted : Finset (Fin m.1)) {b : ℕ} (born : Fin b → P) (i : Fin (deletedᶜ).card) :
    (giantSignedGhostTarget m deleted born).2 (Fin.castAdd b i) =
      m.2 ((deletedᶜ).orderEmbOfFin rfl i) := by
  simp only [giantSignedGhostTarget, Fin.append_left, markedRawSubsetTupleEquiv_survivor]

theorem giantSignedGhostTarget_born {P : Finset ℕ} (m : GiantSignedGroupMemory P)
    (deleted : Finset (Fin m.1)) {b : ℕ} (born : Fin b → P) (i : Fin b) :
    (giantSignedGhostTarget m deleted born).2 (Fin.natAdd (deletedᶜ).card i) =
      ⟨born i, 0⟩ := by
  simp only [giantSignedGhostTarget, Fin.append_right]

def giantSignedGhostGroupApply {P : Finset ℕ} (ν : P → ℝ)
    (A C D : ℂ) (f : GiantSignedGroupMemory P → ℂ) (m : GiantSignedGroupMemory P) : ℂ :=
  ∑ deleted ∈ (giantSignedGhostZeroIndices m).powerset,
    D ^ deleted.card * A ^ ((giantSignedGhostZeroIndices m).card - deleted.card) *
      ∑' b : ℕ, (C ^ b / (Nat.factorial b : ℂ)) *
        ∑ born : Fin b → P, (∏ i, (ν (born i) : ℂ)) * f (giantSignedGhostTarget m deleted born)

def giantSignedGhostGroup {P : Finset ℕ} (ν : P → ℝ) (V q ρ : ℝ)
    (f : GiantSignedGroupMemory P → ℂ) : GiantSignedGroupMemory P → ℂ :=
  giantSignedGhostGroupApply ν ((q / ρ ^ 2 : ℝ) : ℂ)
    ((-(1-q) * V / ρ : ℝ) : ℂ) ((-(1-q) / ρ : ℝ) : ℂ) f

theorem giantSignedGhost_birthMass {P : Finset ℕ} (ν : P → ℝ) (b : ℕ) :
    (∑ born : Fin b → P, ∏ i, ν (born i)) = (∑ p : P, ν p) ^ b :=
  (Fintype.sum_pow ν b).symm

theorem giantSignedGhost_degree_weight {P : Finset ℕ} (m : GiantSignedGroupMemory P)
    (deleted : Finset (Fin m.1)) {b : ℕ} (born : Fin b → P)
    {v : ℝ} (hv : v ≠ 0) :
    v ^ (giantSignedGhostTarget m deleted born).1 / v ^ m.1 = v ^ b / v ^ deleted.card := by
  rw [giantSignedGhostTarget_degree]
  apply (div_eq_div_iff (pow_ne_zero _ hv) (pow_ne_zero _ hv)).mpr
  rw [← pow_add, ← pow_add]
  congr 1
  have hc : deleted.card ≤ m.1 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ deleted)
  omega

end
end ArtinMatthews

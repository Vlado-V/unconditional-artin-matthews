module

public import ArtinMatthews.MarkedMinorArcRawGhostSymmetryIndices
public import ArtinMatthews.MarkedMinorArcRawGhostAction
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! The literal cutoff, signed coefficient and appended target memory
commute with old pending-index permutations, up to target symmetry. -/
noncomputable section
open scoped BigOperators
namespace ArtinMatthews

def markedRawGhostBirthSizesPermuteEquiv {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j : ℕ))) (del : MarkedRawGhostDeletion m) :
    MarkedRawGhostBirthSizes m del ≃
      MarkedRawGhostBirthSizes (markedRawMemoryPermute m σ) (markedRawGhostDeletionPermute m σ del) where
  toFun l := ⟨l.1,by simpa only [markedRawGhostSurvivors_permute_card] using l.2⟩
  invFun l := ⟨l.1,by simpa only [markedRawGhostSurvivors_permute_card] using l.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem markedRawGhostSignedCoefficient_permute {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (V : J → ℝ) (qStage ρ : ℝ)
    (m : MarkedRawMemory P B) (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j : ℕ)))
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (del : MarkedRawGhostDeletion m)
    (l : MarkedRawGhostBirthSizes m del) :
    markedRawGhostSignedCoefficient V qStage ρ (markedRawMemoryPermute m σ) z hz
      (markedRawGhostDeletionPermute m σ del) (markedRawGhostBirthSizesPermuteEquiv m σ del l) =
      markedRawGhostSignedCoefficient V qStage ρ m z hz del l := by
  unfold markedRawGhostSignedCoefficient
  apply Finset.prod_congr rfl
  intro j _
  rw [markedRawGhostDeletionPermute_card, markedRawGhostHitIndices_permute]
  change _ * (qStage/ρ^2)^((_ \ (del j).map (σ j).symm.toEmbedding).card) * _ = _
  rw [← Finset.map_sdiff, Finset.card_map]
  rfl

/-- Birth indices and labels remain unchanged; their factorial measure is
therefore literally the same, including repeated numeric birth values. -/
theorem markedRawGhostBirthMass_permute {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (ν : (j : J) → ↥(P j) → ℝ)
    (m : MarkedRawMemory P B) (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j : ℕ)))
    (del : MarkedRawGhostDeletion m) (l : MarkedRawGhostBirthSizes m del)
    (births : MarkedRawGhostBirthLabels l) :
    markedRawGhostBirthMass ν (markedRawGhostBirthSizesPermuteEquiv m σ del l) births =
      markedRawGhostBirthMass ν l births := rfl

def markedRawGhostAppendIndexEquiv {r r' l : ℕ} (e : Fin r' ≃ Fin r) :
    Fin (r'+l) ≃ Fin (r+l) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr e (Equiv.refl (Fin l))).trans finSumFinEquiv)

theorem markedRawGhostAppendIndexEquiv_values {X : Type*} {r r' l : ℕ}
    (e : Fin r' ≃ Fin r) (a' : Fin r' → X) (a : Fin r → X)
    (b : Fin l → X) (ha : ∀ i, a' i=a (e i)) (i : Fin (r'+l)) :
    (Fin.addCases a' b i : X) = (Fin.addCases a b (markedRawGhostAppendIndexEquiv e i) : X) := by
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · simpa only [markedRawGhostAppendIndexEquiv, Equiv.trans_apply,
      finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply, Sum.map_inl,
      finSumFinEquiv_apply_left, Fin.addCases_left] using ha k
  · simp only [markedRawGhostAppendIndexEquiv, Equiv.trans_apply,
      finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply, Sum.map_inr,
      Equiv.refl_apply, finSumFinEquiv_apply_right, Fin.addCases_right]

/-- Canonically reordered old survivors induce a true target-index
equivalence; the appended ordered birth block is fixed pointwise. -/
theorem markedRawGhostTargetMemory_symmetric_permute {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (f : MarkedRawMemory P B → ℂ)
    (hf : MarkedRawMemorySymmetric f)
    (m : MarkedRawMemory P B) (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j : ℕ)))
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (del : MarkedRawGhostDeletion m)
    (l : MarkedRawGhostBirthSizes m del) (births : MarkedRawGhostBirthLabels l) :
    f (markedRawGhostTargetMemory (markedRawMemoryPermute m σ) z hz
      (markedRawGhostDeletionPermute m σ del) (markedRawGhostBirthSizesPermuteEquiv m σ del l) births) =
      f (markedRawGhostTargetMemory m z hz del l births) := by
  apply markedRawMemorySymmetric_equiv hf
    (markedRawGhostTargetMemory m z hz del l births) _
    (fun j => markedRawGhostAppendIndexEquiv (l := (l.1 j : ℕ))
      (markedRawGhostSurvivorIndexEquiv (σ j) (del j)))
  intro j i
  dsimp only [markedRawGhostTargetMemory]
  apply markedRawGhostAppendIndexEquiv_values
  intro k
  change m.2 j (σ j ((Finset.univ \ (del j).map (σ j).symm.toEmbedding).orderEmbOfFin rfl k)) =
    m.2 j ((Finset.univ \ del j).orderEmbOfFin rfl (markedRawGhostSurvivorIndexEquiv (σ j) (del j) k))
  exact congrArg (m.2 j) (markedRawGhostSurvivorIndexEquiv_apply (σ j) (del j) k).symm

end ArtinMatthews

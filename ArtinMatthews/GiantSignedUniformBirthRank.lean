module

public import ArtinMatthews.GiantSignedUniformBirthFrame
public import ArtinMatthews.GiantSignedBirthFourier
public import ArtinMatthews.MarkedBirthDistinctWeighted
public import ArtinMatthews.MarkedBirthRankCount
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

/-! Distinctness restoration uses one fixed frame across every pattern.
Only the values and performed flags vary with the chronological choices. -/
namespace ArtinMatthews
open MeasureTheory
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

variable {B : Type*} [Fintype B] {P : B → Finset ℕ} {k ell n H : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}

local instance giantSignedUniformBirthPermutationFintype {M N T : ℕ} :
    Fintype (Equiv.Perm (GiantSignedUniformBirthAddress B M N T)) :=
  @Equiv.instFintype (GiantSignedUniformBirthAddress B M N T)
    (GiantSignedUniformBirthAddress B M N T)
    inferInstance inferInstance inferInstance inferInstance

def giantSignedUniformBirthOperation (M N T : ℕ) :
    GiantSignedUniformBirthAddress B M N T → GiantSignedBirthOperation N
  | .inl _ => .initial
  | .inr (.inl a) => .edge a.1
  | .inr (.inr a) => .visit a.1

theorem giantSignedUniformBirthDistinct_weighted_sum
    (d : GiantSignedBirthData P ell C batch) (hH : ∀ i g, batch i g ≤ H) (z : ℂ) :
    (if GiantSignedBirthDistinct d then z else 0) =
      ∑ σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H),
        ((σ.sign : ℤ) : ℂ) *
          (if MarkedBirthPermutationEvent (giantSignedUniformBirthValue d H hH) σ then z else 0) := by
  rw [giantSignedBirthDistinct_iff_uniform d H hH]
  have h := markedBirthDistinct_weighted_permutation_sum
    (fun _ : Unit => giantSignedUniformBirthValue d H hH) (fun _ : Unit => z)
  simpa using h

theorem giantSignedUniformBirth_operations_le
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H)) :
    (σ.support.image (giantSignedUniformBirthOperation (k+ell) n H)).card ≤
      2 * markedBirthPermutationRank σ :=
  markedBirthPermutation_operations_le_twice_rank _ σ

theorem giantSignedUniformBirth_rank_card (r : ℕ) :
    Fintype.card {σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H) //
      markedBirthPermutationRank σ = r} ≤
      ((((n+1) * Fintype.card B * (k+ell+H)) ^ 2) + 1) ^ (2*r) := by
  have h := markedBirthPermutation_rank_card_bound
    (A := GiantSignedUniformBirthAddress B (k+ell) n H) r
  rw [giantSignedUniformBirthAddress_card] at h
  simpa only [pow_two] using h

theorem giantSignedUniformBirth_event_integral (d : GiantSignedBirthData P ell C batch)
    (hH : ∀ i g, batch i g ≤ H)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H)) :
    (∫ θ : GiantSignedUniformBirthAddress B (k+ell) n H → AddCircle (1 : ℝ),
      giantSignedBirthPermutationPhase (giantSignedUniformBirthValue d H hH) σ θ
        ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) =
      if MarkedBirthPermutationEvent (giantSignedUniformBirthValue d H hH) σ then 1 else 0 :=
  giantSignedBirthPermutationPhase_integral _ σ

def giantSignedUniformBirthOperationMultiplier (d : GiantSignedBirthData P ell C batch)
    (hH : ∀ i g, batch i g ≤ H)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H))
    (θ : GiantSignedUniformBirthAddress B (k+ell) n H → AddCircle (1 : ℝ))
    (o : GiantSignedBirthOperation n) : ℂ :=
  ∏ a : GiantSignedUniformBirthAddress B (k+ell) n H,
    if giantSignedUniformBirthOperation (k+ell) n H a = o then
      giantSignedBirthLocalMultiplier σ θ a (giantSignedUniformBirthValue d H hH a) else 1

theorem giantSignedUniformBirthOperationMultiplier_norm_le
    (d : GiantSignedBirthData P ell C batch) (hH : ∀ i g, batch i g ≤ H)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H))
    (θ : GiantSignedUniformBirthAddress B (k+ell) n H → AddCircle (1 : ℝ))
    (o : GiantSignedBirthOperation n) :
    ‖giantSignedUniformBirthOperationMultiplier d hH σ θ o‖ ≤ 1 := by
  rw [giantSignedUniformBirthOperationMultiplier, norm_prod]
  apply Finset.prod_le_one₀
  · intro a _
    exact norm_nonneg _
  · intro a _
    split_ifs
    · exact giantSignedBirthLocalMultiplier_norm_le _ _ _ _
    · simp

theorem giantSignedUniformBirthOperationMultiplier_unaffected
    (d : GiantSignedBirthData P ell C batch) (hH : ∀ i g, batch i g ≤ H)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H))
    (θ : GiantSignedUniformBirthAddress B (k+ell) n H → AddCircle (1 : ℝ))
    (o : GiantSignedBirthOperation n)
    (ho : o ∉ σ.support.image (giantSignedUniformBirthOperation (k+ell) n H)) :
    giantSignedUniformBirthOperationMultiplier d hH σ θ o = 1 := by
  apply Finset.prod_eq_one
  intro a _
  split_ifs with ha
  · have hn : a ∉ σ.support := fun h => ho (Finset.mem_image.mpr ⟨a, h, ha⟩)
    exact ite_eq_right hn
  · rfl

theorem giantSignedUniformBirth_phase_operations
    (d : GiantSignedBirthData P ell C batch) (hH : ∀ i g, batch i g ≤ H)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H))
    (θ : GiantSignedUniformBirthAddress B (k+ell) n H → AddCircle (1 : ℝ)) :
    giantSignedBirthPermutationPhase (giantSignedUniformBirthValue d H hH) σ θ =
      ∏ o : GiantSignedBirthOperation n, giantSignedUniformBirthOperationMultiplier d hH σ θ o := by
  rw [giantSignedBirthPermutationPhase_local]
  unfold giantSignedUniformBirthOperationMultiplier
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro a _
  simp

end
end ArtinMatthews

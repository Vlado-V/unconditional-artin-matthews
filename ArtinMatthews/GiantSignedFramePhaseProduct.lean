module

public import ArtinMatthews.GiantSignedLocalBirthPhase
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

/-! A fixed trace's Fourier factor is the product of its exact initial,
visit and edge birth factors on the common frame. -/
namespace ArtinMatthews
open MeasureTheory
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.decEq

private def giantSignedBirthOperationEquiv (n : ℕ) :
    (Unit ⊕ (Fin n ⊕ Fin (n+1))) ≃ GiantSignedBirthOperation n where
  toFun := fun
    | .inl _ => .initial
    | .inr (.inl i) => .edge i
    | .inr (.inr i) => .visit i
  invFun := fun
    | .initial => .inl ()
    | .edge i => .inr (.inl i)
    | .visit i => .inr (.inr i)
  left_inv := by
    rintro (j | i | i)
    · cases j
      rfl
    · rfl
    · rfl
  right_inv := by intro i; cases i <;> rfl

private theorem giantSignedBirthOperation_prod {n : ℕ} (F : GiantSignedBirthOperation n → ℂ) :
    (∏ i, F i) = F .initial * ((∏ i : Fin n, F (.edge i)) * ∏ i : Fin (n+1), F (.visit i)) := by
  rw [← (giantSignedBirthOperationEquiv n).prod_comp F,
    Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_unique]
  rfl

variable {B : Type*} [Fintype B] {P : B → Finset ℕ} {k ell n H : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}

theorem giantSignedFramePhaseProduct_eq (d : GiantSignedBirthData P ell C batch)
    (hH : ∀ i g, batch i g ≤ H)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H))
    (θ : GiantSignedUniformBirthAddress B (k+ell) n H → AddCircle (1 : ℝ)) :
    giantSignedInitialFramePhase σ θ d.initial *
      ((∏ i, giantSignedVisitFramePhase σ θ i (batch i) (d.born i)) *
        ∏ i, giantSignedEdgeFramePhase σ θ i (d.target i) (d.promoted i)) =
      giantSignedBirthPermutationPhase (giantSignedUniformBirthValue d H hH) σ θ := by
  rw [giantSignedUniformBirth_phase_operations d hH, giantSignedBirthOperation_prod]
  simp_rw [giantSignedInitialFramePhase_eq d hH, giantSignedVisitFramePhase_eq d hH,
    giantSignedEdgeFramePhase_eq d hH]
  ac_rfl

theorem giantSignedBirthPermutationPhase_continuous {A : Type*} [Fintype A] [DecidableEq A]
    (p : A → Option ℕ) (σ : Equiv.Perm A) :
    Continuous (fun θ : A → AddCircle (1 : ℝ) => giantSignedBirthPermutationPhase p σ θ) := by
  have hv (a : Option ℕ) :
      Continuous (fun θ : AddCircle (1 : ℝ) => giantSignedBirthValuePhase θ a) := by
    cases a with
    | none => exact continuous_const
    | some a => exact (fourier (a : ℤ)).continuous
  unfold giantSignedBirthPermutationPhase
  exact continuous_finsetProd _ (fun a _ => by
    by_cases ha : σ a = a
    · simp only [ha, ite_true]
      exact continuous_const
    · simp only [ha, ite_false]
      exact ((hv (p (σ a))).comp (continuous_apply a)).mul (((hv (p a)).comp (continuous_apply a)).star))

theorem giantSignedBirthPermutationPhase_integrable {A : Type*} [Fintype A] [DecidableEq A]
    (p : A → Option ℕ) (σ : Equiv.Perm A) :
    Integrable (fun θ : A → AddCircle (1 : ℝ) => giantSignedBirthPermutationPhase p σ θ)
      (Measure.pi (fun _ => AddCircle.haarAddCircle)) :=
  (giantSignedBirthPermutationPhase_continuous p σ).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end
end ArtinMatthews

module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.Normed.Function.Holder.C2HolderBanach
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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.UniformSpace.Uniformizable
public import OAI.Analysis.Normed.Function.Holder.Banach.Maps
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The closed Banach space of Hölder data supported in a fixed ball. -/

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped BoundedContinuousFunction
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

def supportedHolderSubmodule (m : ℕ) (α R : ℝ) :
    Submodule ℝ (OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α) where
  carrier := {f | ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value f x = 0}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg x hx; simp [hf x hx, hg x hx]
  smul_mem' := by intro c f hf x hx; simp [hf x hx]

abbrev SupportedHolder (m : ℕ) (α R : ℝ) := ↥(supportedHolderSubmodule m α R)

instance instSupportedHolderNormedGroup (m : ℕ) (α R : ℝ) :
    NormedAddCommGroup (SupportedHolder m α R) := inferInstance

instance instSupportedHolderNormedSpace (m : ℕ) (α R : ℝ) :
    NormedSpace ℝ (SupportedHolder m α R) := inferInstance

theorem isClosed_supportedHolderSubmodule (m : ℕ) (α R : ℝ) :
    IsClosed (supportedHolderSubmodule m α R : Set (OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)) := by
  change IsClosed {f : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α |
    ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value f x = 0}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro _hx
  exact isClosed_eq ((OAI.Analysis.Normed.Function.Holder.boundedEvaluation x).continuous.comp OAI.Analysis.Normed.Function.Holder.HolderMap.valueCLM.continuous) continuous_const

instance (m : ℕ) (α R : ℝ) : CompleteSpace (SupportedHolder m α R) :=
  (isClosed_supportedHolderSubmodule m α R).isComplete.completeSpace_coe

namespace SupportedHolder

variable {m : ℕ} {α R : ℝ}

def value (f : SupportedHolder m α R) : EuclideanSpace ℝ (Fin m) → ℝ :=
  OAI.Analysis.Normed.Function.Holder.HolderMap.value f.val

theorem continuous (f : SupportedHolder m α R) : Continuous (SupportedHolder.value f) :=
  (OAI.Analysis.Normed.Function.Holder.HolderMap.value f.val).continuous

theorem support_subset (f : SupportedHolder m α R) :
    Function.support (SupportedHolder.value f) ⊆ closedBall 0 R := by
  intro x hx
  by_contra hc
  exact hx (f.property x hc)

theorem hasCompactSupport (f : SupportedHolder m α R) : HasCompactSupport (SupportedHolder.value f) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 R) (SupportedHolder.support_subset f)

theorem support_subset_ball (f : SupportedHolder m α R) :
    Function.support (SupportedHolder.value f) ⊆ ball 0 (R + 1) :=
  (SupportedHolder.support_subset f).trans (closedBall_subset_ball (by linarith))

theorem norm_value_le (f : SupportedHolder m α R) (x) : |SupportedHolder.value f x| ≤ ‖f‖ :=
  OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le f.val x

theorem holder (f : SupportedHolder m α R) (x y) :
    |SupportedHolder.value f x - SupportedHolder.value f y| ≤ ‖f‖ * ‖x - y‖ ^ α := by
  change |OAI.Analysis.Normed.Function.Holder.HolderMap.value f.val x - OAI.Analysis.Normed.Function.Holder.HolderMap.value f.val y| ≤ ‖f.val‖ * ‖x - y‖ ^ α
  simpa only [SupportedHolder.value, Real.norm_eq_abs, dist_eq_norm] using OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le f.val x y

@[simp] theorem value_add (f g : SupportedHolder m α R) : SupportedHolder.value (f + g) = SupportedHolder.value f + SupportedHolder.value g := rfl
@[simp] theorem value_smul (c : ℝ) (f : SupportedHolder m α R) : SupportedHolder.value (c • f) = c • SupportedHolder.value f := rfl

end SupportedHolder

abbrev GlobalC2Holder (m : ℕ) (α : ℝ) :=
  OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) (show (univ : Set (EuclideanSpace ℝ (Fin m))) ⊆ univ from Subset.rfl) α

instance instGlobalC2HolderNormedGroup (m : ℕ) (α : ℝ) :
    NormedAddCommGroup (GlobalC2Holder m α) := inferInstance

instance instGlobalC2HolderNormedSpace (m : ℕ) (α : ℝ) :
    NormedSpace ℝ (GlobalC2Holder m α) := inferInstance

end OAI.Analysis.PDE.Schauder

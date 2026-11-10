module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.Normed.Function.Holder.Banach.Maps
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

open Set
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder.C2Holder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω K : Set E} {hΩK : Ω ⊆ K} {α : ℝ}

local instance dirichletFirstDerivativeNormedGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance dirichletFirstDerivativeNormedSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance dirichletSecondDerivativeNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) :=
  inferInstance
local instance dirichletSecondDerivativeNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) :=
  inferInstance

def valueCLM : C2Holder (F := F) hΩK α →L[ℝ] (K →ᵇ F) where
  toFun := C2Holder.value
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_fst.comp continuous_subtype_val

def firstDerivativeCLM : C2Holder (F := F) hΩK α →L[ℝ] (K →ᵇ (E →L[ℝ] F)) where
  toFun := C2Holder.firstDerivative
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_snd.fst.comp continuous_subtype_val

def secondDerivativeCLM : C2Holder (F := F) hΩK α →L[ℝ] (K →ᵇ (E →L[ℝ] E →L[ℝ] F)) where
  toFun := C2Holder.secondDerivative
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := OAI.Analysis.Normed.Function.Holder.HolderMap.valueCLM.continuous.comp
    (continuous_snd.snd.comp continuous_subtype_val)

/-- The zero-Dirichlet condition is imposed on the actual continuous boundary trace. -/
def zeroTrace : Submodule ℝ (C2Holder (F := F) hΩK α) where
  carrier := {f | ∀ x : K, x.val ∉ Ω → C2Holder.value f x = 0}
  zero_mem' := by
    change ∀ x : K, x.val ∉ Ω → C2Holder.value (0 : C2Holder (F := F) hΩK α) x = 0
    intro x hx
    rfl
  add_mem' := by
    intro f g hf hg x hx
    change C2Holder.value f x + C2Holder.value g x = 0
    rw [hf x hx, hg x hx, add_zero]
  smul_mem' := by
    intro c f hf x hx
    change c • C2Holder.value f x = 0
    rw [hf x hx, smul_zero]

theorem isClosed_zeroTrace :
    IsClosed (C2Holder.zeroTrace (F := F) (hΩK := hΩK) (α := α) : Set (C2Holder (F := F) hΩK α)) := by
  change IsClosed {f : C2Holder (F := F) hΩK α | ∀ x : K, x.val ∉ Ω → C2Holder.value f x = 0}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro hx
  exact isClosed_eq ((BoundedContinuousFunction.evalCLM ℝ x).continuous.comp
    (C2Holder.valueCLM (F := F) (hΩK := hΩK) (α := α)).continuous) continuous_const

abbrev DirichletSpace (hΩK : Ω ⊆ K) (α : ℝ) : Type _ :=
  ↥(C2Holder.zeroTrace (F := F) (hΩK := hΩK) (α := α))

instance [Fact (IsOpen Ω)] [CompleteSpace F] :
    CompleteSpace (C2Holder.DirichletSpace (F := F) hΩK α) :=
  (C2Holder.isClosed_zeroTrace (F := F) (hΩK := hΩK) (α := α)).isComplete.completeSpace_coe

end OAI.Analysis.Normed.Function.Holder.C2Holder

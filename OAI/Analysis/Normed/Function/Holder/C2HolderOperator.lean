module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.Normed.Function.Holder.Banach.Operator
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
public import OAI.Analysis.Normed.Function.Holder.C2HolderRegularity


set_option backward.privateInPublic true
@[expose] public section

open Set
open scoped BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder.C2Holder

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {Ω K : Set E} {hΩK : Ω ⊆ K} {α : ℝ}

local instance operatorFirstDerivativeNormedGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance operatorFirstDerivativeNormedSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance operatorSecondDerivativeNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) :=
  inferInstance
local instance operatorSecondDerivativeNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) :=
  inferInstance
local instance coefficientNormedGroup :
    NormedAddCommGroup ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] G) := inferInstance
local instance coefficientNormedSpace :
    NormedSpace ℝ ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] G) := inferInstance

/-- The Hessian projection retains its full Hölder norm. -/
def hessianCLM : C2Holder (F := F) hΩK α →L[ℝ] HolderMap K (E →L[ℝ] E →L[ℝ] F) α where
  toFun f := f.val.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_snd.snd.comp continuous_subtype_val

theorem norm_hessianCLM_apply_le (f : C2Holder (F := F) hΩK α) :
    ‖C2Holder.hessianCLM f‖ ≤ ‖f‖ := (le_max_right _ _).trans (le_max_right _ _)

/-- A second-order operator with Cα coefficients acts boundedly from C²,α to Cα. -/
def secondOrderCLM (hα : 0 ≤ α)
    (a : HolderMap K ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] G) α) :
    C2Holder (F := F) hΩK α →L[ℝ] HolderMap K G α :=
  (OAI.Analysis.Normed.Function.Holder.HolderMap.actionCLM hα a).comp C2Holder.hessianCLM

@[simp] theorem secondOrderCLM_apply (hα : 0 ≤ α)
    (a : HolderMap K ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] G) α)
    (f : C2Holder (F := F) hΩK α) (x : K) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (C2Holder.secondOrderCLM hα a f) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value a x (C2Holder.secondDerivative f x) := rfl

theorem norm_secondOrderCLM_apply_le (hα : 0 ≤ α)
    (a : HolderMap K ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] G) α)
    (f : C2Holder (F := F) hΩK α) :
    ‖C2Holder.secondOrderCLM hα a f‖ ≤ (2 * ‖a‖) * ‖f‖ :=
  (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le hα a (C2Holder.hessianCLM f)).trans
    (mul_le_mul_of_nonneg_left (C2Holder.norm_hessianCLM_apply_le f) (by positivity))

/-- On the open domain this is the differential operator applied to the actual
second Fréchet derivative, not an independent jet field. -/
theorem secondOrderCLM_eq_fderiv (hΩ : IsOpen Ω) (hα : 0 ≤ α)
    (a : HolderMap K ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] G) α)
    (f : C2Holder (F := F) hΩK α) {x : E} (hx : x ∈ Ω) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (C2Holder.secondOrderCLM hα a f) ⟨x, hΩK hx⟩ =
      OAI.Analysis.Normed.Function.Holder.HolderMap.value a ⟨x, hΩK hx⟩
        (fderiv ℝ (fderiv ℝ (boundedZeroExtension (C2Holder.value f))) x) := by
  rw [C2Holder.secondOrderCLM_apply, (C2Holder.genuine_derivatives hΩ f hx).2]

end OAI.Analysis.Normed.Function.Holder.C2Holder

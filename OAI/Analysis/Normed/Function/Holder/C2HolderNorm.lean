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
public import OAI.Analysis.Normed.Function.Holder.Banach.Norm


set_option backward.privateInPublic true
@[expose] public section

open Set
open scoped BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder

namespace C2Holder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω K : Set E} {hΩK : Ω ⊆ K} {α : ℝ}

local instance normFirstDerivativeNormedGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance normFirstDerivativeNormedSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance normSecondDerivativeNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) :=
  inferInstance
local instance normSecondDerivativeNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) :=
  inferInstance

@[simp] theorem value_sub (f g : C2Holder (F := F) hΩK α) :
    C2Holder.value (f - g) = C2Holder.value f - C2Holder.value g := rfl

@[simp] theorem firstDerivative_sub (f g : C2Holder (F := F) hΩK α) :
    C2Holder.firstDerivative (f - g) = C2Holder.firstDerivative f - C2Holder.firstDerivative g := rfl

@[simp] theorem secondDerivative_sub (f g : C2Holder (F := F) hΩK α) :
    C2Holder.secondDerivative (f - g) = C2Holder.secondDerivative f - C2Holder.secondDerivative g := rfl

/-- Uniform bounds on the actual jet and the Hessian's Hölder differences
control the Banach norm, in particular for differences of approximating solutions. -/
theorem norm_le_of_bounds (hα : 0 ≤ α) {C : ℝ} (hC : 0 ≤ C)
    (f : C2Holder (F := F) hΩK α)
    (h₀ : ∀ x, ‖C2Holder.value f x‖ ≤ C)
    (h₁ : ∀ x, ‖C2Holder.firstDerivative f x‖ ≤ C)
    (h₂ : ∀ x, ‖C2Holder.secondDerivative f x‖ ≤ C)
    (hh : ∀ x y, ‖C2Holder.secondDerivative f x - C2Holder.secondDerivative f y‖ ≤ C * (dist x y) ^ α) :
    ‖f‖ ≤ C := by
  have hb₀ : ‖f.val.1‖ ≤ C := (BoundedContinuousFunction.norm_le hC).mpr h₀
  have hb₁ : ‖f.val.2.1‖ ≤ C := (BoundedContinuousFunction.norm_le hC).mpr h₁
  have hb₂ : ‖f.val.2.2‖ ≤ C := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_le_of_bounds hα hC _ h₂ hh
  exact max_le hb₀ (max_le hb₁ hb₂)

end C2Holder
end OAI.Analysis.Normed.Function.Holder

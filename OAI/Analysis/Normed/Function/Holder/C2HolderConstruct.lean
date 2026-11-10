module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.Normed.Function.Holder.Banach.Construct
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

open Set Filter
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def boundedRestriction {K : Set E} (f : E → F) (hf : ContinuousOn f K) (C : ℝ)
    (hC : ∀ x ∈ K, ‖f x‖ ≤ C) : K →ᵇ F :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x : K ↦ f x)
    (continuousOn_iff_continuous_domRestrict.mp hf) C (fun x ↦ hC x x.property)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem boundedRestriction_germ {Ω K : Set E} (hΩ : IsOpen Ω) (hΩK : Ω ⊆ K)
    (f : E → F) (hf : ContinuousOn f K) (C : ℝ) (hC : ∀ x ∈ K, ‖f x‖ ≤ C)
    {x : E} (hx : x ∈ Ω) :
    boundedZeroExtension (boundedRestriction f hf C hC) =ᶠ[𝓝 x] f := by
  filter_upwards [hΩ.mem_nhds hx] with y hy
  rw [boundedZeroExtension_apply _ (hΩK hy)]
  rfl

namespace C2Holder

/-- Insert a genuine C² function with bounded value, first and second derivatives
and a Hölder Hessian into the complete C²,α space. -/
def ofContDiff {Ω K : Set E} (hΩ : IsOpen Ω) (hΩK : Ω ⊆ K) {α : ℝ} (hα : 0 ≤ α)
    (f : E → F) (hf : ContDiff ℝ 2 f) {M₀ M₁ M₂ H : ℝ}
    (h₀ : ∀ x ∈ K, ‖f x‖ ≤ M₀)
    (h₁ : ∀ x ∈ K, ‖fderiv ℝ f x‖ ≤ M₁)
    (h₂ : ∀ x ∈ K, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M₂)
    (hh : ∀ x ∈ K, ∀ y ∈ K,
      ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ H * (dist x y) ^ α) :
    C2Holder (F := F) hΩK α := by
  have hf₁ : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hf₂ : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ f)) := hf₁.fderiv_right (by norm_num)
  let v := boundedRestriction f hf.continuous.continuousOn M₀ h₀
  let G := boundedRestriction (fderiv ℝ f) hf₁.continuous.continuousOn M₁ h₁
  let B := boundedRestriction (fderiv ℝ (fderiv ℝ f)) hf₂.continuous.continuousOn M₂ h₂
  let J := OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα B (fun x y ↦ hh x x.property y y.property)
  refine ⟨(v, G, J), ?_, ?_⟩
  · intro x hx
    change HasFDerivAt (boundedZeroExtension v) (fderiv ℝ f x) x
    exact ((hf.differentiable (by norm_num) x).hasFDerivAt).congr_of_eventuallyEq
      (boundedRestriction_germ hΩ hΩK f hf.continuous.continuousOn M₀ h₀ hx)
  · intro x hx
    change HasFDerivAt (boundedZeroExtension G) (fderiv ℝ (fderiv ℝ f) x) x
    exact ((hf₁.differentiable (by norm_num) x).hasFDerivAt).congr_of_eventuallyEq
      (boundedRestriction_germ hΩ hΩK (fderiv ℝ f) hf₁.continuous.continuousOn M₁ h₁ hx)

section Evaluation

variable {Ω K : Set E} (hΩ : IsOpen Ω) (hΩK : Ω ⊆ K) {α : ℝ} (hα : 0 ≤ α)
  (f : E → F) (hf : ContDiff ℝ 2 f) {M₀ M₁ M₂ H : ℝ}
  (h₀ : ∀ x ∈ K, ‖f x‖ ≤ M₀)
  (h₁ : ∀ x ∈ K, ‖fderiv ℝ f x‖ ≤ M₁)
  (h₂ : ∀ x ∈ K, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M₂)
  (hh : ∀ x ∈ K, ∀ y ∈ K,
    ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ H * (dist x y) ^ α)

@[simp] theorem value_ofContDiff (x : K) :
    C2Holder.value (C2Holder.ofContDiff hΩ hΩK hα f hf h₀ h₁ h₂ hh) x = f x := rfl

@[simp] theorem firstDerivative_ofContDiff (x : K) :
    C2Holder.firstDerivative (C2Holder.ofContDiff hΩ hΩK hα f hf h₀ h₁ h₂ hh) x = fderiv ℝ f x := rfl

@[simp] theorem secondDerivative_ofContDiff (x : K) :
    C2Holder.secondDerivative (C2Holder.ofContDiff hΩ hΩK hα f hf h₀ h₁ h₂ hh) x =
      fderiv ℝ (fderiv ℝ f) x := rfl

end Evaluation

end C2Holder
end OAI.Analysis.Normed.Function.Holder

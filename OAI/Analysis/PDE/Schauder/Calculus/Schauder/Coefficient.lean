module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.HolderPullback
public import OAI.Analysis.Normed.Function.Holder.C2HolderOperator
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.BanachData
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

/-! A supported Hölder coefficient field acts on the actual Hessian. -/

noncomputable section
open Set Metric
open scoped BoundedContinuousFunction
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

abbrev EuclideanHessian (m : ℕ) :=
  EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ

instance instEuclideanHessianNormedGroup (m : ℕ) : NormedAddCommGroup (EuclideanHessian m) :=
  inferInstanceAs (NormedAddCommGroup
    (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ))

instance instEuclideanHessianNormedSpace (m : ℕ) : NormedSpace ℝ (EuclideanHessian m) :=
  inferInstanceAs (NormedSpace ℝ
    (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ))

instance instEuclideanHessianFunctionalNormedGroup (m : ℕ) :
    NormedAddCommGroup (EuclideanHessian m →L[ℝ] ℝ) := inferInstance

instance instEuclideanHessianFunctionalNormedSpace (m : ℕ) :
    NormedSpace ℝ (EuclideanHessian m →L[ℝ] ℝ) := inferInstance

def globalC2Value {m : ℕ} {α : ℝ} (u : GlobalC2Holder m α) (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  OAI.Analysis.Normed.Function.Holder.C2Holder.value u ⟨x, mem_univ x⟩

theorem globalC2Value_eq_extension {m : ℕ} {α : ℝ} (u : GlobalC2Holder m α) :
    globalC2Value u = OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value u) := by
  funext x
  exact (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply _ (mem_univ x)).symm

theorem contDiff_globalC2Value {m : ℕ} {α : ℝ} (u : GlobalC2Holder m α) :
    ContDiff ℝ 2 (globalC2Value u) := by
  rw [globalC2Value_eq_extension]
  exact contDiffOn_univ.mp (OAI.Analysis.Normed.Function.Holder.C2Holder.contDiffOn_value isOpen_univ u)

def globalHessianHolder {m : ℕ} {α : ℝ} (hα : 0 ≤ α) :
    GlobalC2Holder m α →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanHessian m) α :=
  (holderIsometricPullback hα (fun x => (⟨x, mem_univ x⟩ : (univ : Set (EuclideanSpace ℝ (Fin m)))))
    (fun _ _ => rfl)).comp OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM

theorem globalHessianHolder_apply {m : ℕ} {α : ℝ} (hα : 0 ≤ α)
    (u : GlobalC2Holder m α) (x : EuclideanSpace ℝ (Fin m)) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (globalHessianHolder hα u) x = fderiv ℝ (fderiv ℝ (globalC2Value u)) x := by
  change OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative u ⟨x, mem_univ x⟩ = _
  rw [globalC2Value_eq_extension]
  exact (OAI.Analysis.Normed.Function.Holder.C2Holder.genuine_derivatives isOpen_univ u (mem_univ x)).2.symm

theorem norm_globalHessianHolder_le {m : ℕ} {α : ℝ} (hα : 0 ≤ α) (u : GlobalC2Holder m α) :
    ‖globalHessianHolder hα u‖ ≤ ‖u‖ :=
  (norm_holderIsometricPullback_le hα
    (fun x => (⟨x, mem_univ x⟩ : (univ : Set (EuclideanSpace ℝ (Fin m)))))
    (fun _ _ => rfl) (OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM u)).trans (OAI.Analysis.Normed.Function.Holder.C2Holder.norm_hessianCLM_apply_le u)

def supportedCoefficientAction {m : ℕ} {α R : ℝ} (hα : 0 ≤ α)
    (a : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanHessian m →L[ℝ] ℝ) α)
    (ha : ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value a x = 0) :
    GlobalC2Holder m α →L[ℝ] SupportedHolder m α R := by
  let A := (OAI.Analysis.Normed.Function.Holder.HolderMap.actionCLM hα a).comp (globalHessianHolder hα)
  refine A.codRestrict (supportedHolderSubmodule m α R) ?_
  intro u x hx
  change OAI.Analysis.Normed.Function.Holder.HolderMap.value a x (OAI.Analysis.Normed.Function.Holder.HolderMap.value (globalHessianHolder hα u) x) = 0
  rw [ha x hx]
  rfl

theorem supportedCoefficientAction_apply {m : ℕ} {α R : ℝ} (hα : 0 ≤ α)
    (a : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanHessian m →L[ℝ] ℝ) α)
    (ha : ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value a x = 0)
    (u : GlobalC2Holder m α) (x : EuclideanSpace ℝ (Fin m)) :
    OAI.Analysis.PDE.Schauder.SupportedHolder.value (supportedCoefficientAction hα a ha u) x =
      OAI.Analysis.Normed.Function.Holder.HolderMap.value a x (fderiv ℝ (fderiv ℝ (globalC2Value u)) x) := by
  change OAI.Analysis.Normed.Function.Holder.HolderMap.value a x (OAI.Analysis.Normed.Function.Holder.HolderMap.value (globalHessianHolder hα u) x) = _
  rw [globalHessianHolder_apply]

theorem norm_supportedCoefficientAction_le {m : ℕ} {α R : ℝ} (hα : 0 ≤ α)
    (a : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanHessian m →L[ℝ] ℝ) α)
    (ha : ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value a x = 0)
    (u : GlobalC2Holder m α) :
    ‖supportedCoefficientAction hα a ha u‖ ≤ 2 * ‖a‖ * ‖u‖ := by
  change ‖OAI.Analysis.Normed.Function.Holder.HolderMap.action hα a (globalHessianHolder hα u)‖ ≤ 2 * ‖a‖ * ‖u‖
  exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le hα a (globalHessianHolder hα u)).trans
    (mul_le_mul_of_nonneg_left (norm_globalHessianHolder_le hα u) (by positivity))

end OAI.Analysis.PDE.Schauder

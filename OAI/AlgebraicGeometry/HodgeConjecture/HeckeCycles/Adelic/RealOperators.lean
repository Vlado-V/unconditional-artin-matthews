module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.FiniteOperators
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

/-! # Real Operators -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.RealOperators.CM

noncomputable section

/-! Extend an actual real Schwartz operator to adelic Schwartz
functions by applying it to each real section. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.FiniteOperators.CM.Sections
variable {I : Type*} [Fintype I]

def raw (U : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I →ₗ[ℂ] ((I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) → ℂ) where
  toFun F x := (U (FiniteOperators.CM.Sections.realSection (fun i => (x i).2) F)).val (fun i => (x i).1)
  map_add' F G := by
    funext x
    rw [map_add, map_add]
    rfl
  map_smul' c F := by
    funext x
    rw [map_smul, map_smul]
    rfl

theorem raw_tensor (U : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I)
    (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) : raw U (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.pureTensor (U f) φ := by
  funext x
  change (U (FiniteOperators.CM.Sections.realSection (fun i => (x i).2) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ))).val (fun i => (x i).1) = _
  rw [FiniteOperators.CM.Sections.realSection_tensor, map_smul]
  exact mul_comm (φ.val (fun i => (x i).2)) ((U f).val (fun i => (x i).1))

theorem raw_mem (U : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) (F : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) :
    raw U F ∈ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I := by
  obtain ⟨F, hF⟩ := F
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨f, φ, rfl⟩ := hF
    change raw U (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ) ∈ _
    rw [raw_tensor]
    exact (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor (U f) φ).property
  | zero =>
    change raw U 0 ∈ _
    rw [map_zero]
    exact (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I).zero_mem
  | add F G hF hG ihF ihG =>
    change raw U (⟨F, hF⟩ + ⟨G, hG⟩) ∈ _
    rw [map_add]
    exact (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I).add_mem ihF ihG
  | smul c F hF ih =>
    change raw U (c • ⟨F, hF⟩) ∈ _
    rw [map_smul]
    exact (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I).smul_mem c ih

def extend (U : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I :=
  (raw U).codRestrict (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) (raw_mem U)

theorem extend_tensor (U : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I)
    (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) : extend U (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor (U f) φ :=
  Subtype.ext (raw_tensor U f φ)

theorem extend_id : extend (LinearMap.id (R := ℂ) (M := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I)) = LinearMap.id := by
  apply FiniteOperators.CM.Sections.linear_ext
  intro f φ
  rw [extend_tensor]
  rfl

theorem extend_comp (U V : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) :
    extend (U.comp V) = (extend U).comp (extend V) := by
  apply FiniteOperators.CM.Sections.linear_ext
  intro f φ
  simp only [LinearMap.comp_apply, extend_tensor]

def operator : (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) →*
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) where
  toFun U := {
    toLinearMap := extend U.toLinearMap
    invFun := extend U.symm.toLinearMap
    left_inv F := by
      have h := congrArg (fun T : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I => T F)
        (extend_comp U.symm.toLinearMap U.toLinearMap).symm
      change extend U.symm.toLinearMap (extend U.toLinearMap F) = _ at h
      have hi : U.symm.toLinearMap.comp U.toLinearMap = LinearMap.id := by
        apply LinearMap.ext
        exact U.symm_apply_apply
      rw [hi, extend_id] at h
      exact h
    right_inv F := by
      have h := congrArg (fun T : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I => T F)
        (extend_comp U.toLinearMap U.symm.toLinearMap).symm
      change extend U.toLinearMap (extend U.symm.toLinearMap F) = _ at h
      have hi : U.toLinearMap.comp U.symm.toLinearMap = LinearMap.id := by
        apply LinearMap.ext
        exact U.apply_symm_apply
      rw [hi, extend_id] at h
      exact h }
  map_one' := by
    apply LinearEquiv.toLinearMap_injective
    exact extend_id
  map_mul' U V := by
    apply LinearEquiv.toLinearMap_injective
    exact extend_comp U.toLinearMap V.toLinearMap

theorem operator_tensor (U : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I)
    (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) : operator U (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor (U f) φ :=
  extend_tensor U.toLinearMap f φ

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.RealOperators.CM

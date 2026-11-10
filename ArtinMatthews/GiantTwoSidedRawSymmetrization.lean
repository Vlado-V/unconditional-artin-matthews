module

public import ArtinMatthews.GiantTwoSidedRawEdgeCoordinates
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

/-! Independent slot permutations at both physical endpoints rename
ordered markings. They preserve both positions and the full raw edge
coefficient after the same renaming. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def giantTwoSidedEndpointPermute {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    {Z : Finset ℕ} (π : J → Equiv.Perm (Fin M)) :
    GiantTwoSidedEndpointState P M Z ≃ GiantTwoSidedEndpointState P M Z where
  toFun s := ⟨(s.val.1,fun j l => s.val.2 j (π j l)),
    fun j => (s.property.1 j).comp (π j).injective,
    fun j l => s.property.2 j (π j l)⟩
  invFun s := ⟨(s.val.1,fun j l => s.val.2 j ((π j).symm l)),
    fun j => (s.property.1 j).comp (π j).symm.injective,
    fun j l => s.property.2 j ((π j).symm l)⟩
  left_inv s := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext j l
      exact congrArg (s.val.2 j) ((π j).apply_symm_apply l)
  right_inv s := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext j l
      exact congrArg (s.val.2 j) ((π j).symm_apply_apply l)

abbrev GiantTwoSidedRawPermutedEdge {J : Type*} [Fintype J] (P : J → Finset ℕ)
    (k : ℕ) (Z Z' : Finset ℕ) (π τ : J → Equiv.Perm (Fin (k+1))) :=
  {e : GiantTwoSidedEndpointState P (k+1) Z × GiantTwoSidedEndpointState P (k+1) Z' //
    GiantTwoSidedRawPhysicalCondition (giantTwoSidedEndpointPermute π e.1)
      (giantTwoSidedEndpointPermute τ e.2)}

def giantTwoSidedRawPermutedEquiv {J : Type*} [Fintype J] {P : J → Finset ℕ}
    {k : ℕ} {Z Z' : Finset ℕ} (π τ : J → Equiv.Perm (Fin (k+1))) :
    GiantTwoSidedRawPermutedEdge P k Z Z' π τ ≃ GiantTwoSidedRawPhysicalEdge P k Z Z' where
  toFun e := ⟨(giantTwoSidedEndpointPermute π e.val.1,
    giantTwoSidedEndpointPermute τ e.val.2),e.property⟩
  invFun e := ⟨((giantTwoSidedEndpointPermute π).symm e.val.1,
    (giantTwoSidedEndpointPermute τ).symm e.val.2),by
      simp only [Equiv.apply_symm_apply,e.property]⟩
  left_inv e := by
    apply Subtype.ext
    exact Prod.ext (Equiv.symm_apply_apply _ _) (Equiv.symm_apply_apply _ _)
  right_inv e := by
    apply Subtype.ext
    exact Prod.ext (Equiv.apply_symm_apply _ _) (Equiv.apply_symm_apply _ _)

def giantTwoSidedRawPermutationAverage {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k : ℕ} {Z Z' : Finset ℕ}
    (f : GiantTwoSidedRawPhysicalEdge P k Z Z' → ℂ) : ℂ :=
  let Permutations := J → Equiv.Perm (Fin (k+1))
  ((Fintype.card Permutations:ℂ)^2)⁻¹ *
    ∑ π : Permutations,∑ τ : Permutations,∑ e : GiantTwoSidedRawPermutedEdge P k Z Z' π τ,
      f (giantTwoSidedRawPermutedEquiv π τ e)

theorem giantTwoSidedRawPermutationAverage_eq {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k : ℕ} {Z Z' : Finset ℕ}
    (f : GiantTwoSidedRawPhysicalEdge P k Z Z' → ℂ) :
    giantTwoSidedRawPermutationAverage f = ∑ e,f e := by
  classical
  let Permutations := J → Equiv.Perm (Fin (k+1))
  let S := ∑ e,f e
  have hsum (π τ : Permutations) : (∑ e : GiantTwoSidedRawPermutedEdge P k Z Z' π τ,
      f (giantTwoSidedRawPermutedEquiv π τ e)) = S :=
    (giantTwoSidedRawPermutedEquiv π τ).sum_comp f
  have hpos : 0 < Fintype.card Permutations :=
    Fintype.card_pos_iff.mpr ⟨fun _ => Equiv.refl _⟩
  have hcard : (Fintype.card Permutations:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  change ((Fintype.card Permutations:ℂ)^2)⁻¹ * (∑ π : Permutations,∑ τ : Permutations,_) = S
  simp_rw [hsum]
  simp only [sum_const,nsmul_eq_mul,card_univ]
  let C := (Fintype.card Permutations:ℂ)
  change (C^2)⁻¹*(C*(C*S)) = S
  rw [← mul_assoc C C S,← pow_two]
  exact inv_mul_cancel_left₀ (pow_ne_zero _ hcard) S

end
end ArtinMatthews

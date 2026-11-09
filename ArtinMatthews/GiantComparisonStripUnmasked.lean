module

public import ArtinMatthews.GiantComparisonStripKernel


set_option backward.privateInPublic true
@[expose] public section

/-! Remove only the two physical position masks on the support of the
smooth quotient cutoff. All marking restrictions are kept in the carrier. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset ℕ} {k ell N m : ℕ}
  {C : J → Finset (Fin k)} {Z Z' : Finset ℕ}

abbrev GiantComparisonUnmaskedEdge (P : J → Finset ℕ) (C : J → Finset (Fin k))
    (ell N : ℕ) (aux : GiantTwoSidedPatternAuxiliary P C) :=
  {a : GiantComparisonSharedData P C ell N //
    GiantComparisonSharedCondition {giantComparisonSharedProduct a.1*a.2.1.val}
      {giantComparisonSharedProduct a.1*(a.2.1.val+giantTwoSidedPatternAuxiliaryProduct aux)} aux a}

def GiantComparisonPositionGuards (Z Z' : Finset ℕ)
    (aux : GiantTwoSidedPatternAuxiliary P C) (a : GiantComparisonSharedData P C ell N) : Prop :=
  giantComparisonSharedProduct a.1*a.2.1.val ∈ Z ∧
    giantComparisonSharedProduct a.1*(a.2.1.val+giantTwoSidedPatternAuxiliaryProduct aux) ∈ Z'

def giantComparisonPositionGuardEquiv (aux : GiantTwoSidedPatternAuxiliary P C) :
    GiantComparisonSharedEdge P C ell N Z Z' aux ≃
      {a : GiantComparisonUnmaskedEdge P C ell N aux // GiantComparisonPositionGuards Z Z' aux a.val} where
  toFun a := ⟨⟨a.val, a.property.sourceDistinct, a.property.targetDistinct,
    a.property.sourceDivides, a.property.targetDivides, mem_singleton_self _, mem_singleton_self _,
    a.property.auxiliaryBan⟩, a.property.sourcePosition, a.property.targetPosition⟩
  invFun a := ⟨a.val.val, a.val.property.sourceDistinct, a.val.property.targetDistinct,
    a.val.property.sourceDivides, a.val.property.targetDivides, a.property.1, a.property.2,
    a.val.property.auxiliaryBan⟩
  left_inv a := Subtype.ext rfl
  right_inv a := Subtype.ext (Subtype.ext rfl)

def giantComparisonUnmaskedSummand (x q : ℝ) (Ψ : ℝ → ℂ)
    (χ : DirichletCharacter ℂ m) (F G : ℕ → ℂ)
    (K : GiantTwoSidedPatternCoefficient P C ell)
    {aux : GiantTwoSidedPatternAuxiliary P C}
    (a : GiantComparisonUnmaskedEdge P C ell N aux) : ℂ :=
  giantComparisonSharedSummand x q Ψ χ F G K
    (Z:={giantComparisonSharedProduct a.val.1*a.val.2.1.val})
    (Z':={giantComparisonSharedProduct a.val.1*(a.val.2.1.val+giantTwoSidedPatternAuxiliaryProduct aux)})
    ⟨a.val,a.property⟩

theorem giantComparisonShared_sum_unmasked [DecidableEq J] (x q : ℝ) (Ψ : ℝ → ℂ)
    (χ : DirichletCharacter ℂ m) (F G : ℕ → ℂ) (K : GiantTwoSidedPatternCoefficient P C ell)
    (aux : GiantTwoSidedPatternAuxiliary P C)
    (hcover : ∀ a : GiantComparisonUnmaskedEdge P C ell N aux,
      Ψ ((a.val.2.1.val:ℝ)/(x*(giantTwoSidedPatternAuxiliaryProduct aux:ℝ))) ≠ 0 →
        GiantComparisonPositionGuards Z Z' aux a.val) :
    (∑ a : GiantComparisonSharedEdge P C ell N Z Z' aux,
      giantComparisonSharedSummand x q Ψ χ F G K a) =
      ∑ a : GiantComparisonUnmaskedEdge P C ell N aux,
        giantComparisonUnmaskedSummand x q Ψ χ F G K a := by
  classical
  let U := GiantComparisonUnmaskedEdge P C ell N aux
  let good (a : U) := GiantComparisonPositionGuards Z Z' aux a.val
  let term (a : U) := giantComparisonUnmaskedSummand x q Ψ χ F G K a
  let e := giantComparisonPositionGuardEquiv (P:=P) (C:=C) (ell:=ell) (N:=N) (Z:=Z) (Z':=Z') aux
  rw [← e.symm.sum_comp (giantComparisonSharedSummand x q Ψ χ F G K)]
  change (∑ a : Subtype good, term a.val) = ∑ a : U, term a
  have hs := Finset.sum_subtype (p := good) (F := inferInstance)
    (univ.filter good) (by simp) term
  rw [← hs, sum_filter]
  apply sum_congr rfl
  intro a _
  change (if good a then term a else 0) = term a
  split_ifs with ha
  · rfl
  · have hz : Ψ ((a.val.2.1.val:ℝ)/(x*(giantTwoSidedPatternAuxiliaryProduct aux:ℝ))) = 0 :=
      not_ne_iff.mp (fun h => ha (hcover a h))
    simp only [term, giantComparisonUnmaskedSummand, giantComparisonSharedSummand,
      giantComparisonPositionKernel, hz, zero_div, zero_mul, mul_zero]

end
end ArtinMatthews

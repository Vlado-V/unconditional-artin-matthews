module

public import ArtinMatthews.GiantComparisonSeparatedEdges
public import Mathlib.Data.Fintype.BigOperators


set_option backward.privateInPublic true
@[expose] public section

/-! The exact position and free-list sum retains the harmonic average
of the copied guard, and the independent version keeps the same list test. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
  {k ell N m : ℕ} {C : J → Finset (Fin k)}

abbrev GiantComparisonListCoefficient (P : J → Finset ℕ) (C : J → Finset (Fin k)) (ell : ℕ) :=
  GiantComparisonFreeLabels P C ell → GiantComparisonFreeLabels P C ell →
    GiantTwoSidedPatternAuxiliary P C → ℂ

def giantComparisonRestoredPair (L : GiantComparisonListCoefficient P C ell)
    (aux : GiantTwoSidedPatternAuxiliary P C) (q : ℝ) (w w' : ℕ) : ℂ :=
  ∑ b : GiantComparisonFreeMarking P C ell w,
    ∑ b' : GiantComparisonFreeMarking P C ell w',
      L b.val b'.val aux*(giantComparisonRestoredSharedDamping aux q w w' b.val b'.val:ℂ)

def giantComparisonIndependentPair (L : GiantComparisonListCoefficient P C ell)
    (aux : GiantTwoSidedPatternAuxiliary P C) (q : ℝ) (w w' : ℕ) : ℂ :=
  (giantComparisonIndependentDamping P C ell q w w':ℂ)*
    ∑ b : GiantComparisonFreeMarking P C ell w,
      ∑ b' : GiantComparisonFreeMarking P C ell w', L b.val b'.val aux

def giantComparisonIndependentAuxiliarySum (N : ℕ) (x q : ℝ) (Ψ : ℝ → ℂ)
    (χ : DirichletCharacter ℂ m) (F G : ℕ → ℂ) (L : GiantComparisonListCoefficient P C ell)
    (aux : GiantTwoSidedPatternAuxiliary P C) : ℂ :=
  let d := giantTwoSidedPatternAuxiliaryProduct aux
  (giantTwoSidedPatternAuxiliaryMass aux:ℂ)*
    ∑ w : ↥(Ioc 0 N), giantComparisonPositionKernel x Ψ χ F G d w.val *
      ((giantTwoSidedPatternFreshMass P C ell)^2:ℝ)*
        giantComparisonIndependentPair L aux q w.val (w.val+d)

theorem giantComparisonUnmasked_sum_eq_separated (x q : ℝ) (Ψ : ℝ → ℂ)
    (χ : DirichletCharacter ℂ m) (F G : ℕ → ℂ)
    (K : GiantTwoSidedPatternCoefficient P C ell) (L : GiantComparisonListCoefficient P C ell)
    (aux : GiantTwoSidedPatternAuxiliary P C)
    (hK : ∀ c b b', K (giantComparisonJoinLabels c b) (giantComparisonJoinLabels c b') aux = L b b' aux) :
    (∑ a : GiantComparisonUnmaskedEdge P C ell N aux,
      giantComparisonUnmaskedSummand x q Ψ χ F G K a) =
      (giantTwoSidedPatternAuxiliaryMass aux:ℂ)*
        ∑ w : ↥(Ioc 0 N), giantComparisonPositionKernel x Ψ χ F G (giantTwoSidedPatternAuxiliaryProduct aux) w.val *
          ((giantTwoSidedPatternFreshMass P C ell)^2:ℝ)*
            giantComparisonRestoredPair L aux q w.val (w.val+giantTwoSidedPatternAuxiliaryProduct aux) := by
  classical
  let S := ↥(Ioc 0 N)
  let X (w : S) := GiantComparisonFreeMarking P C ell w.val
  let Y (w : S) := GiantComparisonFreeMarking P C ell (w.val+giantTwoSidedPatternAuxiliaryProduct aux)
  let A (w : S) (b : X w) (b' : Y w) :=
    {c : GiantComparisonSharedLabels P C // GiantComparisonSharedAdmissible aux c b.val b'.val}
  letI (w : S) (b : X w) (b' : Y w) : Fintype (A w b b') := by
    dsimp [A]
    infer_instance
  letI (w : S) (b : X w) : Fintype (Σ b' : Y w, A w b b') := by
    letI : Fintype (Y w) := by dsimp [Y]; infer_instance
    exact Sigma.instFintype
  letI (w : S) : Fintype (Σ b : X w, Σ b' : Y w, A w b b') := by
    letI : Fintype (X w) := by dsimp [X]; infer_instance
    exact Sigma.instFintype
  letI : Fintype (GiantComparisonSeparatedEdge P C ell N aux) := by
    change Fintype (Σ w : S, Σ b : X w, Σ b' : Y w, A w b b')
    letI : Fintype S := by dsimp [S]; infer_instance
    exact Sigma.instFintype
  rw [← (giantComparisonSeparatedEquiv (ell:=ell) (N:=N) aux).symm.sum_comp (giantComparisonUnmaskedSummand x q Ψ χ F G K)]
  simp only [Fintype.sum_sigma, Finset.mul_sum]
  apply sum_congr rfl
  intro w _
  simp only [giantComparisonRestoredPair, Finset.mul_sum]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro b' _
  rw [giantComparisonRestoredSharedDamping_eq_sum]
  simp only [Complex.ofReal_sum, Finset.mul_sum]
  apply sum_congr rfl
  intro c _
  simp only [giantComparisonSeparatedEquiv, Equiv.coe_fn_symm_mk, giantComparisonUnmaskedSummand,
    giantComparisonSharedSummand, hK, Complex.ofReal_mul, Complex.ofReal_pow]
  ring

end
end ArtinMatthews

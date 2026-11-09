module

public import ArtinMatthews.GiantSmallConditioningData
public import ArtinMatthews.GiantTwoSidedPatternTargetBudget


set_option backward.privateInPublic true
@[expose] public section

/-! A valid tail is an actual completion of its fixed prefix. The
existing completion estimate gives a bound independent of prefix length. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}

omit [DecidableEq J] in
theorem giantSmallTailMass_eq_fresh :
    giantSmallTailMass P ell =
      giantTwoSidedPatternFreshMass P (fun _ => (∅ : Finset (Fin k))) ell := by
  simp only [giantSmallTailMass, giantTwoSidedPatternFreshMass, card_empty, add_zero]

theorem giantSmallConditioningTails_budget
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) {q B : ℝ}
    (hq : 0 < q) (hB : 0 ≤ B)
    (hbudget : ∀ j (z : ℕ),
      (bandReciprocalMass (P j))⁻¹ ^ ell * ((z : ℝ) + (ell : ℝ)) ^ ell *
        q ^ ((z : ℝ) / 2) ≤ B)
    (y : GiantTwoSidedFullResidue P) (d : MarkedPhysicalMarking P k) :
    ((giantSmallConditioningTails (ell := ell) y d).card : ℝ) * giantSmallTailMass P ell *
      giantTwoSidedResidueDamping P (k + ell) q y ≤ B ^ Fintype.card J := by
  let T := giantSmallConditioningTails (ell := ell) y d
  by_cases hT : T.Nonempty
  · obtain ⟨r₀, hr₀⟩ := hT
    have h₀ : GiantSmallStateCondition y (giantSmallAppend d r₀) := (mem_filter.mp hr₀).2
    let a₀ := giantSmallAppend d r₀
    let z := giantTwoSidedResidueZeroProduct y
    let C (_ : J) : Finset (Fin k) := ∅
    let A (j : J) := GiantTwoSidedPatternCompletion (P j) (C j) z (a₀ j)
    let f (r : ↥T) (j : J) : A j := by
      have hr : GiantSmallStateCondition y (giantSmallAppend d r.val) :=
        (mem_filter.mp r.property).2
      refine ⟨giantSmallAppend d r.val j, hr.1 j, ?_, ?_⟩
      · intro i
        exact (giantTwoSidedResidueZeroProduct_dvd_iff hP y
          (giantTwoSidedResidueIndex j (giantSmallAppend d r.val j i))).mpr (hr.2 j i)
      · intro i _
        simp only [a₀, giantSmallAppend, Fin.append_left]
    have hf : Function.Injective f := by
      intro r s hrs
      apply Subtype.ext
      funext j i
      have h := congrArg (fun a : A j => a.val (Fin.natAdd k i)) (congrFun hrs j)
      simpa only [f, giantSmallAppend, Fin.append_right] using h
    have hc : (T.card : ℝ) ≤ (Fintype.card (∀ j, A j) : ℝ) := by
      have h := Fintype.card_le_of_injective f hf
      rw [Fintype.card_coe] at h
      exact_mod_cast h
    have hb := giantTwoSidedPatternCompletionProduct_budget P hdis C a₀ h₀.1
      (f ⟨r₀, hr₀⟩) hq hV (fun j => by
        simpa only [C, card_empty, add_zero] using
          hbudget j (bandCount (P j) z - (k + ell)))
    rw [← giantTwoSidedResidueDamping_eq_physical hP (k + ell) q y,
      ← giantSmallTailMass_eq_fresh] at hb
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc
        (prod_nonneg fun j _ => pow_nonneg (inv_nonneg.mpr (hV j).le) _))
      (Real.rpow_nonneg hq.le _)).trans hb
  · have he : T = ∅ := not_nonempty_iff_eq_empty.mp hT
    change (T.card : ℝ) * _ * _ ≤ _
    rw [he, card_empty, Nat.cast_zero, zero_mul, zero_mul]
    exact pow_nonneg hB _

end
end ArtinMatthews

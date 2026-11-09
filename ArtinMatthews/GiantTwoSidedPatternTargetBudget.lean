module

public import ArtinMatthews.GiantTwoSidedPatternCompletions
public import ArtinMatthews.GiantTwoSidedPatternDamping
public import ArtinMatthews.GiantTwoSidedPatternKernel


set_option backward.privateInPublic true
@[expose] public section

/-! The actual target budget factors into per-group choices at one
forced integer position. Each factor keeps its own half-damping and
inverse band normalization. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantTwoSidedEndpointDamping_eq_prod {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (M n : ℕ) {q : ℝ} (hq : 0 < q) (hn : ∀ j,M≤bandCount (P j) n) :
    giantTwoSidedEndpointDamping P M q n = ∏ j,q^(((bandCount (P j) n-M:ℕ):ℝ)/2) := by
  have hsum : (∑ j,(bandCount (P j) n-M)) + M*Fintype.card J = ∑ j,bandCount (P j) n := by
    have hM : (∑ _j : J,M) = M*Fintype.card J := by simp [Nat.mul_comm]
    rw [← hM,← sum_add_distrib]
    exact sum_congr rfl fun j _ => Nat.sub_add_cancel (hn j)
  unfold giantTwoSidedEndpointDamping
  rw [giantCandidateBandCount_union P hdis n,← hsum,Nat.add_sub_cancel,Nat.cast_sum,sum_div,
    Real.rpow_sum_of_pos hq]

theorem giantTwoSidedPatternCompletionProduct_budget {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    {k ell n : ℕ} (C : J → Finset (Fin k)) (a : MarkedPhysicalMarking P (k+ell))
    (ha : MarkedPhysicalMarkingDistinct a)
    (b : ∀ j,GiantTwoSidedPatternCompletion (P j) (C j) n (a j)) {q B : ℝ} (hq : 0 < q)
    (hV : ∀ j,0 < bandReciprocalMass (P j))
    (hbudget : ∀ j,
      (bandReciprocalMass (P j))⁻¹^(ell+(C j).card)*
      (((bandCount (P j) n-(k+ell):ℕ):ℝ)+((ell+(C j).card:ℕ):ℝ))^(ell+(C j).card)*
      q^(((bandCount (P j) n-(k+ell):ℕ):ℝ)/2) ≤ B) :
    (Fintype.card (∀ j,GiantTwoSidedPatternCompletion (P j) (C j) n (a j)):ℝ)*
      giantTwoSidedPatternFreshMass P C ell*giantTwoSidedEndpointDamping P (k+ell) q n ≤
        B^Fintype.card J := by
  let z (j : J) := (bandCount (P j) n-(k+ell):ℕ)
  let t (j : J) := ell+(C j).card
  let V (j : J) := bandReciprocalMass (P j)
  let A (j : J) := GiantTwoSidedPatternCompletion (P j) (C j) n (a j)
  have hz (j : J) : k+ell ≤ bandCount (P j) n := giantTwoSidedPatternCompletion_count_le (P j) (C j) (b j)
  have hcard (j : J) : (Fintype.card (A j):ℝ) ≤ ((z j:ℝ)+(t j:ℝ))^(t j) := by
    exact_mod_cast giantTwoSidedPatternCompletion_card_le (P j) (C j) n (a j) (ha j)
  rw [Fintype.card_pi,Nat.cast_prod,giantTwoSidedPatternFreshMass,
    giantTwoSidedEndpointDamping_eq_prod P hdis (k+ell) n hq hz,← prod_mul_distrib,← prod_mul_distrib]
  calc
    _ ≤ ∏ j,B := by
      apply prod_le_prod₀ (fun j _ => mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (inv_nonneg.mpr (hV j).le) _))
        (Real.rpow_nonneg hq.le _))
      intro j _
      change ((Fintype.card (A j):ℝ)*(V j)⁻¹^(t j))*q^((z j:ℝ)/2) ≤ B
      rw [mul_comm (Fintype.card (A j):ℝ)]
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hcard j) (pow_nonneg (inv_nonneg.mpr (hV j).le) _))
        (Real.rpow_nonneg hq.le _)).trans (hbudget j)
    _ = _ := by rw [prod_const,card_univ]

def giantTwoSidedPatternTargets {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
    {k ell : ℕ} {C : J → Finset (Fin k)} (step : ℤ) {Z : Finset ℕ} (Z' : Finset ℕ)
    (s : GiantTwoSidedEndpointState P (k+ell) Z) (a : GiantTwoSidedPatternAuxiliary P C) :
    Finset (GiantTwoSidedEndpointState P (k+ell) Z') :=
  univ.filter (fun t => GiantTwoSidedPatternCondition C step s t a)

theorem giantTwoSidedPatternTargets_position {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell : ℕ} {C : J → Finset (Fin k)} {step : ℤ} {Z Z' : Finset ℕ}
    {s : GiantTwoSidedEndpointState P (k+ell) Z} {a : GiantTwoSidedPatternAuxiliary P C}
    {t t' : GiantTwoSidedEndpointState P (k+ell) Z'}
    (ht : t∈giantTwoSidedPatternTargets step Z' s a)
    (ht' : t'∈giantTwoSidedPatternTargets step Z' s a) : t.val.1=t'.val.1 := by
  have h : GiantTwoSidedPatternCondition C step s t a := (mem_filter.mp ht).2
  have h' : GiantTwoSidedPatternCondition C step s t' a := (mem_filter.mp ht').2
  exact Subtype.ext (Int.ofNat.inj (h.2.1.trans h'.2.1.symm))

theorem giantTwoSidedPatternTargets_budget {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    {k ell : ℕ} {C : J → Finset (Fin k)} {step : ℤ} {Z Z' : Finset ℕ}
    {s : GiantTwoSidedEndpointState P (k+ell) Z} {a : GiantTwoSidedPatternAuxiliary P C}
    {t₀ : GiantTwoSidedEndpointState P (k+ell) Z'} (ht₀ : t₀∈giantTwoSidedPatternTargets step Z' s a)
    {q B : ℝ} (hq : 0 < q) (hV : ∀ j,0 < bandReciprocalMass (P j))
    (hbudget : ∀ (j : J) (z : ℕ),
      (bandReciprocalMass (P j))⁻¹^(ell+(C j).card)*
      ((z:ℝ)+((ell+(C j).card:ℕ):ℝ))^(ell+(C j).card)*q^((z:ℝ)/2) ≤ B) :
    ((giantTwoSidedPatternTargets step Z' s a).card:ℝ)*
      giantTwoSidedPatternFreshMass P C ell*
        giantTwoSidedEndpointDamping P (k+ell) q t₀.val.1.val ≤ B^Fintype.card J := by
  let T := giantTwoSidedPatternTargets step Z' s a
  let n := t₀.val.1.val
  let A (j : J) := GiantTwoSidedPatternCompletion (P j) (C j) n (s.val.2 j)
  let f (t : ↥T) (j : J) : A j := by
    have ht : GiantTwoSidedPatternCondition C step s t.val a := (mem_filter.mp t.property).2
    have hn : t.val.val.1.val = n := congrArg (fun v : ↥Z' => v.val)
      (giantTwoSidedPatternTargets_position t.property ht₀)
    refine ⟨t.val.val.2 j,t.val.property.1 j,?_,ht.1 j⟩
    intro l
    rw [← hn]
    exact t.val.property.2 j l
  have hf : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact giantTwoSidedPatternTargets_position u.property v.property
    · funext j
      exact congrArg (fun b : A j => b.val) (congrFun huv j)
  have hcard : (T.card:ℝ) ≤ (Fintype.card (∀ j,A j):ℝ) := by
    have h := Fintype.card_le_of_injective f hf
    rw [Fintype.card_coe] at h
    exact_mod_cast h
  calc
    _ ≤ (Fintype.card (∀ j,A j):ℝ)*giantTwoSidedPatternFreshMass P C ell*
        giantTwoSidedEndpointDamping P (k+ell) q n :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcard (giantTwoSidedPatternFreshMass_nonneg C ell hV))
        (Real.rpow_nonneg hq.le _)
    _ ≤ _ := giantTwoSidedPatternCompletionProduct_budget P hdis C s.val.2 s.property.1
      (f ⟨t₀,ht₀⟩) hq hV (fun j => hbudget j _)

end
end ArtinMatthews

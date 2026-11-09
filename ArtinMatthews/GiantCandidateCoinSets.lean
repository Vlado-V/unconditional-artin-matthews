module

public import ArtinMatthews.GiantCandidateSelectedGroups
public import Mathlib.Algebra.BigOperators.Ring.Finset


set_option backward.privateInPublic true
@[expose] public section

/-! Actual success outcomes are retained by the two separate group-count
conditions. Each signed term adds an arbitrary set of failed groups. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section

def giantCandidateCoinSmall (x : ℝ) : Finset (GiantCandidateGroupIndex x) :=
  (univ : Finset (GiantCandidateSmallGroupIndex x)).map ⟨Sum.inl,Sum.inl_injective⟩

def giantCandidateCoinBig (x : ℝ) : Finset (GiantCandidateGroupIndex x) :=
  (univ : Finset (GiantCandidateBigGroupIndex x)).map ⟨Sum.inr,Sum.inr_injective⟩

theorem giantCandidateCoinSmall_card (x : ℝ) :
    (giantCandidateCoinSmall x).card = Fintype.card (GiantCandidateSmallGroupIndex x) := by
  rw [giantCandidateCoinSmall,card_map,card_univ]

theorem giantCandidateCoinBig_card (x : ℝ) :
    (giantCandidateCoinBig x).card = Fintype.card (GiantCandidateBigGroupIndex x) := by
  rw [giantCandidateCoinBig,card_map,card_univ]

def giantCandidateRetainedOutcomes (x threshold : ℝ) : Finset (Finset (GiantCandidateGroupIndex x)) :=
  (univ : Finset (GiantCandidateGroupIndex x)).powerset.filter (fun S =>
    threshold*Real.log (Real.log x) ≤ ((S ∩ giantCandidateCoinSmall x).card:ℝ) ∧
    threshold*Real.log (Real.log x) ≤ ((S ∩ giantCandidateCoinBig x).card:ℝ))

theorem mem_giantCandidateRetainedOutcomes {x threshold : ℝ} {S : Finset (GiantCandidateGroupIndex x)} :
    S ∈ giantCandidateRetainedOutcomes x threshold ↔
      threshold*Real.log (Real.log x) ≤ ((S ∩ giantCandidateCoinSmall x).card:ℝ) ∧
      threshold*Real.log (Real.log x) ≤ ((S ∩ giantCandidateCoinBig x).card:ℝ) := by
  simp only [giantCandidateRetainedOutcomes,mem_filter,mem_powerset,subset_univ,true_and]

theorem giantCandidateRetainedOutcomes_mono {x threshold : ℝ}
    {S P : Finset (GiantCandidateGroupIndex x)} (hSP : S ⊆ P)
    (hS : S ∈ giantCandidateRetainedOutcomes x threshold) :
    P ∈ giantCandidateRetainedOutcomes x threshold := by
  obtain ⟨hs,hb⟩ := mem_giantCandidateRetainedOutcomes.mp hS
  apply mem_giantCandidateRetainedOutcomes.mpr
  have hmono (A : Finset (GiantCandidateGroupIndex x)) : ((S ∩ A).card:ℝ) ≤ ((P ∩ A).card:ℝ) :=
    Nat.cast_le.mpr (card_le_card (fun i hi => mem_inter.mpr ⟨hSP (mem_inter.mp hi).1,(mem_inter.mp hi).2⟩))
  exact ⟨hs.trans (hmono _),hb.trans (hmono _)⟩

abbrev GiantCandidateCoinTerm (x : ℝ) := Σ _ : Finset (GiantCandidateGroupIndex x),
  Finset (GiantCandidateGroupIndex x)

def giantCandidateCoinTerms (x threshold : ℝ) : Finset (GiantCandidateCoinTerm x) :=
  (giantCandidateRetainedOutcomes x threshold).sigma (fun S =>
    ((univ : Finset (GiantCandidateGroupIndex x)) \ S).powerset)

def giantCandidateCoinTermCoefficient (x c : ℝ) (p : GiantCandidateCoinTerm x) : ℂ :=
  (-1:ℂ)^p.2.card*(c:ℂ)^(p.1 ∪ p.2).card

theorem giantCandidateCoinTermCoefficient_norm_le_one (x : ℝ) {c : ℝ}
    (hc : c ∈ Set.Icc (0:ℝ) 1) (p : GiantCandidateCoinTerm x) :
    ‖giantCandidateCoinTermCoefficient x c p‖ ≤ 1 := by
  simp only [giantCandidateCoinTermCoefficient,norm_mul,norm_pow,norm_neg,norm_one,
    one_pow,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc.1]
  exact pow_le_one₀ hc.1 hc.2

theorem giantCandidateCoinTerms_active_retained {x threshold : ℝ} {p : GiantCandidateCoinTerm x}
    (hp : p ∈ giantCandidateCoinTerms x threshold) :
    p.1 ∪ p.2 ∈ giantCandidateRetainedOutcomes x threshold :=
  giantCandidateRetainedOutcomes_mono subset_union_left (mem_sigma.mp hp).1

theorem giantCandidateCoinTerms_card (x threshold : ℝ) :
    (giantCandidateCoinTerms x threshold).card ≤ 3^Fintype.card (GiantCandidateGroupIndex x) := by
  let U := (univ : Finset (GiantCandidateGroupIndex x))
  let R := giantCandidateRetainedOutcomes x threshold
  have hR : R ⊆ U.powerset := filter_subset _ _
  unfold giantCandidateCoinTerms
  rw [card_sigma]
  change (∑ S ∈ R,((U \ S).powerset).card) ≤ _
  simp only [card_powerset]
  calc
    _ ≤ ∑ S ∈ U.powerset, 2^(U \ S).card :=
      sum_le_sum_of_subset_of_nonneg hR (fun _ _ _ => Nat.zero_le _)
    _ = _ := by
      simpa only [show (1+2:ℕ)=3 by norm_num,prod_const,one_pow,one_mul,U,card_univ] using
        (Finset.prod_add (s:=U) (f:=fun _ => (1:ℕ)) (g:=fun _ => 2)).symm

theorem giantCandidateCoinTerms_card_log_eventually :
    ∀ᶠ x : ℝ in atTop, ∀ threshold : ℝ,
      ((giantCandidateCoinTerms x threshold).card:ℝ) ≤
        (Real.log x)^(giantCandidateGroupLogRate*Real.log 3) := by
  filter_upwards [giantCandidateSelectedGroups_exponential_cost_eventually 3 (by norm_num)] with x hx
  intro threshold
  have hcard : ((giantCandidateCoinTerms x threshold).card:ℝ) ≤
      (3:ℝ)^Fintype.card (GiantCandidateGroupIndex x) := by
    exact_mod_cast giantCandidateCoinTerms_card x threshold
  exact hcard.trans (by simpa only [card_univ] using hx univ)

end
end ArtinMatthews

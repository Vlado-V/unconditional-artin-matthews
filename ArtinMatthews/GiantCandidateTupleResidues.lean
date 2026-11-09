module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! The original ordered tuple carrier in a full product box is finite.
Every residue fiber is a literal product of coordinate fibers. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

def giantCandidateTupleResidues {j : ℕ} (Q : ℕ) (t : Fin j → ℕ) : Fin j → ZMod Q :=
  fun i => (t i:ZMod Q)

def giantCandidateTupleResidueMask {j Q : ℕ} (S : Fin j → Finset ℕ)
    (E : Finset (Fin j → ZMod Q)) : Finset (Fin j → ℕ) :=
  (Fintype.piFinset S).filter (fun t => giantCandidateTupleResidues Q t ∈ E)

theorem giantCandidateTupleResidueMask_card {j Q : ℕ} (S : Fin j → Finset ℕ)
    (E : Finset (Fin j → ZMod Q)) :
    (giantCandidateTupleResidueMask S E).card =
      ∑ a ∈ E,∏ i,((S i).filter (fun n : ℕ => (n:ZMod Q)=a i)).card := by
  classical
  let T := giantCandidateTupleResidueMask S E
  let f := giantCandidateTupleResidues (j:=j) Q
  have hmaps : ∀ t∈T,f t∈E := fun _ ht => (mem_filter.mp ht).2
  have h := sum_fiberwise_of_maps_to hmaps (fun _ => (1:ℕ))
  simp only [sum_const,nsmul_eq_mul,mul_one] at h
  calc
    _ = ∑ a ∈ E,(T.filter (fun t => f t=a)).card := h.symm
    _ = _ := by
      apply sum_congr rfl
      intro a ha
      have hf : T.filter (fun t => f t=a) =
          Fintype.piFinset (fun i => (S i).filter (fun n : ℕ => (n:ZMod Q)=a i)) := by
        ext t
        simp only [T,giantCandidateTupleResidueMask,mem_filter,Fintype.mem_piFinset]
        constructor
        · rintro ⟨⟨ht,_⟩,hEq⟩ i
          exact ⟨ht i,congrFun hEq i⟩
        · intro ht
          have hEq : f t=a := funext (fun i => (ht i).2)
          have hmem : f t ∈ E := hEq.symm ▸ ha
          exact ⟨⟨fun i => (ht i).1,hmem⟩,hEq⟩
      rw [hf,Fintype.card_piFinset]

def giantCandidateTupleResidueMass {j Q : ℕ} (S : Fin j → Finset ℕ)
    (E : Finset (Fin j → ZMod Q)) : ℝ :=
  ((giantCandidateTupleResidueMask S E).card:ℝ)/((Fintype.piFinset S).card:ℝ)

def giantCandidateUniformResidueMass {j Q : ℕ} (E : Finset (Fin j → ZMod Q)) : ℝ :=
  (E.card:ℝ)/(Q:ℝ)^j

theorem giantCandidateTupleResidueMass_eq_sum {j Q : ℕ} (S : Fin j → Finset ℕ)
    (E : Finset (Fin j → ZMod Q)) :
    giantCandidateTupleResidueMass S E =
      ∑ a ∈ E,∏ i,(((S i).filter (fun n : ℕ => (n:ZMod Q)=a i)).card:ℝ)/((S i).card:ℝ) := by
  unfold giantCandidateTupleResidueMass
  rw [giantCandidateTupleResidueMask_card,Fintype.card_piFinset,Nat.cast_sum,sum_div]
  apply sum_congr rfl
  intro a _
  simp only [Nat.cast_prod,div_eq_mul_inv,prod_mul_distrib,prod_inv_distrib]

theorem giantCandidateTupleResidueMass_bounds {j Q : ℕ} (hQ : 0 < Q)
    (S : Fin j → Finset ℕ) (E : Finset (Fin j → ZMod Q)) {ε : ℝ} (hε : ε≤1)
    (hslot : ∀ i (a : ZMod Q),
      |(Q:ℝ)*(((S i).filter (fun n : ℕ => (n:ZMod Q)=a)).card:ℝ)/((S i).card:ℝ)-1|≤ε) :
    (1-ε)^j*giantCandidateUniformResidueMass E ≤ giantCandidateTupleResidueMass S E ∧
      giantCandidateTupleResidueMass S E ≤ (1+ε)^j*giantCandidateUniformResidueMass E := by
  let f (i : Fin j) (a : ZMod Q) : ℝ :=
    (((S i).filter (fun n : ℕ => (n:ZMod Q)=a)).card:ℝ)/((S i).card:ℝ)
  have hQ₀ : (0:ℝ)<Q := Nat.cast_pos.mpr hQ
  have hf₀ (i : Fin j) (a : ZMod Q) : 0 ≤ f i a :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have h (i : Fin j) (a : ZMod Q) : (1-ε)/(Q:ℝ) ≤ f i a ∧ f i a ≤ (1+ε)/(Q:ℝ) := by
    have h := abs_le.mp (hslot i a)
    have he : f i a*(Q:ℝ) = (Q:ℝ)*(((S i).filter (fun n : ℕ => (n:ZMod Q)=a)).card:ℝ)/((S i).card:ℝ) := by
      dsimp only [f]
      ring
    rw [← he] at h
    exact ⟨(div_le_iff₀ hQ₀).mpr (by linarith only [h.1]),(le_div_iff₀ hQ₀).mpr (by linarith only [h.2])⟩
  have hprod₁ (a : Fin j → ZMod Q) : ((1-ε)/(Q:ℝ))^j ≤ ∏ i,f i (a i) := by
    have hle := prod_le_prod₀ (s:=(univ : Finset (Fin j)))
      (fun _ _ => div_nonneg (sub_nonneg.mpr hε) hQ₀.le) (fun i _ => (h i (a i)).1)
    simpa only [prod_const,card_univ,Fintype.card_fin] using hle
  have hprod₂ (a : Fin j → ZMod Q) : (∏ i,f i (a i)) ≤ ((1+ε)/(Q:ℝ))^j := by
    have hle := prod_le_prod₀ (s:=(univ : Finset (Fin j))) (fun i _ => hf₀ i (a i))
      (fun i _ => (h i (a i)).2)
    simpa only [prod_const,card_univ,Fintype.card_fin] using hle
  rw [giantCandidateTupleResidueMass_eq_sum]
  change (1-ε)^j*((E.card:ℝ)/(Q:ℝ)^j) ≤ (∑ a∈E,∏ i,f i (a i)) ∧
    (∑ a∈E,∏ i,f i (a i)) ≤ (1+ε)^j*((E.card:ℝ)/(Q:ℝ)^j)
  constructor
  · calc
      _ = ∑ _a∈E,((1-ε)/(Q:ℝ))^j := by
        rw [sum_const,nsmul_eq_mul,div_pow]
        ring
      _ ≤ _ := sum_le_sum (fun a _ => hprod₁ a)
  · calc
      _ ≤ ∑ _a∈E,((1+ε)/(Q:ℝ))^j := sum_le_sum (fun a _ => hprod₂ a)
      _ = _ := by
        rw [sum_const,nsmul_eq_mul,div_pow]
        ring

end
end ArtinMatthews

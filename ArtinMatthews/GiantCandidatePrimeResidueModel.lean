module

public import ArtinMatthews.GiantCandidateActualResidues
public import ArtinMatthews.GiantCandidateTupleResidues
public import Mathlib.Data.ZMod.QuotientRing


set_option backward.privateInPublic true
@[expose] public section

/-! The candidate residue model is the product of the actual residue
rings at the selected primes. Its event masses factor exactly. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

def giantCandidateResidueCRTEquiv (U : Finset ℕ) (hP : ∀ p∈U,p.Prime) :
    ZMod (giantCandidateResidueModulus U) ≃+* ∀ p : U,ZMod p.val := by
  have hprod : (∏ p : U,p.val) = giantCandidateResidueModulus U :=
    prod_coe_sort U (fun p : ℕ => p)
  have hcop : Pairwise (fun p q : U => p.val.Coprime q.val) := by
    intro p q hpq
    exact (Nat.coprime_primes (hP p.val p.property) (hP q.val q.property)).mpr
      (fun he => hpq (Subtype.ext he))
  exact (ZMod.ringEquivCongr hprod.symm).trans (ZMod.prodEquivPi (fun p : U => p.val) hcop)

def giantCandidateTupleCRTEquiv (U : Finset ℕ) (hP : ∀ p∈U,p.Prime) (j : ℕ) :
    (Fin j → ZMod (giantCandidateResidueModulus U)) ≃ (∀ p : U,Fin j → ZMod p.val) :=
  (Equiv.piCongrRight (fun _ : Fin j => (giantCandidateResidueCRTEquiv U hP).toEquiv)).trans
    (Equiv.piComm (fun (_ : Fin j) (p : U) => ZMod p.val))

theorem giantCandidateTupleCRTEquiv_natCast (U : Finset ℕ) (hP : ∀ p∈U,p.Prime)
    {j : ℕ} (t : Fin j → ℕ) (p : U) (i : Fin j) :
    giantCandidateTupleCRTEquiv U hP j (giantCandidateTupleResidues (giantCandidateResidueModulus U) t) p i =
      (t i:ZMod p.val) := by
  change giantCandidateResidueCRTEquiv U hP (t i:ZMod (giantCandidateResidueModulus U)) p = _
  simp only [map_natCast,Pi.natCast_apply]

def giantCandidatePrimeCRTMask (U : Finset ℕ) (hP : ∀ p∈U,p.Prime)
    {j : ℕ} (E : ∀ p : U,Finset (Fin j → ZMod p.val)) :
    Finset (Fin j → ZMod (giantCandidateResidueModulus U)) :=
  (Fintype.piFinset E).map (giantCandidateTupleCRTEquiv U hP j).symm.toEmbedding

theorem mem_giantCandidatePrimeCRTMask (U : Finset ℕ) (hP : ∀ p∈U,p.Prime)
    {j : ℕ} (E : ∀ p : U,Finset (Fin j → ZMod p.val))
    (a : Fin j → ZMod (giantCandidateResidueModulus U)) :
    a∈giantCandidatePrimeCRTMask U hP E ↔ ∀p,giantCandidateTupleCRTEquiv U hP j a p∈E p := by
  let e := giantCandidateTupleCRTEquiv U hP j
  simp only [giantCandidatePrimeCRTMask,mem_map,Equiv.coe_toEmbedding,Fintype.mem_piFinset]
  change (∃ b, (∀ p,b p∈E p) ∧ e.symm b=a) ↔ _
  constructor
  · rintro ⟨b,hb,he⟩
    have heq : b=e a := by rw [← he,e.apply_symm_apply]
    exact heq ▸ hb
  · intro h
    exact ⟨e a,h,e.symm_apply_apply a⟩

theorem giantCandidatePrimeCRTMask_uniformMass (U : Finset ℕ) (hP : ∀ p∈U,p.Prime)
    {j : ℕ} (E : ∀ p : U,Finset (Fin j → ZMod p.val)) :
    giantCandidateUniformResidueMass (giantCandidatePrimeCRTMask U hP E) =
      ∏ p : U,((E p).card:ℝ)/(p.val:ℝ)^j := by
  unfold giantCandidateUniformResidueMass giantCandidatePrimeCRTMask
  rw [card_map,Fintype.card_piFinset]
  have hQ : (giantCandidateResidueModulus U:ℝ)^j = ∏ p : U,(p.val:ℝ)^j := by
    have hp : (∏ p : U,p.val) = giantCandidateResidueModulus U :=
      prod_coe_sort U (fun p : ℕ => p)
    rw [prod_pow,← Nat.cast_prod,hp]
  rw [hQ]
  simp only [Nat.cast_prod,div_eq_mul_inv,prod_mul_distrib,prod_inv_distrib]

def giantCandidatePrimeTupleMask {U : Finset ℕ} {j : ℕ} (S : Fin j → Finset ℕ)
    (E : ∀ p : U,Finset (Fin j → ZMod p.val)) : Finset (Fin j → ℕ) :=
  (Fintype.piFinset S).filter (fun t => ∀p,(fun i => (t i:ZMod p.val))∈E p)

theorem giantCandidatePrimeTupleMask_eq_residueMask (U : Finset ℕ) (hP : ∀ p∈U,p.Prime)
    {j : ℕ} (S : Fin j → Finset ℕ) (E : ∀ p : U,Finset (Fin j → ZMod p.val)) :
    giantCandidatePrimeTupleMask S E = giantCandidateTupleResidueMask S (giantCandidatePrimeCRTMask U hP E) := by
  ext t
  simp only [giantCandidatePrimeTupleMask,giantCandidateTupleResidueMask,mem_filter,mem_giantCandidatePrimeCRTMask]
  apply and_congr_right
  intro _
  have he (p : U) :
      giantCandidateTupleCRTEquiv U hP j (giantCandidateTupleResidues (giantCandidateResidueModulus U) t) p =
        fun i => (t i:ZMod p.val) :=
    funext (giantCandidateTupleCRTEquiv_natCast U hP t p)
  simp only [he]

end
end ArtinMatthews

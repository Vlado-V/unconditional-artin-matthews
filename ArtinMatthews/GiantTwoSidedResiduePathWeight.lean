module

public import ArtinMatthews.GiantTwoSidedResiduePathFactor
public import ArtinMatthews.GiantTwoSidedResidueInitialMass


set_option backward.privateInPublic true
@[expose] public section

/-! The exact independent residue path coefficient separates into the
original root scalar and the full Haar-coordinate visit factor. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantTwoSidedResidueRoot_coefficient {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) {k ell n : ℕ}
    {C : Fin (n+1) → J → Finset (Fin k)}
    {π τ : Fin (n+1) → J → Equiv.Perm (Fin (k+ell))}
    {aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)} {step : Fin (n+1) → ℤ}
    (d : GiantTwoSidedResidueRootPath C π τ aux step) {q : ℝ} (hq : 0 ≤ q)
    (ζ : Fin (n+1) → ℝ) (K : ∀ i,GiantTwoSidedPatternCoefficient P (C i) ell) :
    (markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell):ℂ)*
      (∏ i : Fin (n+1),giantTwoSidedResiduePatternCoefficient (step i) q (ζ i) (K i)
        (giantTwoSidedResiduePermute (π i) (giantTwoSidedResidueRoot_reconstruct d i.castSucc))
        (giantTwoSidedResiduePermute (τ i) (giantTwoSidedResidueRoot_reconstruct d i.succ)) (aux i))=
      giantTwoSidedRootScalar C d.val.2 π τ aux ζ K*
        (giantTwoSidedIndependentResidueFactor P d.val.2 q
          (giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C d.val.2 π aux step)) d.val.1:ℂ) := by
  have hd := congrArg (fun x : ℝ => (x:ℂ)) (giantTwoSidedResidueRoot_damping_factor hP hdis d hq)
  have hc (i : Fin (n+1)) :
      giantTwoSidedResiduePatternCoefficient (step i) q (ζ i) (K i)
        (giantTwoSidedResiduePermute (π i) (giantTwoSidedResidueRoot_reconstruct d i.castSucc))
        (giantTwoSidedResiduePermute (τ i) (giantTwoSidedResidueRoot_reconstruct d i.succ)) (aux i)=
      (giantTwoSidedPatternAuxiliaryMass (aux i):ℂ)*
        (giantTwoSidedPatternFreshMass P (C i) ell:ℂ)*
        K i (giantTwoSidedPermuteLabels (π i) (d.val.2 i.castSucc))
          (giantTwoSidedPermuteLabels (τ i) (d.val.2 i.succ)) (aux i)*
        (giantTwoSidedPatternDilation (C i)
          (giantTwoSidedPermuteLabels (π i) (d.val.2 i.castSucc)) (aux i):ℂ)^((ζ i:ℂ)*Complex.I)*
        (giantTwoSidedResidueDamping P (k+ell) q (giantTwoSidedResidueRoot_reconstruct d i.castSucc).val.1:ℂ)*
        (giantTwoSidedResidueDamping P (k+ell) q (giantTwoSidedResidueRoot_reconstruct d i.succ).val.1:ℂ) := by
    rw [giantTwoSidedResiduePatternCoefficient,
      ite_eq_left (giantTwoSidedResidueRoot_reconstruct_condition d i)]
    rfl
  rw [← hd]
  unfold giantTwoSidedRootScalar
  simp only [hc,Complex.ofReal_prod,Complex.ofReal_mul,prod_mul_distrib]
  ring

theorem giantTwoSidedResidueRoot_absolute_coefficient {J : Type*} [Fintype J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val]
    (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hV : ∀ j,0 < bandReciprocalMass (P j)) {k ell n : ℕ}
    {C : Fin (n+1) → J → Finset (Fin k)}
    {π τ : Fin (n+1) → J → Equiv.Perm (Fin (k+ell))}
    {aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)} {step : Fin (n+1) → ℤ}
    (d : GiantTwoSidedResidueRootPath C π τ aux step) {q : ℝ} (hq : 0 ≤ q)
    (ζ : Fin (n+1) → ℝ) (K : ∀ i,GiantTwoSidedPatternCoefficient P (C i) ell) :
    giantTwoSidedResidueHaarStateMass P (k+ell)*
      (∏ i : Fin (n+1),‖giantTwoSidedResiduePatternCoefficient (step i) q (ζ i) (K i)
        (giantTwoSidedResiduePermute (π i) (giantTwoSidedResidueRoot_reconstruct d i.castSucc))
        (giantTwoSidedResiduePermute (τ i) (giantTwoSidedResidueRoot_reconstruct d i.succ)) (aux i)‖)=
      (‖giantTwoSidedRootScalar C d.val.2 π τ aux ζ K‖/Fintype.card (GiantTwoSidedFullResidue P))*
        giantTwoSidedIndependentResidueFactor P d.val.2 q
          (giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C d.val.2 π aux step)) d.val.1 := by
  have hσ := markedPhysicalMass_nonneg (fun j => bandReciprocalMass (P j)) (k+ell) (fun j => (hV j).le)
  have hf := giantTwoSidedIndependentResidueFactor_nonneg P d.val.2 hq
    (giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C d.val.2 π aux step)) d.val.1
  have hw := congrArg norm (giantTwoSidedResidueRoot_coefficient hP hdis d hq ζ K)
  simp only [norm_mul,norm_prod,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hσ,abs_of_nonneg hf] at hw
  rw [giantTwoSidedResidueHaarStateMass_eq,div_mul_eq_mul_div,hw]
  ring

end
end ArtinMatthews

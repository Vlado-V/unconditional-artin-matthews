module

public import ArtinMatthews.FiniteAbsolutePathMass
public import ArtinMatthews.GiantTwoSidedResidueInitialMass


set_option backward.privateInPublic true
@[expose] public section

/-! The actual pattern and independent slot averages have finite path
mass bounded by the row estimate, with the terminal state unrestricted. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def giantTwoSidedResidueFamilyAbsoluteEntry {I J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell : ℕ} (patterns : Finset I) (C : I → J → Finset (Fin k))
    (step : ℤ) (q ζ : ℝ) (K : ∀ ν,GiantTwoSidedPatternCoefficient P (C ν) ell)
    (s t : GiantTwoSidedResidueState P (k+ell)) : ℝ :=
  ∑ ν∈patterns,giantTwoSidedResidueSlotAverage
    (giantTwoSidedResiduePatternAbsoluteEntry step q ζ (K ν)) s t

theorem giantTwoSidedResidueFamilyAbsoluteEntry_nonneg {I J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell : ℕ} (patterns : Finset I) (C : I → J → Finset (Fin k))
    (step : ℤ) (q ζ : ℝ) (K : ∀ ν,GiantTwoSidedPatternCoefficient P (C ν) ell)
    (s t : GiantTwoSidedResidueState P (k+ell)) :
    0 ≤ giantTwoSidedResidueFamilyAbsoluteEntry patterns C step q ζ K s t := by
  apply sum_nonneg
  intro ν _
  apply div_nonneg _ (sq_nonneg _)
  exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _

def giantTwoSidedResidueFamilyPathMass {I J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val]
    {k ell n : ℕ} (patterns : Fin n → Finset I) (C : Fin n → I → J → Finset (Fin k))
    (step : Fin n → ℤ) (q : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i ν,GiantTwoSidedPatternCoefficient P (C i ν) ell) : ℝ :=
  finiteAbsolutePathMass n (fun _ : GiantTwoSidedResidueState P (k+ell) =>
    giantTwoSidedResidueHaarStateMass P (k+ell))
      (fun i => giantTwoSidedResidueFamilyAbsoluteEntry (patterns i) (C i) (step i) q (ζ i) (K i))

theorem giantTwoSidedResidueFamilyPathMass_le {I J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val]
    (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) (hV : ∀ j,0 < bandReciprocalMass (P j))
    {k ell n : ℕ} (patterns : Fin n → Finset I) (C : Fin n → I → J → Finset (Fin k))
    (step : Fin n → ℤ) (q : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i ν,GiantTwoSidedPatternCoefficient P (C i ν) ell) {B : ℝ} (hB : 0 ≤ B)
    (hrow : ∀ i (s : GiantTwoSidedResidueState P (k+ell)),
      (∑ t,giantTwoSidedResidueFamilyAbsoluteEntry (patterns i) (C i) (step i) q (ζ i) (K i) s t) ≤ B) :
    giantTwoSidedResidueFamilyPathMass patterns C step q ζ K ≤ B^n := by
  apply finiteAbsolutePathMass_le_of_initial_le_one
  · intro _
    exact div_nonneg (markedPhysicalMass_nonneg _ _ (fun j => (hV j).le)) (Nat.cast_nonneg _)
  · exact giantTwoSidedResidue_initialMass_le_one P hP hdis hV (k+ell)
  · exact hB
  · exact fun i s t => giantTwoSidedResidueFamilyAbsoluteEntry_nonneg _ _ _ _ _ _ s t
  · exact hrow

theorem giantCandidateResidueFamily_pathMass_eventually {I : Type*} (ell m₀ : ℕ)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (C₁ : ℝ) :
    ∃ A : ℝ,0 ≤ A ∧ ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      let P (j : S) := giantCandidateGroup x j.val
      ∀ (nz : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val),
      letI : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val := nz
      ∀ (k n : ℕ) (patterns : Fin n → Finset I) (C : Fin n → I → S → Finset (Fin k)),
        (∀ i ν,ν∈patterns i → ∀ j,(C i ν j).card ≤ m₀) →
      ∀ (step : Fin n → ℤ) (ζ : Fin n → ℝ)
        (K : ∀ i ν,GiantTwoSidedPatternCoefficient P (C i ν) ell) (K₀ : Fin n → I → ℝ),
        (∀ i ν,ν∈patterns i → 0 ≤ K₀ i ν ∧ ∀ b c a,‖K i ν b c a‖ ≤ K₀ i ν) →
        (∀ i,(∑ ν∈patterns i,K₀ i ν) ≤ (Real.log x)^C₁) →
        giantTwoSidedResidueFamilyPathMass patterns C step q ζ K ≤ ((Real.log x)^(C₁+A))^n := by
  obtain ⟨A,hA,h⟩ := giantCandidateResiduePatternFamily_absolute_rows_columns_eventually (I:=I) ell m₀ hq hq1 C₁
  refine ⟨A,hA,?_⟩
  filter_upwards [h,giantCandidateSelectedGroups_geometry_eventually,
    giantCandidateFullPrimes_prime_upper_eventually,
    Real.tendsto_log_atTop.eventually_gt_atTop (0:ℝ)] with x hx hgeo hprime hL
  intro S
  let P (j : S) := giantCandidateGroup x j.val
  dsimp only
  intro nz
  let : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val := nz
  intro k n patterns C hC step ζ K K₀ hK hmass
  have hP (j : S) (p : ℕ) (hp : p∈P j) : p.Prime :=
    (hprime p (mem_giantCandidateFullPrimes.mpr ⟨j.val,hp⟩)).1
  have hV (j : S) : 0 < bandReciprocalMass (P j) :=
    (div_pos (Real.log_pos (by norm_num)) (by norm_num)).trans ((hgeo S).2.1 j).1
  apply giantTwoSidedResidueFamilyPathMass_le hP (hgeo S).1 hV patterns C step q ζ K
    (Real.rpow_nonneg hL.le _)
  intro i s
  exact (hx S nz k (patterns i) (C i) (fun ν hν => hC i ν hν) (step i) (ζ i)
    (K i) (K₀ i) (fun ν hν => hK i ν hν) (hmass i)).1 s

end
end ArtinMatthews

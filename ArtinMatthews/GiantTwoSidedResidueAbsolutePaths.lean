module

public import ArtinMatthews.GiantTwoSidedResiduePathExpansion


set_option backward.privateInPublic true
@[expose] public section

/-! The fully expanded positive-length Haar path mass obeys the same
logarithmic bound as the actual absolute transition matrix. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantCandidateResidueExpandedRoot_pathMass_eventually {I : Type*} (ell m₀ : ℕ)
    {q : ℝ} (hq : 0<q) (hq1 : q<1) (C₁ : ℝ) :
    ∃ A : ℝ,0 ≤ A ∧ ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      let P (j : S) := giantCandidateGroup x j.val
      ∀ (nz : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val),
      letI : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val := nz
      ∀ (k n : ℕ),n≠0 →
      ∀ (patterns : Fin n → Finset I) (C : Fin n → I → S → Finset (Fin k)),
        (∀ i ν,ν∈patterns i → ∀ j,(C i ν j).card ≤ m₀) →
      ∀ (step : Fin n → ℤ) (ζ : Fin n → ℝ)
        (K : ∀ i ν,GiantTwoSidedPatternCoefficient P (C i ν) ell) (K₀ : Fin n → I → ℝ),
        (∀ i ν,ν∈patterns i → 0 ≤ K₀ i ν ∧ ∀ b c a,‖K i ν b c a‖ ≤ K₀ i ν) →
        (∀ i,(∑ ν∈patterns i,K₀ i ν) ≤ (Real.log x)^C₁) →
        giantTwoSidedResidueExpandedRootMass patterns C step q ζ K ≤ ((Real.log x)^(C₁+A))^n := by
  obtain ⟨A,hA,h⟩ := giantCandidateResidueFamily_pathMass_eventually (I:=I) ell m₀ hq hq1 C₁
  refine ⟨A,hA,?_⟩
  filter_upwards [h,giantCandidateSelectedGroups_geometry_eventually,
    giantCandidateFullPrimes_prime_upper_eventually] with x hx hgeo hprime
  intro S
  let P (j : S) := giantCandidateGroup x j.val
  dsimp only
  intro nz
  let : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val := nz
  intro k n hn
  cases n with
  | zero => exact (hn rfl).elim
  | succ n =>
    intro patterns C hC step ζ K K₀ hK hmass
    have hP (j : S) (p : ℕ) (hp : p∈P j) : p.Prime :=
      (hprime p (mem_giantCandidateFullPrimes.mpr ⟨j.val,hp⟩)).1
    have hV (j : S) : 0<bandReciprocalMass (P j) :=
      (div_pos (Real.log_pos (by norm_num)) (by norm_num)).trans ((hgeo S).2.1 j).1
    rw [giantTwoSidedResidueExpandedRootMass_eq hP (hgeo S).1 hV patterns C step hq.le ζ K]
    exact hx S nz k (n+1) patterns C hC step ζ K K₀ hK hmass

end
end ArtinMatthews

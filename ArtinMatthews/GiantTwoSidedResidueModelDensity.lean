module

public import ArtinMatthews.GiantTwoSidedResidueDensity
public import ArtinMatthews.GiantTwoSidedRootRelative


set_option backward.privateInPublic true
@[expose] public section

/-! The fixed-label product density in the arithmetic replacement is
exactly the full independent Haar expectation of the same visit factor. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section

theorem giantCandidateIndependentResidueMean_eq_rootDensity :
    ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      let P (j : S) := giantCandidateGroup x j.val
      ∀ (nz : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val),
      letI : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val := nz
      ∀ (M : ℕ) (labels : Fin (giantTwoSidedSourceMomentLength x+1) → MarkedPhysicalMarking P M)
        (q : ℝ) (offset : Fin (giantTwoSidedSourceMomentLength x+1) → ℤ),
        giantTwoSidedIndependentResidueMean labels q offset=giantTwoSidedRootDensity x S labels q offset := by
  filter_upwards [giantCandidateSelectedGroups_geometry_eventually,
    giantCandidateFullPrimes_prime_upper_eventually] with x hgeo hprime
  intro S
  let P (j : S) := giantCandidateGroup x j.val
  dsimp only
  intro nz
  let : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val := nz
  intro M labels q offset
  have hP (j : S) (p : ℕ) (hp : p∈P j) : p.Prime :=
    (hprime p (mem_giantCandidateFullPrimes.mpr ⟨j.val,hp⟩)).1
  exact giantTwoSidedIndependentResidueMean_density hP (hgeo S).1 labels q offset

end
end ArtinMatthews

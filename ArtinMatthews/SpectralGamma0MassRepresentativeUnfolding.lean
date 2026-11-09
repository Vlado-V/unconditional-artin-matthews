module

public import ArtinMatthews.SpectralGamma0GlobalPairing


set_option backward.privateInPublic true
@[expose] public section

/-! Actual full ambient mass pairings unfold against a continuous invariant
representative, with the genuine central multiplicity two. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

theorem gamma0Mass_inner_unfold_representative (N : ℕ) [NeZero N]
    (M : Gamma0RegionL2 N) (F : UpperHalfPlane → ℂ) (hF : Continuous F)
    (hFinv : ∀ g : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, F (g.val • z)=F z)
    (hM : ∀ q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
      (M q : UpperHalfPlane → ℂ)=ᵐ[volume.restrict ModularGroup.fd] (fun z => F (q.out⁻¹ • z)))
    (ψ : h2SmoothCompactSeeds) :
    inner ℂ (gamma0SmoothSeedMass N ψ) M=2*∫ z : UpperHalfPlane, inner ℂ (ψ.val z) (F z) := by
  rw [PiLp.inner_apply]
  calc
    _=∑ q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
      ∫ z in ModularGroup.fd, inner ℂ (gamma0PoincareSeed N ψ.val (q.out⁻¹ • z)) (F (q.out⁻¹ • z)) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [gamma0SeedMass_coeFn N ψ.val q,hM q] with z hψ hMz
      change inner ℂ ((gamma0SeedMass N ψ.val q) z) (M q z)=_
      rw [hψ,hMz]
    _=_ := gamma0_periodization_unfold_inner N F hF hFinv ψ.val

end ArtinMatthews

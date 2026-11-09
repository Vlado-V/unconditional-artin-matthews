module

public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeFreshInteger
public import ArtinMatthews.MarkedMinorArcBanRawCollision


set_option backward.privateInPublic true
@[expose] public section

/-! Exact actual-band fresh-law transport in the edge row, preserving the
literal integer product and the unnormalized tilted measure. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

theorem markedDirtyActualFresh_expectation_eq {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (q x : ℝ) (f : ℤ → ℝ) :
    (∑ fresh : (j : J) → ↥(markedRawActualPrimeBand e x j),
      finiteProductMass (markedRawActualPrimeAtom e q x) fresh*
        f (markedDirtyRawFreshIntegerProduct fresh)) =
      ∑ fresh : MarkedFreshPrimeTuple e x,
        markedFreshTiltedLaw e q x fresh*f (markedFreshIntegerProduct e x fresh) := by
  classical
  rw [← Equiv.sum_comp (markedBanRawLastEquiv e x) (fun fresh =>
    markedFreshTiltedLaw e q x fresh*f (markedFreshIntegerProduct e x fresh))]
  apply Finset.sum_congr rfl
  intro fresh _
  have hm := markedBanRawLastMass_eq e q x fresh
  have hp := markedBanRawLastProduct_eq e x fresh
  rw [markedDirtyRawFreshIntegerProduct_eq,hp]
  exact congrArg (fun c => c*f (markedFreshIntegerProduct e x (markedBanRawLastEquiv e x fresh))) hm

end ArtinMatthews

module

public import ArtinMatthews.KloostermanWeightedStationary
public import Mathlib.Data.ZMod.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! The square-residue weight is invariant under every additive unit
shift which vanishes in the smaller quotient. -/
namespace ArtinMatthews
open OAI.Erdos970.ErdosKloosterman.PrimePower
noncomputable section
variable {R S : Type*} [CommRing R] [CommRing S]
attribute [local instance] Classical.decEq

def doubleVoronoiResidueWeight (f : R →+* S) (m₄ k₁ : R) (u : Rˣ) : ℂ :=
  if f k₁ = (f m₄ * f (u : R))^2 then 1 else 0

theorem doubleVoronoiResidueWeight_shift (f : R →+* S) (m₄ k₁ : R)
    (u : Rˣ) (h : R) (hh : h^2=0) (hf : f h=0) :
    doubleVoronoiResidueWeight f m₄ k₁ (shiftUnit u h hh) =
      doubleVoronoiResidueWeight f m₄ k₁ u := by
  simp only [doubleVoronoiResidueWeight, shiftUnit_val, map_add, hf, add_zero]

/-- The q/D shift and all its multiples vanish modulo d whenever
 d divides q/D. -/
theorem doubleVoronoiResidueWeight_quotient_shift {q d D : ℕ}
    (hdq : d∣q) (hdquot : d∣q/D) (m₄ k₁ : ZMod q)
    (u : (ZMod q)ˣ) (z : ZMod q) (hh : (((q/D : ℕ) : ZMod q)*z)^2=0) :
    doubleVoronoiResidueWeight (ZMod.castHom hdq (ZMod d)) m₄ k₁
      (shiftUnit u (((q/D : ℕ) : ZMod q)*z) hh) =
    doubleVoronoiResidueWeight (ZMod.castHom hdq (ZMod d)) m₄ k₁ u := by
  apply doubleVoronoiResidueWeight_shift
  rw [map_mul, map_natCast, (ZMod.natCast_eq_zero_iff _ _).mpr hdquot, zero_mul]

end
end ArtinMatthews

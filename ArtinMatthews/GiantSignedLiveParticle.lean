module

public import ArtinMatthews.GiantSignedEdgeMemory
public import ArtinMatthews.GiantSignedGhostLiveOrigin
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! A live active slot carries residue zero. An old ghost survivor
retains its residue and an appended birth starts at zero. -/
namespace ArtinMatthews
noncomputable section

def giantSignedLiveParticle {P : Finset ℕ} {M : ℕ}
    (active : Fin M → P) (m : GiantSignedGroupMemory P) :
    GiantSignedLiveSlots M m.1 → GiantSignedParticle P :=
  Sum.elim (fun i => giantSignedParticleAt 0 (active i)) m.2

theorem giantSignedLiveParticle_prime {P : Finset ℕ} {M : ℕ}
    (active : Fin M → P) (m : GiantSignedGroupMemory P) (s : GiantSignedLiveSlots M m.1) :
    (giantSignedLiveParticle active m s).1 = giantSignedLivePrime active m s := by
  cases s <;> rfl

theorem giantSignedGhostLiveOrigin_particle {P : Finset ℕ} {M b : ℕ}
    (active : Fin M → P) (m : GiantSignedGroupMemory P) (deleted : Finset (Fin m.1))
    (born : Fin b → P) (s : GiantSignedLiveSlots M (giantSignedGhostTarget m deleted born).1) :
    giantSignedLiveParticle active (giantSignedGhostTarget m deleted born) s =
      Sum.elim (giantSignedLiveParticle active m) (fun i => giantSignedParticleAt 0 (born i))
        (giantSignedGhostLiveOrigin M m deleted born s) := by
  rcases s with i | i
  · rfl
  · change Fin ((deletedᶜ).card+b) at i
    refine Fin.addCases ?_ ?_ i
    · intro j
      rw [giantSignedGhostLiveOrigin_survivor]
      exact giantSignedGhostTarget_survivor m deleted born j
    · intro j
      rw [giantSignedGhostLiveOrigin_born]
      change (giantSignedGhostTarget m deleted born).2 (Fin.natAdd (deletedᶜ).card j) =
        giantSignedParticleAt 0 (born j)
      simpa only [giantSignedParticleAt, Int.cast_zero] using giantSignedGhostTarget_born m deleted born j

end
end ArtinMatthews

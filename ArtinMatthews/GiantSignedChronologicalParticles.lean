module

public import ArtinMatthews.GiantSignedChronologicalOrigins
public import ArtinMatthews.GiantSignedLiveParticle
public import ArtinMatthews.GiantSignedRawEdgeLiveParticle
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

/-! Local chronological particle equations on the same checked origin maps. -/
namespace ArtinMatthews
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n M : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}

def giantSignedStateLiveParticle (s : GiantSignedState PS PB M) (g : B) :
    GiantSignedStateLiveSlots s g → GiantSignedParticle (PB g) :=
  giantSignedLiveParticle (s.2.1 g) (giantSignedMemoryGroupEquiv PB s.2.2 g)

theorem giantSignedStateLiveParticle_prime (s : GiantSignedState PS PB M) (g : B)
    (z : GiantSignedStateLiveSlots s g) :
    (giantSignedStateLiveParticle s g z).1 = giantSignedStateLivePrime s g z :=
  giantSignedLiveParticle_prime _ _ _

theorem giantSignedStateLiveEquiv_particle {s t : GiantSignedState PS PB M} (h : s = t)
    (g : B) (z : GiantSignedStateLiveSlots s g) :
    giantSignedStateLiveParticle t g (giantSignedStateLiveEquiv h g z) =
      giantSignedStateLiveParticle s g z := by
  subst t
  rfl

theorem giantSignedChronologicalVisitOrigin_particle
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (i : Fin (n+1)) (g : B)
    (z : GiantSignedStateLiveSlots (giantSignedChronologicalAfterVisitState h i) g) :
    giantSignedStateLiveParticle (giantSignedChronologicalAfterVisitState h i) g z =
      Sum.elim (giantSignedStateLiveParticle (h.state i) g) (fun u => giantSignedParticleAt 0 (h.born i g u))
        (giantSignedChronologicalVisitOrigin h i g z) :=
  giantSignedGhostLiveOrigin_particle _ _ _ _ z

theorem giantSignedChronologicalEdgeOrigin_particle (κ : Fin n → ℤ)
    (h : GiantSignedChronologicalChoices PS PB ell C batch)
    (ha : GiantSignedChronologicalAdmissible κ h) (i : Fin n) (g : B)
    (z : GiantSignedStateLiveSlots (h.state i.succ) g) :
    giantSignedStateLiveParticle (h.state i.succ) g z =
      Sum.elim (fun u => giantSignedParticleTranslate (κ i * (giantSignedChronologicalProduct h i : ℤ))
          (giantSignedStateLiveParticle (giantSignedChronologicalAfterVisitState h i.castSucc) g u))
        (fun u : {u : Fin (ell+(C i g).card) // u ∉ (h.edge i).2.1 g} =>
          giantSignedParticleAt 0
            (giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigTarget h i) g u.val))
        (giantSignedChronologicalEdgeOrigin κ h ha.compatible i g z) := by
  let s := giantSignedChronologicalAfterVisitState h i.castSucc
  let r := giantSignedChronologicalRawMove h i
  let e := giantSignedStateLiveEquiv
    (giantSignedChronologicalRawMove_target κ h ha.compatible i).symm g
  have he := giantSignedStateLiveEquiv_particle
    (giantSignedChronologicalRawMove_target κ h ha.compatible i).symm g z
  exact he.symm.trans (giantSignedRawEdgeLiveOrigin_particle (κ i) s r
    (giantSignedChronologicalRawMove_condition κ h ha.compatible i) (ha.promotion i).1 g (e z))

end
end ArtinMatthews

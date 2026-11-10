module

public import ArtinMatthews.GiantSignedLiveParticle
public import ArtinMatthews.GiantSignedEdgeLiveIndices
public import ArtinMatthews.GiantSignedGhostMemoryCoordinates
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

/-! The same raw index map also preserves particle displacement.
Copied active slots have shift zero in their own residue fields. -/
namespace ArtinMatthews
noncomputable section

variable {B : Type*} {PB : B → Finset ℕ} {k ell : ℕ}
    (C : B → Finset (Fin k)) (m : GiantSignedMemory PB)
    (a b : MarkedPhysicalMarking PB (k+ell))
    (c : GiantSignedEdgeChoice (fun g => ell+(C g).card) m.1) (d : ℤ)

theorem giantSignedEdgeLiveOrigin_particle (hcopy : IdealCopied C a b)
    (hzero : ∀ g (i : Fin k), i ∉ C g → (d : ZMod (a g (Fin.castAdd ell i)).val) = 0)
    (hhit : GiantSignedEdgeHits d m (giantSignedPatternFreeLabels C b) c) (g : B)
    (s : GiantSignedLiveSlots (k+ell)
      ((giantSignedEdgeTarget d m (giantSignedPatternFreeLabels C a) c).1 g)) :
    giantSignedLiveParticle (b g) (giantSignedMemoryGroupEquiv PB
        (giantSignedEdgeTarget d m (giantSignedPatternFreeLabels C a) c) g) s =
      Sum.elim (fun i => giantSignedParticleTranslate d
          (giantSignedLiveParticle (a g) (giantSignedMemoryGroupEquiv PB m g) i))
        (fun i : {i : Fin (ell+(C g).card) // i ∉ c.2.1 g} =>
          giantSignedParticleAt 0 (giantSignedPatternFreeLabels C b g i.val))
        (giantSignedEdgeLiveOrigin (C g) (c.1 g) (c.2.1 g) (c.2.2 g) s) := by
  let origin := giantSignedEdgeLiveOrigin (C g) (c.1 g) (c.2.1 g) (c.2.2 g)
  let old := giantSignedMemoryGroupEquiv PB m g
  let new := giantSignedMemoryGroupEquiv PB
    (giantSignedEdgeTarget d m (giantSignedPatternFreeLabels C a) c) g
  let L : GiantSignedLiveSlots (k+ell) (((Finset.univ.map (c.2.2 g))ᶜ).card+(c.1 g).card) →
      GiantSignedParticle (PB g) := giantSignedLiveParticle (b g) new
  let R : (GiantSignedLiveSlots (k+ell) (m.1 g) ⊕
      {i : Fin (ell+(C g).card) // i ∉ c.2.1 g}) → GiantSignedParticle (PB g) :=
    Sum.elim (fun i => giantSignedParticleTranslate d (giantSignedLiveParticle (a g) old i))
      (fun i => giantSignedParticleAt 0 (giantSignedPatternFreeLabels C b g i.val))
  change GiantSignedLiveSlots (k+ell) (((Finset.univ.map (c.2.2 g))ᶜ).card+(c.1 g).card) at s
  change L s = R (origin s)
  rcases s with i | i
  · obtain ⟨s, rfl⟩ := (giantSignedCanonicalSlotEquiv (C g) ell).symm.surjective i
    rcases s with j | j
    · let u := Fin.castAdd ell j.val
      have he : L (.inl u) = R (.inl (.inl u)) := by
        change giantSignedParticleAt 0 (b g u) = giantSignedParticleTranslate d
          (giantSignedParticleAt 0 (a g u))
        rw [hcopy g j.val j.property, giantSignedParticleTranslate_at, zero_add]
        unfold giantSignedParticleAt
        rw [hzero g j.val j.property, Int.cast_zero]
      exact he.trans (congrArg R (giantSignedEdgeLiveOrigin_copied (C g) (c.1 g) (c.2.1 g)
        (c.2.2 g) j)).symm
    · rw [giantSignedCanonicalSlotEquiv_symm_free]
      obtain ⟨s, rfl⟩ := (markedRawSubsetIndexEquiv (c.2.1 g)).surjective j
      rcases s with i | i
      · refine (hhit g i).symm.trans ?_
        exact (congrArg R (giantSignedEdgeLiveOrigin_promoted (C g) (c.1 g) (c.2.1 g)
          (c.2.2 g) i)).symm
      · let j : {j : Fin (ell+(C g).card) // j ∉ c.2.1 g} :=
          ⟨((c.2.1 g)ᶜ).orderEmbOfFin rfl i,
            Finset.mem_compl.mp (((c.2.1 g)ᶜ.orderIsoOfFin rfl) i).property⟩
        exact (congrArg R (giantSignedEdgeLiveOrigin_fresh (C g) (c.1 g) (c.2.1 g)
          (c.2.2 g) j)).symm
  · refine Fin.addCases ?_ ?_ i
    · intro j
      refine (giantSignedEdgeTarget_survivor d m (giantSignedPatternFreeLabels C a) c g j).trans ?_
      exact (congrArg R (giantSignedEdgeLiveOrigin_survivor (C g) (c.1 g) (c.2.1 g)
        (c.2.2 g) j)).symm
    · intro j
      have he := giantSignedEdgeTarget_store d m (giantSignedPatternFreeLabels C a) c g j
      have hs : giantSignedParticleAt d
          (giantSignedPatternFreeLabels C a g ((c.1 g).orderEmbOfFin rfl j)) =
          R (.inl (.inl (giantSignedFreeSlotEmbedding (C g) ell ((c.1 g).orderEmbOfFin rfl j)))) := by
        change _ = giantSignedParticleTranslate d (giantSignedParticleAt 0 _)
        rw [giantSignedParticleTranslate_at, zero_add]
        rfl
      exact he.trans (hs.trans (congrArg R (giantSignedEdgeLiveOrigin_stored (C g) (c.1 g) (c.2.1 g)
        (c.2.2 g) j)).symm)

end
end ArtinMatthews

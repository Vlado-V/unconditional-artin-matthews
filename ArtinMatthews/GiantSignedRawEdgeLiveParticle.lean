module

public import ArtinMatthews.GiantSignedRawEdgeLiveOrigin
public import ArtinMatthews.GiantSignedLiveParticle
public import ArtinMatthews.GiantSignedEdgeLiveParticle
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

/-! The original dilation translates every old live particle. A copied
active label divides the dilation by its literal copied factor. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ} {C : B → Finset (Fin k)}
    (κ : ℤ) (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2)

theorem giantSignedRawEdge_copy_shift_zero (g : B) (i : Fin k) (hi : i ∉ C g) :
    ((κ * (giantSignedRawEdgeProduct s r : ℤ) : ℤ) :
      ZMod (giantSignedRawEdgeBigSource s r g (Fin.castAdd ell i)).val) = 0 := by
  let a := giantSignedRawEdgeBigSource s r
  let p := (a g (Fin.castAdd ell i)).val
  have h1 : p ∣ ∏ l ∈ Finset.univ \ C g, (a g (Fin.castAdd ell l)).val :=
    Finset.dvd_prod_of_mem (fun l => (a g (Fin.castAdd ell l)).val)
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩)
  have h2 : p ∣ giantTwoSidedPatternCopiedProduct C a := h1.trans
    (Finset.dvd_prod_of_mem (fun j => ∏ l ∈ Finset.univ \ C j, (a j (Fin.castAdd ell l)).val)
      (Finset.mem_univ g))
  have hD : p ∣ giantSignedRawEdgeProduct s r :=
    dvd_mul_of_dvd_right (dvd_mul_of_dvd_left h2 _) _
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr
    (dvd_mul_of_dvd_right (Int.ofNat_dvd.mpr hD) κ)

theorem giantSignedRawEdgeLiveOrigin_particle (hc : GiantSignedRawEdgeCondition κ s r)
    (hh : GiantSignedEdgeHits (κ * (giantSignedRawEdgeProduct s r : ℤ)) s.2.2
      (giantSignedPatternFreeLabels C r.bigTarget) r.choice) (g : B)
    (z : GiantSignedLiveSlots (k+ell) ((giantSignedRawEdgeTarget κ s r).2.2.1 g)) :
    giantSignedLiveParticle ((giantSignedRawEdgeTarget κ s r).2.1 g)
        (giantSignedMemoryGroupEquiv PB (giantSignedRawEdgeTarget κ s r).2.2 g) z =
      Sum.elim (fun i => giantSignedParticleTranslate (κ * (giantSignedRawEdgeProduct s r : ℤ))
          (giantSignedLiveParticle (s.2.1 g) (giantSignedMemoryGroupEquiv PB s.2.2 g) i))
        (fun i : {i : Fin (ell+(C g).card) // i ∉ r.choice.2.1 g} =>
          giantSignedParticleAt 0 (giantSignedPatternFreeLabels C r.bigTarget g i.val))
        (giantSignedRawEdgeLiveOrigin κ s r g z) := by
  let d := κ * (giantSignedRawEdgeProduct s r : ℤ)
  let u := Sum.map (r.targetBigPermutation g).symm id z
  let w := giantSignedEdgeLiveOrigin (C g) (r.choice.1 g) (r.choice.2.1 g) (r.choice.2.2 g) u
  have he := giantSignedEdgeLiveOrigin_particle C s.2.2 (giantSignedRawEdgeBigSource s r) r.bigTarget
    r.choice d hc.2.2.1 (giantSignedRawEdge_copy_shift_zero κ s r) hh g u
  have hl : giantSignedLiveParticle ((giantSignedRawEdgeTarget κ s r).2.1 g)
      (giantSignedMemoryGroupEquiv PB (giantSignedRawEdgeTarget κ s r).2.2 g) z =
      giantSignedLiveParticle (r.bigTarget g)
        (giantSignedMemoryGroupEquiv PB (giantSignedRawEdgeTarget κ s r).2.2 g) u := by
    cases z <;> rfl
  refine hl.trans (he.trans ?_)
  change Sum.elim (fun i => giantSignedParticleTranslate d
      (giantSignedLiveParticle ((giantSignedRawEdgeBigSource s r) g)
        (giantSignedMemoryGroupEquiv PB s.2.2 g) i)) _ w =
    Sum.elim (fun i => giantSignedParticleTranslate d
      (giantSignedLiveParticle (s.2.1 g) (giantSignedMemoryGroupEquiv PB s.2.2 g) i)) _
      (Sum.map (Sum.map (r.sourceBigPermutation g) id) id w)
  rcases w with (i | i) | i <;> rfl

end
end ArtinMatthews

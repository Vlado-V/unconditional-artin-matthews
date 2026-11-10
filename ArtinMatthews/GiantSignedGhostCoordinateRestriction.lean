module

public import ArtinMatthews.GiantSignedGhostMemoryProduct
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Restricting a coordinate word to the complement of one fixed memory. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {B : Type*} [Fintype B] [DecidableEq B] {P : B → Finset ℕ}

omit [Fintype B] in
theorem giantSignedMemorySplit_update_complement (g : B)
    (t : GiantSignedGroupMemory (P g))
    (y : (h : {h : B // h ≠ g}) → GiantSignedGroupMemory (P h))
    (h : {h : B // h ≠ g}) (s : GiantSignedGroupMemory (P h)) :
    (giantSignedMemorySplit P g).symm (t, Function.update y h s) =
      Function.update ((giantSignedMemorySplit P g).symm (t, y)) h.val s := by
  funext a
  by_cases ha : a = g
  · subst a
    simp [giantSignedMemorySplit, Equiv.piSplitAt, Ne.symm h.property]
  · by_cases hh : a = h.val
    · subst a
      simp [giantSignedMemorySplit, Equiv.piSplitAt, h.property]
    · have hsub : (⟨a, ha⟩ : {a : B // a ≠ g}) ≠ h := by
        intro he
        exact hh (congrArg Subtype.val he)
      simp [giantSignedMemorySplit, Equiv.piSplitAt, ha, hh, hsub]

omit [Fintype B] in
theorem giantSignedGhostCoordinateWord_restrict
    (ν : ∀ g, P g → ℝ) (A C D : B → ℂ) (g : B)
    (gs : List {h : B // h ≠ g}) (f : GiantSignedMemoryGroups P → ℂ)
    (t : GiantSignedGroupMemory (P g))
    (y : (h : {h : B // h ≠ g}) → GiantSignedGroupMemory (P h)) :
    giantSignedGhostCoordinateWord
        (fun h : {h : B // h ≠ g} => ν h) (fun h => A h) (fun h => C h) (fun h => D h)
        gs (fun z => f ((giantSignedMemorySplit P g).symm (t, z))) y =
      giantSignedGhostCoordinateWord ν A C D (gs.map Subtype.val) f
        ((giantSignedMemorySplit P g).symm (t, y)) := by
  induction gs generalizing y with
  | nil => rfl
  | cons h gs ih =>
    simp only [giantSignedGhostCoordinateWord, List.map_cons,
      giantSignedGhostCoordinateApply_update]
    have hs : ((giantSignedMemorySplit P g).symm (t, y)) h.val = y h := by
      simp [giantSignedMemorySplit, Equiv.piSplitAt, h.property]
    rw [hs]
    apply congrArg (fun F => giantSignedGhostGroupApply (ν h) (A h) (C h) (D h) F (y h))
    funext s
    rw [ih, giantSignedMemorySplit_update_complement]

theorem giantSignedGhostProduct_tail_exponential
    (f : GiantSignedMemoryGroups P → ℂ) (hf : GiantSignedGhostProductExponential f)
    (g : B) (t : GiantSignedGroupMemory (P g)) :
    GiantSignedGhostProductExponential
      (fun y : (h : {h : B // h ≠ g}) → GiantSignedGroupMemory (P h) =>
        f ((giantSignedMemorySplit P g).symm (t, y))) := by
  obtain ⟨Cf, u, hCf, hu, hf⟩ := hf
  refine ⟨Cf * u ^ t.1, u, mul_nonneg hCf (pow_nonneg hu.le _), hu, ?_⟩
  intro y
  have h := hf ((giantSignedMemorySplit P g).symm (t, y))
  rw [giantSignedMemoryTotalDegree_split] at h
  unfold giantSignedMemoryTotalDegree
  convert h using 1
  rw [pow_add]
  ring

end
end ArtinMatthews

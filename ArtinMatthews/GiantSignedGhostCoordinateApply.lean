module

public import ArtinMatthews.GiantSignedGhostMemoryCoordinates
public import ArtinMatthews.GiantSignedGhostSchur
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

/-! A coordinate ghost on the original product of all pending memories,
with exact product-measure disintegration. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

variable {B : Type*} [Fintype B] [DecidableEq B] {P : B → Finset ℕ}

def giantSignedMemoryTotalDegree (x : GiantSignedMemoryGroups P) : ℕ :=
  ∑ g, (x g).1

def GiantSignedGhostProductSymmetric (f : GiantSignedMemoryGroups P → ℂ) : Prop :=
  ∀ g y, GiantSignedGroupSymmetric
    (fun t => f ((giantSignedMemorySplit P g).symm (t, y)))

def GiantSignedGhostProductExponential (f : GiantSignedMemoryGroups P → ℂ) : Prop :=
  ∃ C u : ℝ, 0 ≤ C ∧ 0 < u ∧ ∀ x, ‖f x‖ ≤ C * u ^ giantSignedMemoryTotalDegree x

def giantSignedGhostCoordinateApply (ν : ∀ g, P g → ℝ) (A C D : B → ℂ)
    (g : B) (f : GiantSignedMemoryGroups P → ℂ) (x : GiantSignedMemoryGroups P) : ℂ :=
  let z := giantSignedMemorySplit P g x
  giantSignedGhostGroupApply (ν g) (A g) (C g) (D g)
    (fun t => f ((giantSignedMemorySplit P g).symm (t, z.2))) z.1

omit [Fintype B] in
theorem giantSignedMemorySplit_update (g : B) (x : GiantSignedMemoryGroups P)
    (t : GiantSignedGroupMemory (P g)) :
    (giantSignedMemorySplit P g).symm (t, (giantSignedMemorySplit P g x).2) =
      Function.update x g t := by
  funext h
  by_cases hh : h = g
  · subst h
    simp [giantSignedMemorySplit, Equiv.piSplitAt]
  · simp [giantSignedMemorySplit, Equiv.piSplitAt, hh]

omit [Fintype B] in
theorem giantSignedGhostCoordinateApply_update (ν : ∀ g, P g → ℝ) (A C D : B → ℂ)
    (g : B) (f : GiantSignedMemoryGroups P → ℂ) (x : GiantSignedMemoryGroups P) :
    giantSignedGhostCoordinateApply ν A C D g f x =
      giantSignedGhostGroupApply (ν g) (A g) (C g) (D g)
        (fun t => f (Function.update x g t)) (x g) := by
  simp only [giantSignedGhostCoordinateApply, giantSignedMemorySplit_update]
  rfl

omit [Fintype B] in
theorem giantSignedGhostCoordinateApply_split (ν : ∀ g, P g → ℝ) (A C D : B → ℂ)
    (g : B) (f : GiantSignedMemoryGroups P → ℂ)
    (t : GiantSignedGroupMemory (P g))
    (y : (h : {h : B // h ≠ g}) → GiantSignedGroupMemory (P h)) :
    giantSignedGhostCoordinateApply ν A C D g f ((giantSignedMemorySplit P g).symm (t, y)) =
      giantSignedGhostGroupApply (ν g) (A g) (C g) (D g)
        (fun s => f ((giantSignedMemorySplit P g).symm (s, y))) t := by
  simp only [giantSignedGhostCoordinateApply, Equiv.apply_symm_apply]

theorem giantSignedMemoryTotalDegree_split (g : B)
    (t : GiantSignedGroupMemory (P g))
    (y : (h : {h : B // h ≠ g}) → GiantSignedGroupMemory (P h)) :
    giantSignedMemoryTotalDegree ((giantSignedMemorySplit P g).symm (t, y)) =
      t.1 + ∑ h : {h : B // h ≠ g}, (y h).1 := by
  unfold giantSignedMemoryTotalDegree
  rw [giantSignedSum_split g]
  congr 1
  · simp [giantSignedMemorySplit, Equiv.piSplitAt]
  · apply Finset.sum_congr rfl
    intro h _
    simp [giantSignedMemorySplit, Equiv.piSplitAt, h.property]

theorem giantSignedGhostProduct_slice_bound
    (f : GiantSignedMemoryGroups P → ℂ) (C u : ℝ)
    (hf : ∀ x, ‖f x‖ ≤ C * u ^ giantSignedMemoryTotalDegree x)
    (g : B) (y : (h : {h : B // h ≠ g}) → GiantSignedGroupMemory (P h))
    (t : GiantSignedGroupMemory (P g)) :
    ‖f ((giantSignedMemorySplit P g).symm (t, y))‖ ≤
      (C * u ^ (∑ h : {h : B // h ≠ g}, (y h).1)) * u ^ t.1 := by
  have h := hf ((giantSignedMemorySplit P g).symm (t, y))
  rw [giantSignedMemoryTotalDegree_split, pow_add] at h
  convert h using 1
  ring

variable [∀ (g : B) (p : P g), NeZero p.val]

theorem giantSignedGhostCoordinateApply_energy
    (ν : ∀ g, P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (A C D : B → ℂ) (g : B) (v : ℝ) (hv : 0 < v)
    (hrow : ‖A g‖ + ‖D g‖ / v ≤ 1) (hcol : ‖A g‖ + ‖C g‖ / v ≤ 1)
    (f : GiantSignedMemoryGroups P → ℂ) (hfs : GiantSignedGhostProductSymmetric f)
    (Cf u : ℝ) (hCf : 0 ≤ Cf) (hu : 0 < u)
    (hf : ∀ x, ‖f x‖ ≤ Cf * u ^ giantSignedMemoryTotalDegree x) :
    giantSignedGhostProductEnergy ν (giantSignedGhostCoordinateApply ν A C D g f) ≤
      ENNReal.ofReal (Real.exp ((‖C g‖ + ‖D g‖) * (∑ p : P g, ν g p) * v)) *
        giantSignedGhostProductEnergy ν f := by
  rw [giantSignedGhostProductEnergy_split ν hν g,
    giantSignedGhostProductEnergy_split ν hν g]
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro y
  simp_rw [giantSignedGhostCoordinateApply_split]
  let c := Cf * u ^ (∑ h : {h : B // h ≠ g}, (y h).1)
  have hc : 0 ≤ c := mul_nonneg hCf (pow_nonneg hu.le _)
  have he := giantSignedGhostGroupApply_energy (ν g) (hν g) (A g) (C g) (D g) v hv hrow hcol
    (fun t => f ((giantSignedMemorySplit P g).symm (t, y))) (hfs g y)
    c u hc hu (giantSignedGhostProduct_slice_bound f Cf u hf g y)
  calc
    _ ≤ ENNReal.ofReal (∏ h : {h : B // h ≠ g}, giantSignedGroupMemoryMass (ν h) (y h)) *
        (ENNReal.ofReal (Real.exp ((‖C g‖ + ‖D g‖) * (∑ p : P g, ν g p) * v)) *
          giantSignedGroupEnergy (ν g) (fun t => f ((giantSignedMemorySplit P g).symm (t, y)))) :=
      mul_le_mul' le_rfl he
    _ = _ := by ring

end
end ArtinMatthews

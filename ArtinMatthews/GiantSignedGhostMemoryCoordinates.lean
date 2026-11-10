module

public import ArtinMatthews.GiantSignedFockMoments
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

/-! The full pending state is exactly the finite product of its genuine
group memories. Factorial masses are unchanged by this coordinate map. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

abbrev GiantSignedMemoryGroups {B : Type*} (P : B → Finset ℕ) :=
  (g : B) → GiantSignedGroupMemory (P g)

def giantSignedMemoryGroupEquiv {B : Type*} (P : B → Finset ℕ) :
    GiantSignedMemory P ≃ GiantSignedMemoryGroups P where
  toFun m g := ⟨m.1 g, m.2 g⟩
  invFun x := ⟨fun g => (x g).1, fun g => (x g).2⟩
  left_inv m := by cases m; rfl
  right_inv x := by funext g; exact Sigma.eta (x g)

def giantSignedMemoryProductMass {B : Type*} [Fintype B] {P : B → Finset ℕ}
    (ν : ∀ g, P g → ℝ) (x : GiantSignedMemoryGroups P) : ℝ :=
  ∏ g, giantSignedGroupMemoryMass (ν g) (x g)

theorem giantSignedMemoryGroupEquiv_mass {B : Type*} [Fintype B] {P : B → Finset ℕ}
    (ν : ∀ g, P g → ℝ) (m : GiantSignedMemory P) :
    giantSignedMemoryProductMass ν (giantSignedMemoryGroupEquiv P m) =
      giantSignedMemoryMass ν m := rfl

theorem giantSignedMemoryProductMass_nonneg {B : Type*} [Fintype B] {P : B → Finset ℕ}
    (ν : ∀ g, P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (x : GiantSignedMemoryGroups P) :
    0 ≤ giantSignedMemoryProductMass ν x :=
  Finset.prod_nonneg fun g _ => giantSignedGroupMemoryMass_nonneg (ν g) (hν g) (x g)

def giantSignedGhostMemoryEnergy {B : Type*} [Fintype B] {P : B → Finset ℕ}
    (ν : ∀ g, P g → ℝ) (f : GiantSignedMemory P → ℂ) : ℝ≥0∞ :=
  ∑' m, ENNReal.ofReal (giantSignedMemoryMass ν m * ‖f m‖ ^ 2)

def giantSignedGhostProductEnergy {B : Type*} [Fintype B] {P : B → Finset ℕ}
    (ν : ∀ g, P g → ℝ) (f : GiantSignedMemoryGroups P → ℂ) : ℝ≥0∞ :=
  ∑' x, ENNReal.ofReal (giantSignedMemoryProductMass ν x * ‖f x‖ ^ 2)

theorem giantSignedGhostMemoryEnergy_groups {B : Type*} [Fintype B] {P : B → Finset ℕ}
    (ν : ∀ g, P g → ℝ) (f : GiantSignedMemory P → ℂ) :
    giantSignedGhostMemoryEnergy ν f =
      giantSignedGhostProductEnergy ν (fun x => f ((giantSignedMemoryGroupEquiv P).symm x)) := by
  unfold giantSignedGhostMemoryEnergy giantSignedGhostProductEnergy
  symm
  exact (giantSignedMemoryGroupEquiv P).symm.tsum_eq
    (fun m : GiantSignedMemory P => ENNReal.ofReal (giantSignedMemoryMass ν m * ‖f m‖ ^ 2))

@[to_additive giantSignedSum_split]
theorem giantSignedProduct_split {B M : Type*} [Fintype B] [DecidableEq B] [CommMonoid M]
    (g : B) (f : B → M) :
    (∏ h, f h) = f g * ∏ h : {h : B // h ≠ g}, f h := by
  classical
  have hs : Subsingleton {h : B // h = g} := ⟨fun a b => Subtype.ext (a.property.trans b.property.symm)⟩
  let _ := hs
  let _ : Fintype {h : B // h = g} := Subtype.fintype (fun h => h = g)
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun h => h = g) f]
  congr 1
  exact Fintype.prod_subsingleton (fun h : {h : B // h = g} => f h) ⟨g, rfl⟩

def giantSignedMemorySplit {B : Type*} [DecidableEq B] (P : B → Finset ℕ) (g : B) :
    GiantSignedMemoryGroups P ≃
      GiantSignedGroupMemory (P g) × ((h : {h : B // h ≠ g}) → GiantSignedGroupMemory (P h)) :=
  Equiv.piSplitAt g (fun h => GiantSignedGroupMemory (P h))

theorem giantSignedMemorySplit_mass {B : Type*} [Fintype B] [DecidableEq B]
    {P : B → Finset ℕ} (ν : ∀ g, P g → ℝ) (g : B)
    (t : GiantSignedGroupMemory (P g))
    (y : (h : {h : B // h ≠ g}) → GiantSignedGroupMemory (P h)) :
    giantSignedMemoryProductMass ν ((giantSignedMemorySplit P g).symm (t, y)) =
      giantSignedGroupMemoryMass (ν g) t *
        ∏ h : {h : B // h ≠ g}, giantSignedGroupMemoryMass (ν h) (y h) := by
  unfold giantSignedMemoryProductMass
  rw [giantSignedProduct_split g (fun h =>
    giantSignedGroupMemoryMass (ν h) ((giantSignedMemorySplit P g).symm (t, y) h))]
  congr 1
  · simp [giantSignedMemorySplit, Equiv.piSplitAt]
  · apply Finset.prod_congr rfl
    intro h _
    simp [giantSignedMemorySplit, Equiv.piSplitAt, h.property]

theorem giantSignedGhostProductEnergy_split {B : Type*} [Fintype B] [DecidableEq B]
    {P : B → Finset ℕ} (ν : ∀ g, P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (g : B) (f : GiantSignedMemoryGroups P → ℂ) :
    giantSignedGhostProductEnergy ν f =
      ∑' y : (h : {h : B // h ≠ g}) → GiantSignedGroupMemory (P h),
        ENNReal.ofReal (∏ h : {h : B // h ≠ g}, giantSignedGroupMemoryMass (ν h) (y h)) *
          giantSignedGroupEnergy (ν g) (fun t => f ((giantSignedMemorySplit P g).symm (t, y))) := by
  unfold giantSignedGhostProductEnergy
  calc
    _ = ∑' z, ENNReal.ofReal (giantSignedMemoryProductMass ν
        ((giantSignedMemorySplit P g).symm z) * ‖f ((giantSignedMemorySplit P g).symm z)‖ ^ 2) :=
      ((giantSignedMemorySplit P g).symm.tsum_eq _).symm
    _ = ∑' y, ∑' t, ENNReal.ofReal (giantSignedMemoryProductMass ν
        ((giantSignedMemorySplit P g).symm (t, y)) * ‖f ((giantSignedMemorySplit P g).symm (t, y))‖ ^ 2) := by
      rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
    _ = _ := by
      apply tsum_congr
      intro y
      unfold giantSignedGroupEnergy
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro t
      rw [giantSignedMemorySplit_mass]
      have hp : 0 ≤ ∏ h : {h : B // h ≠ g}, giantSignedGroupMemoryMass (ν h) (y h) :=
        Finset.prod_nonneg fun h _ => giantSignedGroupMemoryMass_nonneg (ν h) (hν h) (y h)
      rw [mul_comm (giantSignedGroupMemoryMass (ν g) t)
        (∏ h : {h : B // h ≠ g}, giantSignedGroupMemoryMass (ν h) (y h)),
        mul_assoc, ENNReal.ofReal_mul hp]

end
end ArtinMatthews

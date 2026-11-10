module

public import ArtinMatthews.GiantSignedGhostMemoryProduct
public import ArtinMatthews.GiantSignedGhostSimultaneous
public import ArtinMatthews.GiantSignedGhostMemoryUniform
public import ArtinMatthews.GiantSignedGhostSimultaneousIteration
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

/-! Energy and domain closure for the original simultaneous ghost row. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

variable {B : Type*} [Fintype B] [DecidableEq B] {P : B → Finset ℕ}

theorem giantSignedGhostSimultaneous_eq_memoryApply_function
    (ν : ∀ g, P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (A C D : B → ℂ)
    (f : GiantSignedMemory P → ℂ) (Cf u : ℝ) (hCf : 0 ≤ Cf) (hu : 0 < u)
    (hf : ∀ m, ‖f m‖ ≤ Cf * u ^ (∑ g, m.1 g)) :
    giantSignedGhostSimultaneousApply ν A C D f = giantSignedGhostMemoryApply ν A C D f := by
  funext m
  exact giantSignedGhostSimultaneous_eq_memoryApply ν hν A C D f Cf u hCf hu hf m

theorem giantSignedGhostSimultaneous_symmetric
    (ν : ∀ g, P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (A C D : B → ℂ)
    (f : GiantSignedMemory P → ℂ) (hfs : GiantSignedMemorySymmetric f)
    (Cf u : ℝ) (hCf : 0 ≤ Cf) (hu : 0 < u)
    (hf : ∀ m, ‖f m‖ ≤ Cf * u ^ (∑ g, m.1 g)) :
    GiantSignedMemorySymmetric (giantSignedGhostSimultaneousApply ν A C D f) := by
  rw [giantSignedGhostSimultaneous_eq_memoryApply_function ν hν A C D f Cf u hCf hu hf]
  exact giantSignedGhostMemoryApply_symmetric ν A C D f hfs

theorem giantSignedGhostSimultaneous_exponential
    (ν : ∀ g, P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (A C D : B → ℂ)
    (f : GiantSignedMemory P → ℂ) (Cf u : ℝ) (hCf : 0 ≤ Cf) (hu : 0 < u)
    (hf : ∀ m, ‖f m‖ ≤ Cf * u ^ (∑ g, m.1 g)) :
    ∃ C' u' : ℝ, 0 ≤ C' ∧ 0 < u' ∧
      ∀ m, ‖giantSignedGhostSimultaneousApply ν A C D f m‖ ≤ C' * u' ^ (∑ g, m.1 g) := by
  let F := fun x => f ((giantSignedMemoryGroupEquiv P).symm x)
  have hF : GiantSignedGhostProductExponential F :=
    ⟨Cf, u, hCf, hu, fun x => hf ((giantSignedMemoryGroupEquiv P).symm x)⟩
  obtain ⟨C', u', hC', hu', hG⟩ :=
    giantSignedGhostCoordinateWord_exponential ν hν A C D Finset.univ.toList F hF
  refine ⟨C', u', hC', hu', ?_⟩
  intro m
  rw [giantSignedGhostSimultaneous_eq_memoryApply ν hν A C D f Cf u hCf hu hf m]
  exact hG (giantSignedMemoryGroupEquiv P m)

theorem giantSignedGhostSimultaneous_empty [IsEmpty B]
    (ν : ∀ g, P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (A C D : B → ℂ)
    (f : GiantSignedMemory P → ℂ) (Cf u : ℝ) (hCf : 0 ≤ Cf) (hu : 0 < u)
    (hf : ∀ m, ‖f m‖ ≤ Cf * u ^ (∑ g, m.1 g)) :
    giantSignedGhostSimultaneousApply ν A C D f = f := by
  rw [giantSignedGhostSimultaneous_eq_memoryApply_function ν hν A C D f Cf u hCf hu hf]
  exact giantSignedGhostMemoryApply_empty ν A C D f

def giantSignedGhostSimultaneousGroup (ν : ∀ g, P g → ℝ) (V : B → ℝ) (q ρ : ℝ)
    (f : GiantSignedMemory P → ℂ) : GiantSignedMemory P → ℂ :=
  giantSignedGhostSimultaneousApply ν (fun _ => ((q / ρ ^ 2 : ℝ) : ℂ))
    (fun g => ((-(1-q) * V g / ρ : ℝ) : ℂ)) (fun _ => ((-(1-q) / ρ : ℝ) : ℂ)) f

variable [∀ (g : B) (p : P g), NeZero p.val]

theorem giantSignedGhostSimultaneous_energy
    (ν : ∀ g, P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (A C D : B → ℂ)
    (v : ℝ) (hv : 0 < v)
    (hrow : ∀ g, ‖A g‖ + ‖D g‖ / v ≤ 1) (hcol : ∀ g, ‖A g‖ + ‖C g‖ / v ≤ 1)
    (f : GiantSignedMemory P → ℂ) (hfs : GiantSignedMemorySymmetric f)
    (Cf u : ℝ) (hCf : 0 ≤ Cf) (hu : 0 < u)
    (hf : ∀ m, ‖f m‖ ≤ Cf * u ^ (∑ g, m.1 g)) :
    giantSignedGhostMemoryEnergy ν (giantSignedGhostSimultaneousApply ν A C D f) ≤
      (∏ g, ENNReal.ofReal (Real.exp ((‖C g‖ + ‖D g‖) * (∑ p : P g, ν g p) * v))) *
        giantSignedGhostMemoryEnergy ν f := by
  rw [giantSignedGhostSimultaneous_eq_memoryApply_function ν hν A C D f Cf u hCf hu hf]
  exact giantSignedGhostMemoryApply_energy ν hν A C D v hv hrow hcol f hfs Cf u hCf hu hf

theorem giantSignedGhostSimultaneousGroup_energy
    (ν : ∀ g, P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ) (q ρ v : ℝ) (hv : 0 < v)
    (hrow : |q / ρ ^ 2| + |-(1-q) / ρ| / v ≤ 1)
    (hcol : ∀ g, |q / ρ ^ 2| + |-(1-q) * V g / ρ| / v ≤ 1)
    (f : GiantSignedMemory P → ℂ) (hfs : GiantSignedMemorySymmetric f)
    (Cf u : ℝ) (hCf : 0 ≤ Cf) (hu : 0 < u)
    (hf : ∀ m, ‖f m‖ ≤ Cf * u ^ (∑ g, m.1 g)) :
    giantSignedGhostMemoryEnergy ν (giantSignedGhostSimultaneousGroup ν V q ρ f) ≤
      (∏ g, ENNReal.ofReal (Real.exp ((|-(1-q) * V g / ρ| + |-(1-q) / ρ|) *
        (∑ p : P g, ν g p) * v))) * giantSignedGhostMemoryEnergy ν f := by
  have he := giantSignedGhostSimultaneous_energy ν hν
    (fun _ => ((q / ρ ^ 2 : ℝ) : ℂ)) (fun g => ((-(1-q) * V g / ρ : ℝ) : ℂ))
    (fun _ => ((-(1-q) / ρ : ℝ) : ℂ)) v hv
    (fun _ => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hrow)
    (fun g => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hcol g) f hfs Cf u hCf hu hf
  simpa only [giantSignedGhostSimultaneousGroup, Complex.norm_real, Real.norm_eq_abs] using he

omit [Fintype B] [DecidableEq B] [∀ (g : B) (p : P g), NeZero p.val] in
theorem giantSignedGhostSimultaneous_uniform_energy
    (aMax cMax dMax massMax : ℝ) (ha : aMax < 1) (hc : 0 ≤ cMax) (hd : 0 ≤ dMax) :
    ∃ v : ℝ, 1 < v ∧ ∀ (J : Type*) [Fintype J] [DecidableEq J]
      (Q : J → Finset ℕ) [∀ (g : J) (p : Q g), NeZero p.val]
      (ν : ∀ g, Q g → ℝ), (∀ g p, 0 ≤ ν g p) → (∀ g, (∑ p : Q g, ν g p) ≤ massMax) →
      ∀ A C D z : J → ℂ,
        (∀ g, ‖A g‖ ≤ aMax) → (∀ g, ‖C g‖ ≤ cMax) →
        (∀ g, ‖D g‖ ≤ dMax) → (∀ g, ‖z g‖ ≤ 2) →
      ∀ f : GiantSignedMemory Q → ℂ, GiantSignedMemorySymmetric f →
      ∀ Cf u : ℝ, 0 ≤ Cf → 0 < u → (∀ m, ‖f m‖ ≤ Cf * u ^ (∑ g, m.1 g)) →
        giantSignedGhostMemoryEnergy ν (giantSignedGhostSimultaneousApply ν A (fun g => z g * C g) D f) ≤
          ENNReal.ofReal (Real.exp ((2 * cMax + dMax) * massMax * v)) ^ Fintype.card J *
            giantSignedGhostMemoryEnergy ν f := by
  obtain ⟨v, hv, hvbound⟩ := giantSignedGhostMemory_uniform_energy aMax cMax dMax massMax ha hc hd
  refine ⟨v, hv, ?_⟩
  intro J instJ instDec Q instQ ν hν hmass A C D z hA hC hD hz f hfs Cf u hCf hu hf
  rw [giantSignedGhostSimultaneous_eq_memoryApply_function ν hν A (fun g => z g * C g) D
    f Cf u hCf hu hf]
  exact hvbound J Q ν hν hmass A C D z hA hC hD hz f hfs Cf u hCf hu hf

end
end ArtinMatthews

module

public import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.PhaseAction
public import OAI.RepresentationTheory.Theta.CosetTests
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.BoundedScalar
public import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.HeisenbergLattice
public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.CosetPhase
public import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteHeisenberg


set_option backward.privateInPublic true
@[expose] public section

/-! A finite Weil operator acts on translated lattice tests by one common
scalar and the actual symplectic transport of their centers. The scalar is
derived from Heisenberg intertwining and lattice support, not assumed. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators Classical
open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData
open OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction
open OAI.RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction
open OAI.RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.PhaseAction.TestTransport
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.HeisenbergLattice.TestTransport
open OAI.RepresentationTheory.Hecke.RadialDilation.FiniteHeisenberg.Realization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Explicit inverse-matrix lattice conditions fixing the base lattice line.
No condition fixing individual residue classes is included. -/
def finiteBaseLatticeControl (r : ℚ) (hr : r ≠ 0) (g : Sp ι AQf) : Prop :=
  (∀ p ∈ finiteLattice r⁻¹ (inv_ne_zero hr),
    finiteMomentum g⁻¹ p 0 ∈ finiteLattice r⁻¹ (inv_ne_zero hr) ∧
    finitePosition g⁻¹ p 0 ∈ finiteLattice r hr ∧
    finiteScale (1 / 2) (finitePosition g⁻¹ p 0) ∈ finiteLattice r hr) ∧
  (∀ q ∈ finiteLattice r hr,
    finiteMomentum g⁻¹ 0 q ∈ finiteLattice r⁻¹ (inv_ne_zero hr) ∧
    finitePosition g⁻¹ 0 q ∈ finiteLattice r hr ∧
    finiteScale (1 / 2) (finiteMomentum g⁻¹ 0 q) ∈ finiteLattice r⁻¹ (inv_ne_zero hr))

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
    (D : WeilData ι MpR MpF MpA)

/-- The actual operator scalar on the base lattice follows from the proved
joint Heisenberg eigenspace theorem. -/
theorem finiteWeil_baseLattice_scalar (r : ℚ) (hr : r ≠ 0) (m : MpF)
    (hm : finiteBaseLatticeControl r hr (D.finite.project m)) :
    D.finite.action m (latticeTestFunction r hr) =
      (D.finite.action m (latticeTestFunction r hr)).val 0 •
        latticeTestFunction r hr := by
  let f := latticeTestFunction (ι := ι) r hr
  apply OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.BoundedScalar.TestTransport.finite_lattice_joint_eigenvector D
  · intro p hp x
    obtain ⟨h1, h2, h3⟩ := hm.1 p hp
    have ht := finite_intertwines_inverse_input D m p 0 f f
      (fun y => (finite_heisenberg_lattice_fixed_half_translation D r hr _ _ h1 h2 h3 y).symm) x
    simpa only [finite_heisenberg_modulation] using ht
  · intro q hq x
    obtain ⟨h1, h2, h3⟩ := hm.2 q hq
    have ht := finite_intertwines_inverse_input D m 0 q f f
      (fun y => (finite_heisenberg_lattice_fixed_half_modulation D r hr _ _ h1 h2 h3 y).symm) x
    simpa only [finite_heisenberg_translation] using ht.symm

/-- A translated lattice test is transported to its actual target coset.
All hypotheses are concrete matrix/lattice/phase conditions; no eigenline
or modular transformation is an input. -/
theorem finiteWeil_latticeCoset_action (r : ℚ) (hr : r ≠ 0) (m : MpF)
    (hm : finiteBaseLatticeControl r hr (D.finite.project m))
    (a b : ι → AQf)
    (hp : finiteMomentum (D.finite.project m) 0 a ∈
      finiteLattice r⁻¹ (inv_ne_zero hr))
    (hq : finitePosition (D.finite.project m) 0 a - b ∈ finiteLattice r hr)
    (hphase : (∑ i, finiteMomentum (D.finite.project m) 0 a i *
      (finiteScale (1 / 2) (finitePosition (D.finite.project m) 0 a)) i) ∈ integralAdele) :
    D.finite.action m (latticeCosetTest r hr a) =
      (D.finite.action m (latticeTestFunction r hr)).val 0 • latticeCosetTest r hr b := by
  let f := latticeTestFunction (ι := ι) r hr
  have hf := finiteWeil_baseLattice_scalar D r hr m hm
  apply Subtype.ext
  funext x
  have ht := D.finite.intertwines m 0 a f (latticeCosetTest r hr a)
    (fun y => by rw [finite_heisenberg_translation]; rfl) x
  change (D.finite.action m (latticeCosetTest r hr a)).val x =
    heisenberg D.finiteCharacter (finiteMomentum (D.finite.project m) 0 a)
      (finitePosition (D.finite.project m) 0 a) (D.finite.action m f).val x at ht
  rw [ht]
  nth_rw 1 [hf]
  change _ * ((D.finite.action m f).val 0 * f.val _) =
    (D.finite.action m f).val 0 * (latticeCosetTest r hr b).val x
  rw [← mul_left_comm]
  exact congrArg (fun z : ℂ => (D.finite.action m f).val 0 * z)
    (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.CosetPhase.CM.translate
      D r hr _ _ b hp hq hphase x)

end ArtinMatthews

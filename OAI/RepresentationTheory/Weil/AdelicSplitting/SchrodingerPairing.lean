module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.AdelicSplitting.Normalization
public import OAI.RepresentationTheory.Weil.UnitarySplitting.CayleyCompositionPhase
public import OAI.RepresentationTheory.Weil.UnitarySplitting.Oscillator
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import OAI.RepresentationTheory.Weil.UnitarySplitting.Heisenberg


set_option backward.privateInPublic true
@[expose] public section

/-! # Schrodinger Pairing -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.SchrodingerPairing.Construction

noncomputable section

/-! The alternating pairing of the actual Schrödinger Heisenberg law.
It is the negative of the historical AdelicSplitting coordinate pairing. The corrected
Cayley phase below is fixed by this independently checked cocycle law. -/

open scoped Classical

variable (k : Type) [NormedField k] (N : ℕ)

def schrodingerPairing : LinearMap.BilinForm k (Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :=
  (Matrix.J (Fin N) k).toBilin'

theorem schrodingerPairing_eq_standard (x y : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
    schrodingerPairing k N x y = UnitarySplitting.Oscillator.Construction.standardSymplecticPairing N x y := by
  simp [schrodingerPairing, Matrix.toBilin'_apply, Matrix.J,
    Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply,
    UnitarySplitting.Oscillator.Construction.standardSymplecticPairing, Finset.sum_sub_distrib]
  ring

theorem schrodingerPairing_eq_neg_phasePair
    [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k] (x y : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
    schrodingerPairing k N x y = -Normalization.Construction.phasePair k N x y := by
  rw [Normalization.Construction.phasePair, neg_neg]
  rfl

theorem schrodingerPairing_alternating : (schrodingerPairing k N).IsAlt := by
  intro x
  rw [schrodingerPairing_eq_standard]
  unfold UnitarySplitting.Oscillator.Construction.standardSymplecticPairing
  apply Finset.sum_eq_zero
  intro i _
  ring

theorem schrodingerPairing_preserved (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) (x y : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
    schrodingerPairing k N (Local.FunctionsMetaplectic.Construction.symplecticAction g x) (Local.FunctionsMetaplectic.Construction.symplecticAction g y) =
      schrodingerPairing k N x y := by
  have h := congrArg Matrix.toBilin' ((SymplecticGroup.mem_iff'.mp g.property))
  rw [← Matrix.toBilin'_comp] at h
  exact congrArg (fun B : LinearMap.BilinForm k (Local.FunctionsMetaplectic.Construction.PhaseSpace k N) => B x y) h

theorem schrodingerPairing_frame (d : k) (n m : ℕ)
    (H : Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic k d))
    (K : Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic k d))
    (c : TensorSpace.Construction.SymplecticFrame d n m H K) (x y : TensorSpace.Construction.TensorPosition d n m) :
    schrodingerPairing k (n * m) (c.coordinates x) (c.coordinates y) =
      -TensorSpace.Construction.tracePairing d n m H K x y := by
  have h := congrArg Neg.neg (c.preserves x y)
  simpa only [schrodingerPairing, TensorSpace.Construction.coordinatePairing, neg_neg] using h

variable [CharZero k]

theorem heisenberg_composition_schrodingerPairing (ψ : AddChar k ℂ)
    (v w : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) (f : Local.FunctionsMetaplectic.Construction.Position k N → ℂ) :
    Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v (Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ w f) =
      ψ (schrodingerPairing k N v w / 2) • Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (v + w) f := by
  rw [schrodingerPairing_eq_standard]
  exact UnitarySplitting.Heisenberg.Construction.heisenbergFunction_composition ψ v w f

def symplecticPhaseEquiv (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) : Local.FunctionsMetaplectic.Construction.PhaseSpace k N ≃ₗ[k] Local.FunctionsMetaplectic.Construction.PhaseSpace k N where
  toFun := Local.FunctionsMetaplectic.Construction.symplecticAction g
  invFun := Local.FunctionsMetaplectic.Construction.symplecticAction g⁻¹
  left_inv := Local.FunctionsMetaplectic.Construction.symplecticAction_cancel_inv g
  right_inv := Local.FunctionsMetaplectic.Construction.symplecticAction_inv_cancel g
  map_add' := Matrix.mulVec_add g.val
  map_smul' := Matrix.mulVec_smul g.val

def openCellDifference (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) (hg : (g.val - 1).det ≠ 0) :
    Local.FunctionsMetaplectic.Construction.PhaseSpace k N ≃ₗ[k] Local.FunctionsMetaplectic.Construction.PhaseSpace k N :=
  Matrix.toLinearEquiv (Pi.basisFun k (Fin N ⊕ Fin N)) (g.val - 1) (isUnit_iff_ne_zero.mpr hg)

omit [CharZero k] in
theorem openCellDifference_apply (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) (hg : (g.val - 1).det ≠ 0)
    (x : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) : openCellDifference k N g hg x = Local.FunctionsMetaplectic.Construction.symplecticAction g x - x := by
  change (g.val - 1).mulVec x = g.val.mulVec x - x
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]

def schrodingerCayleyPhase (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) (hg : (g.val - 1).det ≠ 0)
    (v : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) : k :=
  UnitarySplitting.CayleyCompositionPhase.Construction.cayleyWeylPhase (schrodingerPairing k N)
    (openCellDifference k N g hg) v

theorem schrodingerCayleyPhase_translation (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) (hg : (g.val - 1).det ≠ 0)
    (u w : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
    schrodingerCayleyPhase k N g hg (u - w) + schrodingerPairing k N u w / 2 =
      schrodingerCayleyPhase k N g hg (u - Local.FunctionsMetaplectic.Construction.symplecticAction g w) +
        schrodingerPairing k N (Local.FunctionsMetaplectic.Construction.symplecticAction g w) u / 2 :=
  UnitarySplitting.CayleyCompositionPhase.Construction.cayleyWeylPhase_translation
    (schrodingerPairing k N) (schrodingerPairing_alternating k N)
    (symplecticPhaseEquiv k N g) (openCellDifference k N g hg)
    (schrodingerPairing_preserved k N g) (openCellDifference_apply k N g hg) u w

theorem schrodingerCayleyPhase_original_variable (g : Local.FunctionsMetaplectic.Construction.Symplectic k N)
    (hg : (g.val - 1).det ≠ 0) (w : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
    schrodingerCayleyPhase k N g hg (w - Local.FunctionsMetaplectic.Construction.symplecticAction g w) =
      schrodingerPairing k N w (Local.FunctionsMetaplectic.Construction.symplecticAction g w) / 2 := by
  have hw : w - Local.FunctionsMetaplectic.Construction.symplecticAction g w = openCellDifference k N g hg (-w) := by
    rw [openCellDifference_apply]
    change w - g.val.mulVec w = g.val.mulVec (-w) - -w
    rw [Matrix.mulVec_neg]
    abel
  rw [hw]
  change schrodingerPairing k N ((openCellDifference k N g hg).symm
    (openCellDifference k N g hg (-w))) (openCellDifference k N g hg (-w)) / 2 = _
  rw [LinearEquiv.symm_apply_apply, ← hw, map_neg, LinearMap.neg_apply, map_sub,
    schrodingerPairing_alternating k N w]
  ring

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.SchrodingerPairing.Construction

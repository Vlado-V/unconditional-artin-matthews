module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! # Position Basis -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.PositionBasis.LocalAnalysis

noncomputable section

/-! Explicit finite position coordinates for a basis, with one index
for the position and one for the scalar-space basis. -/

open scoped Classical

variable {R E ι : Type*} [CommRing R] [AddCommGroup E] [Module R E] [Fintype ι]

def positionBasisCoordinates (N : ℕ) (b : Module.Basis ι R E) :
    (Fin N → E) ≃ₗ[R] ((Fin N × ι) → R) where
  toFun x p := b.equivFun (x p.1) p.2
  invFun y i := b.equivFun.symm (fun j => y (i, j))
  left_inv x := funext (fun i => b.equivFun.symm_apply_apply (x i))
  right_inv y := funext (fun p => congrFun (b.equivFun.apply_symm_apply (fun j => y (p.1, j))) p.2)
  map_add' x y := funext (fun p => congrFun (b.equivFun.map_add (x p.1) (y p.1)) p.2)
  map_smul' c x := funext (fun p => congrFun (b.equivFun.map_smul c (x p.1)) p.2)

def positionBasis (N : ℕ) (b : Module.Basis ι R E) : Module.Basis (Fin N × ι) R (Fin N → E) :=
  Module.Basis.ofEquivFun (positionBasisCoordinates N b)

theorem positionBasis_equivFun (N : ℕ) (b : Module.Basis ι R E) :
    (positionBasis N b).equivFun = positionBasisCoordinates N b :=
  Module.Basis.equivFun_ofEquivFun _

theorem positionBasis_equivFun_symm (N : ℕ) (b : Module.Basis ι R E) (y : (Fin N × ι) → R)
    (i : Fin N) : (positionBasis N b).equivFun.symm y i = b.equivFun.symm (fun j => y (i, j)) := by
  rw [positionBasis_equivFun]
  rfl

theorem positionBasis_apply (N : ℕ) (b : Module.Basis ι R E) (p : Fin N × ι) :
    positionBasis N b p = Pi.single p.1 (b p.2) := by
  apply (positionBasisCoordinates N b).injective
  have hp := (positionBasis N b).equivFun_self p
  rw [positionBasis_equivFun] at hp
  funext z
  rw [hp]
  by_cases h : z.1 = p.1
  · rcases z with ⟨i, j⟩
    dsimp only at h
    subst i
    rcases p with ⟨k, l⟩
    simp [positionBasisCoordinates, Finsupp.single_apply]
  · have hpz : p ≠ z := fun hz => h (congrArg Prod.fst hz).symm
    simp [positionBasisCoordinates, h, hpz]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.PositionBasis.LocalAnalysis

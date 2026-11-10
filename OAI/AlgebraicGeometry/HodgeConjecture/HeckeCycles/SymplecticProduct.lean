module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData
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


set_option backward.privateInPublic true
@[expose] public section

/-! # Symplectic Product -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.SymplecticProduct.CM

/-! Symplectic matrices over a product ring are exactly pairs of
symplectic matrices over its two factors. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData
variable {I R S : Type*} [Fintype I] [DecidableEq I] [CommRing R] [CommRing S]

def pairMatrix (A : Matrix I I R) (B : Matrix I I S) : Matrix I I (R × S) :=
  fun i j => (A i j, B i j)

omit [Fintype I] [DecidableEq I] in
theorem pairMatrix_fst (A : Matrix I I R) (B : Matrix I I S) :
    (pairMatrix A B).map (RingHom.fst R S) = A := rfl

omit [Fintype I] [DecidableEq I] in
theorem pairMatrix_snd (A : Matrix I I R) (B : Matrix I I S) :
    (pairMatrix A B).map (RingHom.snd R S) = B := rfl

omit [Fintype I] [DecidableEq I] in
theorem matrix_ext (A B : Matrix I I (R × S))
    (h₁ : A.map (RingHom.fst R S) = B.map (RingHom.fst R S))
    (h₂ : A.map (RingHom.snd R S) = B.map (RingHom.snd R S)) : A = B := by
  apply Matrix.ext
  intro i j
  exact Prod.ext (congrFun (congrFun h₁ i) j) (congrFun (congrFun h₂ i) j)

theorem pairMatrix_one : pairMatrix (1 : Matrix I I R) (1 : Matrix I I S) = 1 := by
  apply matrix_ext
  · rw [pairMatrix_fst]
    exact ((RingHom.fst R S).mapMatrix.map_one).symm
  · rw [pairMatrix_snd]
    exact ((RingHom.snd R S).mapMatrix.map_one).symm

omit [DecidableEq I] in
theorem pairMatrix_mul (A C : Matrix I I R) (B D : Matrix I I S) :
    pairMatrix (A * C) (B * D) = pairMatrix A B * pairMatrix C D := by
  apply matrix_ext
  · rw [pairMatrix_fst, Matrix.map_mul, pairMatrix_fst, pairMatrix_fst]
  · rw [pairMatrix_snd, Matrix.map_mul, pairMatrix_snd, pairMatrix_snd]

theorem pairMatrix_symplectic (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I R) (h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I S) :
    pairMatrix g.val h.val ∈ Matrix.symplecticGroup I (R × S) := by
  apply SymplecticGroup.mem_iff'.mpr
  apply matrix_ext
  · rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.map_J,
      pairMatrix_fst, SymplecticGroup.mem_iff'.mp g.property]
  · rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.map_J,
      pairMatrix_snd, SymplecticGroup.mem_iff'.mp h.property]

def pair : (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I R × RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I S) →* RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I (R × S) where
  toFun a := ⟨pairMatrix a.1.val a.2.val, pairMatrix_symplectic a.1 a.2⟩
  map_one' := Subtype.ext pairMatrix_one
  map_mul' a b := Subtype.ext (pairMatrix_mul a.1.val b.1.val a.2.val b.2.val)

theorem pair_fst (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I R) (h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I S) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RingHom.fst R S) (pair (g, h)) = g :=
  Subtype.ext (pairMatrix_fst g.val h.val)

theorem pair_snd (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I R) (h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I S) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RingHom.snd R S) (pair (g, h)) = h :=
  Subtype.ext (pairMatrix_snd g.val h.val)

theorem pair_projections (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I (R × S)) :
    pair (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RingHom.fst R S) g, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RingHom.snd R S) g) = g := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  exact Prod.eta (g.val i j)

theorem pair_eq_one (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I R) (h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I S) : pair (g, h) = 1 ↔ g = 1 ∧ h = 1 := by
  constructor
  · intro he
    constructor
    · have h₁ := congrArg (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RingHom.fst R S)) he
      rwa [pair_fst, map_one] at h₁
    · have h₂ := congrArg (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RingHom.snd R S)) he
      rwa [pair_snd, map_one] at h₂
  · rintro ⟨rfl, rfl⟩
    exact pair.map_one

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.SymplecticProduct.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.SymplecticProduct.CM.Phase

/-! Coordinate projections of the actual product-ring symplectic
phase action are the two factor actions. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SymplecticProduct.CM
variable {I R S : Type*} [Fintype I] [DecidableEq I] [CommRing R] [CommRing S]

theorem phase_fst (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I R) (h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I S) (p q : I → R × S) (i : I ⊕ I) :
    (((pair (g, h)).val *ᵥ Sum.elim p q) i).1 =
      (g.val *ᵥ Sum.elim (fun j => (p j).1) (fun j => (q j).1)) i := by
  change (RingHom.fst R S) ((pairMatrix g.val h.val *ᵥ Sum.elim p q) i) = _
  rw [RingHom.map_mulVec, pairMatrix_fst]
  have he : (fun j => (RingHom.fst R S) (Sum.elim p q j)) =
      Sum.elim (fun j => (p j).1) (fun j => (q j).1) := by
    funext j
    cases j <;> rfl
  dsimp only [Function.comp_def]
  rw [he]

theorem phase_snd (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I R) (h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I S) (p q : I → R × S) (i : I ⊕ I) :
    (((pair (g, h)).val *ᵥ Sum.elim p q) i).2 =
      (h.val *ᵥ Sum.elim (fun j => (p j).2) (fun j => (q j).2)) i := by
  change (RingHom.snd R S) ((pairMatrix g.val h.val *ᵥ Sum.elim p q) i) = _
  rw [RingHom.map_mulVec, pairMatrix_snd]
  have he : (fun j => (RingHom.snd R S) (Sum.elim p q j)) =
      Sum.elim (fun j => (p j).2) (fun j => (q j).2) := by
    funext j
    cases j <;> rfl
  dsimp only [Function.comp_def]
  rw [he]

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.SymplecticProduct.CM.Phase

end

end OAI

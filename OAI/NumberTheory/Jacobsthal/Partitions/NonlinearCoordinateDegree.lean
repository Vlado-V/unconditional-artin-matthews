module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Basic.Complex.Basic
public import OAI.NumberTheory.Jacobsthal.Partitions.NestedCoordinates
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import OAI.NumberTheory.Jacobsthal.Estimates.NestedDegreeBounds
public import OAI.NumberTheory.Jacobsthal.Estimates.NestedPartials


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

namespace Erdos970

section

namespace ErdosCriticalGeometry

theorem irreducible_of_constant_polynomial (p : Polynomial ℂ)
    (hp : Irreducible (Polynomial.C p : Nested ℂ)) : Irreducible p := by
  refine ⟨fun h => hp.not_isUnit (Polynomial.isUnit_C.mpr h), ?_⟩
  intro a b hab
  have h := hp.2 (show Polynomial.C p = Polynomial.C a*Polynomial.C b by rw [hab, map_mul])
  exact h.imp Polynomial.isUnit_C.mp Polynomial.isUnit_C.mp

theorem nonlinear_outer_degree_pos (E : MV ℂ ≃ₐ[ℂ] Nested ℂ) (i : Fin 2)
    (hXi : E (MvPolynomial.X i) = Polynomial.C Polynomial.X)
    (Q : MV ℂ) (hQ : Irreducible Q) (hdeg : 1 < Q.totalDegree) : 0 < (E Q).natDegree := by
  have hC (c : ℂ) : E (MvPolynomial.C c) = Polynomial.C (Polynomial.C c) := by
    simpa using E.commutes c
  have hEQ : Irreducible (E Q) := (MulEquiv.irreducible_iff E.toMulEquiv).mpr hQ
  by_contra! hzero
  have he : E Q = Polynomial.C ((E Q).coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hzero
  have hc : Irreducible ((E Q).coeff 0) := irreducible_of_constant_polynomial _ (he ▸ hEQ)
  have hlin := Polynomial.eq_X_add_C_of_degree_le_one
    (IsAlgClosed.degree_eq_one_of_irreducible ℂ hc).le
  let a : ℂ := ((E Q).coeff 0).coeff 1
  let b : ℂ := ((E Q).coeff 0).coeff 0
  have hQlin : Q = MvPolynomial.C a*MvPolynomial.X i+MvPolynomial.C b := by
    apply E.injective
    rw [map_add, map_mul, hC, hC, hXi, he, hlin]
    simp only [map_add, map_mul, a, b]
  have ht : Q.totalDegree ≤ 1 := by
    rw [hQlin]
    apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
    · simp
  omega

theorem nonlinear_nestedX_degree_pos (Q : MV ℂ) (hQ : Irreducible Q) (hdeg : 1 < Q.totalDegree) :
    0 < (nestedX ℂ Q).natDegree :=
  nonlinear_outer_degree_pos (nestedX ℂ) 1 (nestedX_X_one ℂ) Q hQ hdeg

theorem nonlinear_nestedY_degree_pos (Q : MV ℂ) (hQ : Irreducible Q) (hdeg : 1 < Q.totalDegree) :
    0 < (nestedY ℂ Q).natDegree :=
  nonlinear_outer_degree_pos (nestedY ℂ) 0 (nestedY_X_zero ℂ) Q hQ hdeg

theorem nonlinear_partial_zero_ne (Q : MV ℂ) (hQ : Irreducible Q) (hdeg : 1 < Q.totalDegree) :
    MvPolynomial.pderiv 0 Q ≠ 0 := by
  intro hz
  have hd := congrArg (nestedX ℂ) hz
  rw [nestedX_partial_zero, map_zero] at hd
  exact (nonlinear_nestedX_degree_pos Q hQ hdeg).ne' (Polynomial.derivative_eq_zero.mp hd)

theorem nonlinear_partial_one_ne (Q : MV ℂ) (hQ : Irreducible Q) (hdeg : 1 < Q.totalDegree) :
    MvPolynomial.pderiv 1 Q ≠ 0 := by
  intro hz
  have hd := congrArg (nestedY ℂ) hz
  rw [nestedY_partial_one, map_zero] at hd
  exact (nonlinear_nestedY_degree_pos Q hQ hdeg).ne' (Polynomial.derivative_eq_zero.mp hd)

theorem nonlinear_partial_not_dvd (Q : MV ℂ) (hQ : Irreducible Q) (hdeg : 1 < Q.totalDegree)
    (i : Fin 2) : ¬ Q ∣ MvPolynomial.pderiv i Q := by
  have hn : MvPolynomial.pderiv i Q ≠ 0 := by
    fin_cases i
    · exact nonlinear_partial_zero_ne Q hQ hdeg
    · exact nonlinear_partial_one_ne Q hQ hdeg
  intro hd
  have h1 := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hd hn
  have h2 := partial_totalDegree_le ℂ Q i
  omega

end ErdosCriticalGeometry

end

end Erdos970

end OAI

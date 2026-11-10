module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.Jacobsthal.Partitions.NestedCoordinates
public import Mathlib.Algebra.MvPolynomial.PDeriv
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

namespace OAI

namespace Erdos970

section

namespace ErdosCriticalGeometry

variable (R : Type*) [CommSemiring R]

theorem unique_degree_le_totalDegree (P : MvPolynomial (Fin 1) R) :
    (MvPolynomial.uniqueAlgEquiv R (Fin 1) P).natDegree ≤ P.totalDegree := by
  classical
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [MvPolynomial.coeff_uniqueAlgEquiv]
  by_contra hc
  have h := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hc)
  simp only [Finsupp.sum_single_index] at h
  exact (not_le_of_gt hk) h

theorem nestedX_degree_le (Q : MV R) : (nestedX R Q).natDegree ≤ Q.totalDegree := by
  change (Polynomial.map (MvPolynomial.uniqueAlgEquiv R (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv R 1 Q)).natDegree ≤ _
  exact Polynomial.natDegree_map_le.trans
    ((MvPolynomial.natDegree_finSuccEquiv Q).le.trans (MvPolynomial.degreeOf_le_totalDegree Q 0))

theorem nestedX_coefficient_degree_le (Q : MV R) (k : ℕ) :
    ((nestedX R Q).coeff k).natDegree ≤ Q.totalDegree := by
  change ((Polynomial.map (MvPolynomial.uniqueAlgEquiv R (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv R 1 Q)).coeff k).natDegree ≤ _
  rw [Polynomial.coeff_map]
  apply (unique_degree_le_totalDegree R _).trans
  by_cases h : (MvPolynomial.finSuccEquiv R 1 Q).coeff k = 0
  · simp [h]
  · have hb := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le Q k h
    omega

theorem nestedY_degree_le (Q : MV R) : (nestedY R Q).natDegree ≤ Q.totalDegree := by
  have h := nestedX_degree_le R (MvPolynomial.renameEquiv R (Equiv.swap (0 : Fin 2) 1) Q)
  simpa only [MvPolynomial.totalDegree_renameEquiv, nestedY, AlgEquiv.trans_apply] using h

theorem nestedY_coefficient_degree_le (Q : MV R) (k : ℕ) :
    ((nestedY R Q).coeff k).natDegree ≤ Q.totalDegree := by
  have h := nestedX_coefficient_degree_le R (MvPolynomial.renameEquiv R (Equiv.swap (0 : Fin 2) 1) Q) k
  simpa only [MvPolynomial.totalDegree_renameEquiv, nestedY, AlgEquiv.trans_apply] using h

theorem partial_totalDegree_le (Q : MV R) (i : Fin 2) :
    (MvPolynomial.pderiv i Q).totalDegree ≤ Q.totalDegree-1 := by
  classical
  apply Finset.sup_le
  intro m hm
  have hc := MvPolynomial.mem_support_iff.mp hm
  rw [MvPolynomial.coeff_pderiv] at hc
  have hQ := MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hc)
  have hd := MvPolynomial.le_totalDegree hQ
  rw [Finsupp.sum_add_index] at hd
  · simp only [Finsupp.sum_single_index] at hd
    omega
  · simp
  · intros
    rfl

end ErdosCriticalGeometry

end

end Erdos970

end OAI

module

public import ArtinMatthews.SpectralCuspEisensteinEquivalentWidths
public import ArtinMatthews.SpectralCuspEisensteinInfinity
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual cusp-equivalence classes form a finite quotient of integral charts.
Finiteness is derived from the actual finite-index coset space. -/
noncomputable section
open Set Matrix
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0EisensteinCuspsEquivalent_symm (N : ℕ) {r a : SL(2,ℤ)}
    (h : gamma0EisensteinCuspsEquivalent N r a) :
    gamma0EisensteinCuspsEquivalent N a r := by
  obtain ⟨M,hM⟩ := (gamma0EisensteinCuspsEquivalent_iff N r a).mp h
  apply (gamma0EisensteinCuspsEquivalent_iff N a r).mpr
  refine ⟨⟨M.val⁻¹,?_⟩,?_⟩
  · change r⁻¹*M.val⁻¹*a ∈ CongruenceSubgroup.Gamma0 N
    have he : r⁻¹*M.val⁻¹*a=(a⁻¹*M.val*r)⁻¹ := by group
    rw [he]
    exact (CongruenceSubgroup.Gamma0 N).inv_mem M.property
  · change ((M.val⁻¹ : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0=0
    simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,hM]

theorem gamma0EisensteinCuspsEquivalent_trans (N : ℕ) {r a b : SL(2,ℤ)}
    (h : gamma0EisensteinCuspsEquivalent N r a) (h' : gamma0EisensteinCuspsEquivalent N a b) :
    gamma0EisensteinCuspsEquivalent N r b := by
  obtain ⟨M,hM⟩ := (gamma0EisensteinCuspsEquivalent_iff N r a).mp h
  obtain ⟨R,hR⟩ := (gamma0EisensteinCuspsEquivalent_iff N a b).mp h'
  apply (gamma0EisensteinCuspsEquivalent_iff N r b).mpr
  refine ⟨⟨R.val*M.val,?_⟩,?_⟩
  · change b⁻¹*(R.val*M.val)*r ∈ CongruenceSubgroup.Gamma0 N
    have he : b⁻¹*(R.val*M.val)*r=(b⁻¹*R.val*a)*(a⁻¹*M.val*r) := by group
    rw [he]
    exact (CongruenceSubgroup.Gamma0 N).mul_mem R.property M.property
  · change ((R.val*M.val : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0=0
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,hR,hM,zero_mul,mul_zero,add_zero]

def gamma0EisensteinCuspSetoid (N : ℕ) : Setoid SL(2,ℤ) where
  r := gamma0EisensteinCuspsEquivalent N
  iseqv := ⟨gamma0EisensteinCuspsEquivalent_refl N,fun h => gamma0EisensteinCuspsEquivalent_symm N h,
    fun h h' => gamma0EisensteinCuspsEquivalent_trans N h h'⟩

def Gamma0EisensteinCuspClasses (N : ℕ) := Quotient (gamma0EisensteinCuspSetoid N)

def gamma0EisensteinCuspClass (N : ℕ) (r : SL(2,ℤ)) : Gamma0EisensteinCuspClasses N :=
  Quotient.mk (gamma0EisensteinCuspSetoid N) r

theorem gamma0EisensteinCuspClass_eq_iff (N : ℕ) (r a : SL(2,ℤ)) :
    gamma0EisensteinCuspClass N r=gamma0EisensteinCuspClass N a ↔
      gamma0EisensteinCuspsEquivalent N r a :=
  ⟨fun h => Quotient.exact h,fun h => Quotient.sound h⟩

def gamma0EisensteinCuspClassRepresentative (N : ℕ) (i : Gamma0EisensteinCuspClasses N) :
    SL(2,ℤ) :=
  Quotient.out (s:=gamma0EisensteinCuspSetoid N) i

theorem gamma0EisensteinCuspClassRepresentative_class (N : ℕ) (i : Gamma0EisensteinCuspClasses N) :
    gamma0EisensteinCuspClass N (gamma0EisensteinCuspClassRepresentative N i)=i :=
  Quotient.out_eq i

theorem gamma0EisensteinCuspClass_of_cosets_surjective (N : ℕ) :
    Function.Surjective (fun i : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N =>
      gamma0EisensteinCuspClass N i.out) := by
  intro c
  let r := gamma0EisensteinCuspClassRepresentative N c
  let i : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N := QuotientGroup.mk r
  refine ⟨i,?_⟩
  rw [← gamma0EisensteinCuspClassRepresentative_class N c]
  apply (gamma0EisensteinCuspClass_eq_iff N i.out r).mpr
  apply (gamma0EisensteinCuspsEquivalent_iff N i.out r).mpr
  refine ⟨⟨1,?_⟩,?_⟩
  · have hi : i.out⁻¹*r ∈ CongruenceSubgroup.Gamma0 N :=
      QuotientGroup.eq.mp (Quotient.out_eq' i)
    change r⁻¹*1*i.out ∈ CongruenceSubgroup.Gamma0 N
    simpa only [mul_one,_root_.mul_inv_rev,inv_inv] using (CongruenceSubgroup.Gamma0 N).inv_mem hi
  · simp

instance gamma0EisensteinCuspClasses_finite (N : ℕ) [NeZero N] :
    Finite (Gamma0EisensteinCuspClasses N) :=
  Finite.of_surjective _ (gamma0EisensteinCuspClass_of_cosets_surjective N)

instance gamma0EisensteinCuspClasses_fintype (N : ℕ) [NeZero N] :
    Fintype (Gamma0EisensteinCuspClasses N) := Fintype.ofFinite _

instance gamma0EisensteinCuspClasses_decidableEq (N : ℕ) :
    DecidableEq (Gamma0EisensteinCuspClasses N) := Classical.decEq _

theorem gamma0CuspEisensteinIndicator_eq_cuspClass (N : ℕ) (r a : SL(2,ℤ)) :
    gamma0CuspEisensteinIndicator N r a =
      if gamma0EisensteinCuspClass N r=gamma0EisensteinCuspClass N a then 1 else 0 := by
  classical
  simp only [gamma0CuspEisensteinIndicator,gamma0EisensteinCuspClass_eq_iff]

end ArtinMatthews

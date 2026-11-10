module

public import ArtinMatthews.VaryingKummerAnalyticIdealModuleResidueCoordinates
public import ArtinMatthews.VaryingKummerAnalyticMixedIntegralIdeal
public import ArtinMatthews.VaryingKummerAnalyticIdealFrequencyLabels
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.RingTheory.PiTensorProduct
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


set_option backward.privateInPublic true
@[expose] public section

/-! Actual trace representation of the primitive additive character on
I/(MI). Rational phases on an actual integral basis construct the frequency;
no globally principal different or inverse ideal generator is assumed. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal Module
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def idealModuleTraceChar (I : Ideal (𝓞 K)) (α : K) : AddChar I ℂ :=
  (fieldTraceAddChar K α).compAddMonoidHom (Submodule.subtype I).toAddMonoidHom

theorem idealModuleTraceChar_apply (I : Ideal (𝓞 K)) (α : K) (a : I) :
    idealModuleTraceChar K I α a = fieldTraceAddChar K α a.val := rfl

def idealModuleQuotientAddChar (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥) :
    AddChar (IdealModuleResidue I M) ℂ :=
  (idealTraceAddChar K M hM).compAddMonoidHom
    (idealModuleTrivialization I M hI hM).symm.toAddMonoidHom

def idealModuleLiftedAddChar (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥) :
    AddChar I ℂ :=
  (idealTraceAddChar K M hM).compAddMonoidHom
    (idealResidueCoordinate I M hI hM).toAddMonoidHom

theorem idealModuleLiftedAddChar_quotient (I M : Ideal (𝓞 K))
    (hI : I ≠ ⊥) (hM : M ≠ ⊥) (a : I) :
    idealModuleLiftedAddChar K I M hI hM a =
      idealModuleQuotientAddChar K I M hI hM (Submodule.Quotient.mk a) := rfl

theorem mixedIntegralIdealBasis_coe (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (j : MixedIdealIndex K (integralIdealFractionalUnit I hI)) :
    ((mixedIntegralIdealBasis K I hI j).val : K) =
      basisOfFractionalIdeal K (integralIdealFractionalUnit I hI) j := by
  rw [basisOfFractionalIdeal_apply]
  change (((integralIdealToFractional K I hI).symm
    (fractionalIdealBasis K (integralIdealFractionalUnit I hI).val j)).val : K) = _
  have H := integralIdealToFractional_coe K I hI
    ((integralIdealToFractional K I hI).symm
      (fractionalIdealBasis K (integralIdealFractionalUnit I hI).val j))
  rw [LinearEquiv.apply_symm_apply] at H
  exact H.symm

private theorem addChar_sum {A : Type*} [AddCommMonoid A] (χ : AddChar A ℂ)
    {ι : Type*} (s : Finset ι) (f : ι → A) :
    χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, Finset.prod_insert hi,
      AddChar.map_add_eq_mul, ih]

private theorem addChar_eq_of_basis {A : Type*} [AddCommGroup A]
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ A) (χ ψ : AddChar A ℂ)
    (h : ∀ j, χ (b j) = ψ (b j)) : χ = ψ := by
  ext a
  conv_lhs => rw [← b.sum_repr a]
  conv_rhs => rw [← b.sum_repr a]
  simp only [addChar_sum, AddChar.map_zsmul_eq_zpow, h]

def idealModuleBasisPhase (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)
    (j : MixedIdealIndex K (integralIdealFractionalUnit I hI)) : ℚ :=
  Algebra.trace ℚ K ((idealTraceGenerator K M hM : K) *
    (Quotient.out (idealResidueCoordinate I M hI hM
      (mixedIntegralIdealBasis K I hI j)) : 𝓞 K))

/-- The trace-dual basis turns the actual rational basis phases into a
genuine field element representing the pulled-back primitive character. -/
def idealModuleTraceFrequencyBase (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥) : K :=
  ∑ j, idealModuleBasisPhase K I M hI hM j •
    (basisOfFractionalIdeal K (integralIdealFractionalUnit I hI)).traceDual j

theorem idealModuleTraceFrequencyBase_trace_basis (I M : Ideal (𝓞 K))
    (hI : I ≠ ⊥) (hM : M ≠ ⊥)
    (j : MixedIdealIndex K (integralIdealFractionalUnit I hI)) :
    Algebra.trace ℚ K (idealModuleTraceFrequencyBase K I M hI hM *
      ((mixedIntegralIdealBasis K I hI j).val : K)) = idealModuleBasisPhase K I M hI hM j := by
  rw [mixedIntegralIdealBasis_coe]
  simp only [idealModuleTraceFrequencyBase, Finset.sum_mul, smul_mul_assoc,
    map_sum, map_smul, Basis.trace_traceDual_mul, smul_eq_mul]
  simp

/-- This is an equality of actual additive characters on the whole ideal,
not a presumed trace representation. -/
theorem idealModuleTraceFrequencyBase_character (I M : Ideal (𝓞 K))
    (hI : I ≠ ⊥) (hM : M ≠ ⊥) :
    idealModuleTraceChar K I (idealModuleTraceFrequencyBase K I M hI hM) =
      idealModuleLiftedAddChar K I M hI hM := by
  apply addChar_eq_of_basis (mixedIntegralIdealBasis K I hI)
  intro j
  rw [idealModuleTraceChar_apply, fieldTraceAddChar_apply,
    idealModuleTraceFrequencyBase_trace_basis]
  change Complex.exp _ = idealTraceAddChar K M hM
    (idealResidueCoordinate I M hI hM (mixedIntegralIdealBasis K I hI j))
  rw [← Ideal.Quotient.mk_out
    (idealResidueCoordinate I M hI hM (mixedIntegralIdealBasis K I hI j)),
    idealTraceAddChar_mk]
  rfl

theorem idealModuleTraceChar_eq_one_iff_mem_dual (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (α : K) :
    idealModuleTraceChar K I α = 1 ↔
      α ∈ FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [FractionalIdeal.mem_dual (FractionalIdeal.coeIdeal_ne_zero.mpr hI)]
  constructor
  · intro h a ha
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp ha
    have H := congrArg (fun χ : AddChar I ℂ => χ ⟨b, hb⟩) h
    exact (fieldTraceAddChar_eq_one_iff K α b).mp H
  · intro h
    ext a
    apply (fieldTraceAddChar_eq_one_iff K α a.val).mpr
    exact h _ (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰ a.property)

theorem idealModuleTraceChar_sub (I : Ideal (𝓞 K)) (α β : K) :
    idealModuleTraceChar K I (α - β) =
      idealModuleTraceChar K I α / idealModuleTraceChar K I β := by
  ext a
  simpa only [idealModuleTraceChar_apply, AddChar.div_apply'] using
    congrArg (fun χ : AddChar (𝓞 K) ℂ => χ a.val) (fieldTraceAddChar_sub K α β)

theorem idealModuleTraceChar_eq_iff_sub_mem_dual (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (α β : K) :
    idealModuleTraceChar K I α = idealModuleTraceChar K I β ↔
      α - β ∈ FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [← idealModuleTraceChar_eq_one_iff_mem_dual K I hI, idealModuleTraceChar_sub, div_eq_one]

end
end ArtinMatthews.VaryingKummerAnalytic

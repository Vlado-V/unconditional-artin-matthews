module

public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveThetaDualResidue
public import ArtinMatthews.VaryingKummerAnalyticIdealModuleLinearComparison
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
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.RingTheory.Henselian
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

/-! Genuine inverse-character residue matching on the trace-dual ideal.
The integral representative is obtained by Mathlib's actual denominator
clearing, and the comparison scalar is proved to be a unit. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)

abbrev mixedPrimitiveDualFractionalIdeal : FractionalIdeal (𝓞 K)⁰ K :=
  dual ℤ ℚ ((M*I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)

def mixedPrimitiveDualIntegralIdeal : Ideal (𝓞 K) :=
  (mixedPrimitiveDualFractionalIdeal K I M).num

include hI hM in
theorem mixedPrimitiveDualIntegralIdeal_ne_bot :
    mixedPrimitiveDualIntegralIdeal K I M ≠ ⊥ := by
  intro h
  exact (FractionalIdeal.dual_ne_zero ℤ ℚ
    (FractionalIdeal.coeIdeal_ne_zero.mpr (mul_ne_zero hM hI)))
      (FractionalIdeal.zero_of_num_eq_bot (by simp) h)

def mixedPrimitiveDualIntegralEquiv :
    (mixedPrimitiveDualFractionalIdeal K I M).val ≃ₗ[𝓞 K]
      mixedPrimitiveDualIntegralIdeal K I M :=
  FractionalIdeal.equivNum (nonZeroDivisors.coe_ne_zero _)

theorem mixedPrimitiveDualIntegralEquiv_coe
    (β : (mixedPrimitiveDualFractionalIdeal K I M).val) :
    (((mixedPrimitiveDualIntegralEquiv K I M β : 𝓞 K)) : K) =
      (((mixedPrimitiveDualFractionalIdeal K I M).den : 𝓞 K) : K) * (β : K) := by
  exact FractionalIdeal.equivNum_apply (nonZeroDivisors.coe_ne_zero _) β

/-- The actual dual residue is a unit multiple of the canonical coordinate
on its actual denominator-cleared integral representative. -/
theorem mixedPrimitiveDualResidue_exists_unit :
    ∃ u : ((𝓞 K) ⧸ M)ˣ, ∀ β : (mixedPrimitiveDualFractionalIdeal K I M).val,
      idealModuleDualResidue K I M hI hM β β.property =
        (u : (𝓞 K) ⧸ M) * idealResidueCoordinate (mixedPrimitiveDualIntegralIdeal K I M) M
          (mixedPrimitiveDualIntegralIdeal_ne_bot K I M hI hM) hM
          (mixedPrimitiveDualIntegralEquiv K I M β) := by
  let f := (idealModuleDualResidueLinear K I M hI hM).comp
    (mixedPrimitiveDualIntegralEquiv K I M).symm.toLinearMap
  have hf : Function.Surjective f :=
    (idealModuleDualResidueLinear_surjective K I M hI hM).comp
      (mixedPrimitiveDualIntegralEquiv K I M).symm.surjective
  obtain ⟨u,hu⟩ := idealModuleLinearMap_exists_unit
    (mixedPrimitiveDualIntegralIdeal K I M) M
    (mixedPrimitiveDualIntegralIdeal_ne_bot K I M hI hM) hM f hf
  refine ⟨u,fun β => ?_⟩
  have H := hu (mixedPrimitiveDualIntegralEquiv K I M β)
  simpa only [f, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply, idealModuleDualResidueLinear_apply] using H

/-- No unit-modulus scalar is postulated: it is the inverse character value
of the actual comparison unit furnished by the two residue coordinates. -/
theorem mixedPrimitiveDualWeight_exists_scalar (χ : MulChar ((𝓞 K) ⧸ M) ℂ) :
    ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ β : (mixedPrimitiveDualFractionalIdeal K I M).val,
      χ⁻¹ (idealModuleDualResidue K I M hI hM β β.property) =
        κ * χ⁻¹ (idealResidueCoordinate (mixedPrimitiveDualIntegralIdeal K I M) M
          (mixedPrimitiveDualIntegralIdeal_ne_bot K I M hI hM) hM
          (mixedPrimitiveDualIntegralEquiv K I M β)) := by
  let : Finite ((𝓞 K) ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient hM
  let : Fintype ((𝓞 K) ⧸ M) := Fintype.ofFinite _
  obtain ⟨u,hu⟩ := mixedPrimitiveDualResidue_exists_unit K I M hI hM
  refine ⟨χ⁻¹ (u : (𝓞 K) ⧸ M),
    Complex.norm_eq_one_of_mem_rootsOfUnity ((χ⁻¹).apply_mem_rootsOfUnity u),fun β => ?_⟩
  rw [hu, map_mul]

end
end ArtinMatthews.VaryingKummerAnalytic

module

public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveThetaFourier
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual trace-dual residue label is linear, with exact kernel dual(I).
This supplies the algebraic compatibility needed to unfold the transformed
weighted theta through global units and inverse ideal classes. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)

theorem idealModuleDualResidue_eq_of_character (β : K)
    (hβ : β ∈ dual ℤ ℚ ((M*I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))
    (r : (𝓞 K) ⧸ M)
    (H : ∀ a : I, idealModuleTraceChar K I β a =
      idealTraceAddChar K M hM (r * idealResidueCoordinate I M hI hM a)) :
    idealModuleDualResidue K I M hI hM β hβ = r := by
  apply AddChar.to_mulShift_inj_of_isPrimitive (idealTraceAddChar_isPrimitive K M hM)
  ext x
  obtain ⟨a,rfl⟩ := idealResidueCoordinate_surjective I M hI hM x
  change idealTraceAddChar K M hM
      (idealModuleDualResidue K I M hI hM β hβ * idealResidueCoordinate I M hI hM a) = _
  rw [← idealModuleDualResidue_character]
  exact H a

/-- The residue label constructed from finite trace duality is an actual
O-linear map, rather than merely an arbitrary enumeration. -/
def idealModuleDualResidueLinear :
    (dual ℤ ℚ ((M*I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)).val →ₗ[𝓞 K]
      (𝓞 K) ⧸ M where
  toFun β := idealModuleDualResidue K I M hI hM β β.property
  map_add' β γ := by
    apply idealModuleDualResidue_eq_of_character K I M hI hM
    intro a
    calc
      _ = idealModuleTraceChar K I β a * idealModuleTraceChar K I γ a := by
        simp only [idealModuleTraceChar_apply, fieldTraceAddChar_apply,
          Submodule.coe_add, add_mul, map_add, Rat.cast_add, Complex.exp_add]
      _ = _ := by
        rw [idealModuleDualResidue_character K I M hI hM β β.property,
          idealModuleDualResidue_character K I M hI hM γ γ.property,
          add_mul, AddChar.map_add_eq_mul]
  map_smul' b β := by
    apply idealModuleDualResidue_eq_of_character K I M hI hM
    intro a
    calc
      _ = idealModuleTraceChar K I β (b • a) := by
        simp only [idealModuleTraceChar_apply, fieldTraceAddChar_apply]
        congr 3
        congr 1
        change ((b : K) * (β : K)) * ((a : 𝓞 K) : K) =
          (β : K) * ((b * (a : 𝓞 K) : 𝓞 K) : K)
        simp only [map_mul]
        ring
      _ = _ := by
        rw [idealModuleDualResidue_character K I M hI hM β β.property, map_smul]
        congr 1
        change idealModuleDualResidue K I M hI hM β β.property *
          (Ideal.Quotient.mk M b * idealResidueCoordinate I M hI hM a) =
            (Ideal.Quotient.mk M b * idealModuleDualResidue K I M hI hM β β.property) *
              idealResidueCoordinate I M hI hM a
        ring

@[simp] theorem idealModuleDualResidueLinear_apply
    (β : (dual ℤ ℚ ((M*I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)).val) :
    idealModuleDualResidueLinear K I M hI hM β =
      idealModuleDualResidue K I M hI hM β β.property := rfl

theorem idealModuleDualResidueLinear_surjective :
    Function.Surjective (idealModuleDualResidueLinear K I M hI hM) := by
  intro r
  exact ⟨⟨idealModuleFrequencyResidueValue K I M hI hM r,
    idealModuleFrequencyResidueValue_mem_dual K I M hI hM r⟩,
    idealModuleDualResidue_frequencyResidueValue K I M hI hM r⟩

theorem idealModuleDualResidueLinear_eq_zero_iff
    (β : (dual ℤ ℚ ((M*I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)).val) :
    idealModuleDualResidueLinear K I M hI hM β = 0 ↔
      (β : K) ∈ dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) := by
  have hz := map_zero (idealModuleDualResidueLinear K I M hI hM)
  rw [← hz]
  change idealModuleDualResidue K I M hI hM β β.property =
    idealModuleDualResidue K I M hI hM 0 (by exact (dual ℤ ℚ _).zero_mem) ↔ _
  simpa only [sub_zero] using idealModuleDualResidue_eq_iff_sub_mem_dual
    K I M hI hM (β : K) 0 β.property ((dual ℤ ℚ _).zero_mem)

/-- Scalar multiplication on the genuine dual ideal becomes multiplication
by the residue of that scalar. -/
theorem idealModuleDualResidueLinear_smul (b : 𝓞 K)
    (β : (dual ℤ ℚ ((M*I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)).val) :
    idealModuleDualResidueLinear K I M hI hM (b • β) =
      Ideal.Quotient.mk M b * idealModuleDualResidueLinear K I M hI hM β :=
  (idealModuleDualResidueLinear K I M hI hM).map_smul b β

/-- The transformed inverse-character weight is invariant under actual
global units whenever the original residue character is trivial on them. -/
theorem idealModuleDualResidue_inverseWeight_unit
    (χ : MulChar ((𝓞 K) ⧸ M) ℂ)
    (hunit : ∀ u : (𝓞 K)ˣ, χ (Ideal.Quotient.mk M (u : 𝓞 K)) = 1)
    (u : (𝓞 K)ˣ)
    (β : (dual ℤ ℚ ((M*I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)).val) :
    χ⁻¹ (idealModuleDualResidueLinear K I M hI hM ((u : 𝓞 K) • β)) =
      χ⁻¹ (idealModuleDualResidueLinear K I M hI hM β) := by
  rw [idealModuleDualResidueLinear_smul, map_mul]
  have H : χ⁻¹ (Ideal.Quotient.mk M (u : 𝓞 K)) = 1 := by
    rw [MulChar.inv_apply_eq_inv', hunit, inv_one]
  rw [H, one_mul]

end
end ArtinMatthews.VaryingKummerAnalytic

module

public import ArtinMatthews.VaryingKummerAnalyticMixedCosetCoordinates
public import ArtinMatthews.VaryingKummerAnalyticIdealModuleCosets
public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveThetaFourier
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact grouping of the primitive ideal-residue theta into genuine lattice
cosets, and identification of its finite Fourier weight with the Gauss sum. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open Module NumberField FractionalIdeal
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open ArtinMatthews.ReusedTheta
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
set_option maxHeartbeats 800000
variable (K : Type*) [Field K] [NumberField K]
variable (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)

abbrev mixedConductorIdeal := integralIdealFractionalUnit (M*I) (mul_ne_zero hM hI)
abbrev MixedConductorIndex := MixedIdealIndex K (mixedConductorIdeal K I M hI hM)

variable [NeZero M]

local instance : Finite ((𝓞 K) ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance : Fintype ((𝓞 K) ⧸ M) := Fintype.ofFinite _

def mixedPrimitiveCosetPoint (r : (𝓞 K) ⧸ M) : MixedConductorIndex K I M hI hM → ℝ :=
  mixedIdealCosetPoint K (mixedConductorIdeal K I M hI hM)
    ((idealModuleResidueRepresentative I M hI hM r : 𝓞 K) : K)

def mixedPrimitiveCosetEquiv : I ≃ ((𝓞 K) ⧸ M) × (MixedConductorIndex K I M hI hM → ℤ) :=
  (idealModuleCosetEquiv I M hI hM).trans
    (Equiv.prodCongr (Equiv.refl _) (mixedIntegralIdealBasis K (M*I) (mul_ne_zero hM hI)).equivFun.toEquiv)

omit [NeZero M] in
@[simp] theorem mixedPrimitiveCosetEquiv_fst (a : I) :
    (mixedPrimitiveCosetEquiv K I M hI hM a).1 = idealResidueCoordinate I M hI hM a := rfl

omit [NeZero M] in
theorem mixedPrimitiveCosetEquiv_symm_coe
    (p : ((𝓞 K) ⧸ M) × (MixedConductorIndex K I M hI hM → ℤ)) :
    (((mixedPrimitiveCosetEquiv K I M hI hM).symm p : 𝓞 K) : K) =
      ((idealModuleResidueRepresentative I M hI hM p.1 : 𝓞 K) : K) +
        ((fractionalIdealBasis K (mixedConductorIdeal K I M hI hM).val).equivFun.symm p.2 :
          (mixedConductorIdeal K I M hI hM).val) := by
  change (((idealModuleResidueRepresentative I M hI hM p.1 : 𝓞 K) +
    (((mixedIntegralIdealBasis K (M*I) (mul_ne_zero hM hI)).equivFun.symm p.2 : M*I) : 𝓞 K)) : K) = _
  congr 1
  have H := integralIdealToFractional_coe K (M*I) (mul_ne_zero hM hI)
    ((mixedIntegralIdealBasis K (M*I) (mul_ne_zero hM hI)).equivFun.symm p.2)
  rw [← H]
  congr 1
  simp [mixedIntegralIdealBasis, mixedConductorIdeal]

def mixedPrimitiveTheta (χ : MulChar ((𝓞 K) ⧸ M) ℂ) (u : logSpace K) (t : ℝ) : ℂ :=
  ∑' a : I, χ (idealResidueCoordinate I M hI hM a) *
    mixedComplexArchGaussian K ((a : 𝓞 K) : K) t u

theorem mixedPrimitiveCosetProduct_summable (χ : MulChar ((𝓞 K) ⧸ M) ℂ)
    (u : logSpace K) {t : ℝ} (ht : 0 < t) :
    Summable (fun p : ((𝓞 K) ⧸ M) × (MixedConductorIndex K I M hI hM → ℤ) =>
      χ p.1 * Complex.exp (-((Real.pi*t : ℝ) : ℂ) *
        ‖logScaledLattice (mixedIdealMatrix K (mixedConductorIdeal K I M hI hM))
          (mixedIdealLogScale K (mixedConductorIdeal K I M hI hM) u)
          (WithLp.toLp 2 (mixedPrimitiveCosetPoint K I M hI hM p.1) + euclideanInteger p.2)‖^2)) := by
  apply Summable.of_norm
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2
  refine ⟨?_, Summable.of_finite⟩
  intro r
  exact ((cosetLatticeTheta_summable
    (logScaledLattice (mixedIdealMatrix K (mixedConductorIdeal K I M hI hM))
      (mixedIdealLogScale K (mixedConductorIdeal K I M hI hM) u))
    (mixedPrimitiveCosetPoint K I M hI hM r) (Real.pi*t)
    (mul_pos Real.pi_pos ht)).mul_left (χ r)).norm

theorem mixedPrimitiveTheta_eq_cosets (χ : MulChar ((𝓞 K) ⧸ M) ℂ)
    (u : logSpace K) {t : ℝ} (ht : 0 < t) :
    mixedPrimitiveTheta K I M hI hM χ u t =
      congruenceTheta
        (logScaledLattice (mixedIdealMatrix K (mixedConductorIdeal K I M hI hM))
          (mixedIdealLogScale K (mixedConductorIdeal K I M hI hM) u))
        (mixedPrimitiveCosetPoint K I M hI hM) χ (Real.pi*t) := by
  unfold mixedPrimitiveTheta
  rw [← (mixedPrimitiveCosetEquiv K I M hI hM).symm.tsum_eq]
  have H (p : ((𝓞 K) ⧸ M) × (MixedConductorIndex K I M hI hM → ℤ)) :
      idealResidueCoordinate I M hI hM ((mixedPrimitiveCosetEquiv K I M hI hM).symm p) = p.1 :=
    congrArg Prod.fst ((mixedPrimitiveCosetEquiv K I M hI hM).apply_symm_apply p)
  simp_rw [H, mixedPrimitiveCosetEquiv_symm_coe, ← mixedIdealCosetPoint_gaussian]
  change (∑' p : ((𝓞 K) ⧸ M) × (MixedConductorIndex K I M hI hM → ℤ),
    χ p.1 * Complex.exp (-((Real.pi*t : ℝ) : ℂ) *
      ‖logScaledLattice (mixedIdealMatrix K (mixedConductorIdeal K I M hI hM))
        (mixedIdealLogScale K (mixedConductorIdeal K I M hI hM) u)
        (WithLp.toLp 2 (mixedPrimitiveCosetPoint K I M hI hM p.1) + euclideanInteger p.2)‖^2)) = _
  rw [(mixedPrimitiveCosetProduct_summable K I M hI hM χ u ht).tsum_prod, tsum_fintype]
  simp only [congruenceTheta, cosetLatticeTheta, tsum_mul_left]

omit [NeZero M] in
theorem mixedPrimitiveCosetPoint_character (r : (𝓞 K) ⧸ M)
    (z : MixedConductorIndex K I M hI hM → ℤ) :
    UnitAddTorus.mFourier z (torusProjection (mixedPrimitiveCosetPoint K I M hI hM r)) =
      idealTraceAddChar K M hM
        (idealModuleDualResidue K I M hI hM
          (mixedDualIntegerEquiv K (mixedConductorIdeal K I M hI hM) z)
          (mixedDualIntegerEquiv K (mixedConductorIdeal K I M hI hM) z).property * r) := by
  unfold mixedPrimitiveCosetPoint
  rw [mixedIdealCosetPoint_fourier]
  have H := idealModuleDualResidue_character K I M hI hM
    (mixedDualIntegerEquiv K (mixedConductorIdeal K I M hI hM) z)
    (mixedDualIntegerEquiv K (mixedConductorIdeal K I M hI hM) z).property
    (idealModuleResidueRepresentative I M hI hM r)
  rw [idealModuleResidueRepresentative_coordinate] at H
  rw [← H, idealModuleTraceChar_apply, fieldTraceAddChar_apply]
  congr 1
  rw [mul_comm (mixedDualIntegerEquiv K (mixedConductorIdeal K I M hI hM) z : K)]
  ring

theorem mixedPrimitiveCosetFourierWeight (χ : MulChar ((𝓞 K) ⧸ M) ℂ)
    (hχ : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals χ)
    (z : MixedConductorIndex K I M hI hM → ℤ) :
    congruenceThetaFourierWeight (mixedPrimitiveCosetPoint K I M hI hM) χ z =
      χ⁻¹ (idealModuleDualResidue K I M hI hM
        (mixedDualIntegerEquiv K (mixedConductorIdeal K I M hI hM) z)
        (mixedDualIntegerEquiv K (mixedConductorIdeal K I M hI hM) z).property) *
      idealTraceGaussSum K M χ := by
  unfold congruenceThetaFourierWeight
  simp_rw [mixedPrimitiveCosetPoint_character]
  exact idealTraceFourier_primitive K M χ hχ _

end
end ArtinMatthews.VaryingKummerAnalytic

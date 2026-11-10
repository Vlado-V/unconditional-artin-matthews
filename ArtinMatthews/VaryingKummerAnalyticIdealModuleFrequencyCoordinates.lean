module

public import ArtinMatthews.VaryingKummerAnalyticIdealModuleFrequencyLabels
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import ArtinMatthews.VaryingKummerAnalyticIdealModuleFrequencySeparation
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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
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

/-! Fixed-ideal integer coordinates, literal trace phases and uniform
integer-translate spacing for the actual primitive I/(MI) frequencies. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal Module
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

abbrev IdealModuleFrequencyIndex (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :=
  MixedIdealIndex K (integralIdealFractionalUnit I hI)

theorem idealModuleFrequencyIndex_card (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    Fintype.card (IdealModuleFrequencyIndex K I hI) = Module.finrank ℚ K :=
  mixedIdealIndex_card K _

def idealModuleIntegerCoordinates (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (a : I) :
    IdealModuleFrequencyIndex K I hI → ℤ :=
  (mixedIntegralIdealBasis K I hI).repr a

def idealModuleTraceCoordinates (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (α : K) :
    IdealModuleFrequencyIndex K I hI → ℝ := fun j =>
  (Algebra.trace ℚ K (α * basisOfFractionalIdeal K (integralIdealFractionalUnit I hI) j) : ℝ)

theorem idealModuleIntegerCoordinates_expansion (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (a : I) :
    (a.val : K) = ∑ j, (idealModuleIntegerCoordinates K I hI a j : ℚ) •
      basisOfFractionalIdeal K (integralIdealFractionalUnit I hI) j := by
  have H := congrArg (fun b : I => (b.val : K))
    ((mixedIntegralIdealBasis K I hI).sum_repr a).symm
  simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower, map_sum, map_zsmul,
    mixedIntegralIdealBasis_coe, Int.cast_smul_eq_zsmul, idealModuleIntegerCoordinates] using H

def idealModuleIntegerCoordinateConstant (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) : ℝ :=
  1 + ‖(mixedEmbedding.fractionalIdealLatticeBasis K
    (integralIdealFractionalUnit I hI)).equivFunL.toContinuousLinearMap‖

theorem idealModuleIntegerCoordinateConstant_pos (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    0 < idealModuleIntegerCoordinateConstant K I hI := by
  unfold idealModuleIntegerCoordinateConstant
  positivity

theorem idealModuleIntegerCoordinates_real_eq (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (a : I) :
    (fun j => (idealModuleIntegerCoordinates K I hI a j : ℝ)) =
      (mixedEmbedding.fractionalIdealLatticeBasis K (integralIdealFractionalUnit I hI)).equivFunL
        (mixedEmbedding K (a.val : K)) := by
  have H : (mixedEmbedding.fractionalIdealLatticeBasis K
      (integralIdealFractionalUnit I hI)).equivFun.symm
        (fun j => (idealModuleIntegerCoordinates K I hI a j : ℝ)) =
      mixedEmbedding K (a.val : K) := by
    rw [Basis.equivFun_symm_apply]
    conv_rhs => rw [idealModuleIntegerCoordinates_expansion K I hI a]
    simp only [map_sum, map_rat_smul, mixedEmbedding.fractionalIdealLatticeBasis_apply]
    apply Finset.sum_congr rfl
    intro j _
    exact (ratCast_smul_eq ℚ ℝ _ _).symm
  ext j
  change (idealModuleIntegerCoordinates K I hI a j : ℝ) =
    (mixedEmbedding.fractionalIdealLatticeBasis K (integralIdealFractionalUnit I hI)).repr
      (mixedEmbedding K (a.val : K)) j
  simpa only [LinearEquiv.apply_symm_apply, Basis.equivFun_apply] using congrArg
    (fun x => (mixedEmbedding.fractionalIdealLatticeBasis K
      (integralIdealFractionalUnit I hI)).equivFun x j) H

theorem idealModuleIntegerCoordinates_norm_le (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (a : I) :
    ‖fun j => (idealModuleIntegerCoordinates K I hI a j : ℝ)‖ ≤
      idealModuleIntegerCoordinateConstant K I hI * ‖mixedEmbedding K (a.val : K)‖ := by
  rw [idealModuleIntegerCoordinates_real_eq]
  have h := (mixedEmbedding.fractionalIdealLatticeBasis K
    (integralIdealFractionalUnit I hI)).equivFunL.toContinuousLinearMap.le_opNorm
      (mixedEmbedding K (a.val : K))
  apply h.trans
  simp only [idealModuleIntegerCoordinateConstant, add_mul, one_mul]
  nlinarith [norm_nonneg (mixedEmbedding K (a.val : K))]

theorem idealModuleTrace_pairing_eq_sum_rat (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (a : I) (α : K) :
    Algebra.trace ℚ K (α * (a.val : K)) =
      ∑ j, (idealModuleIntegerCoordinates K I hI a j : ℚ) *
        Algebra.trace ℚ K (α * basisOfFractionalIdeal K (integralIdealFractionalUnit I hI) j) := by
  rw [idealModuleIntegerCoordinates_expansion K I hI a]
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul]

theorem idealModuleTrace_pairing_eq_sum (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (a : I) (α : K) :
    (Algebra.trace ℚ K (α * (a.val : K)) : ℝ) =
      ∑ j, (idealModuleIntegerCoordinates K I hI a j : ℝ) *
        idealModuleTraceCoordinates K I hI α j := by
  rw [idealModuleTrace_pairing_eq_sum_rat K I hI a α]
  simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast, idealModuleTraceCoordinates]

theorem idealModuleTraceCoordinates_add (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (α β : K) :
    idealModuleTraceCoordinates K I hI (α + β) =
      idealModuleTraceCoordinates K I hI α + idealModuleTraceCoordinates K I hI β := by
  ext j
  simp only [idealModuleTraceCoordinates, add_mul, map_add, Rat.cast_add, Pi.add_apply]

theorem idealModuleTraceCoordinates_sub (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (α β : K) :
    idealModuleTraceCoordinates K I hI (α - β) =
      idealModuleTraceCoordinates K I hI α - idealModuleTraceCoordinates K I hI β := by
  ext j
  simp only [idealModuleTraceCoordinates, sub_mul, map_sub, Rat.cast_sub, Pi.sub_apply]

def idealModuleTraceIntegerLift (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (k : IdealModuleFrequencyIndex K I hI → ℤ) : K :=
  ∑ j, k j • (basisOfFractionalIdeal K (integralIdealFractionalUnit I hI)).traceDual j

theorem idealModuleTraceIntegerLift_coordinates (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (k : IdealModuleFrequencyIndex K I hI → ℤ) :
    idealModuleTraceCoordinates K I hI (idealModuleTraceIntegerLift K I hI k) =
      fun j => (k j : ℝ) := by
  ext j
  simp only [idealModuleTraceCoordinates, idealModuleTraceIntegerLift, Finset.sum_mul,
    smul_mul_assoc, map_sum, map_zsmul, Basis.trace_traceDual_mul]
  simp

theorem idealModuleTraceCoordinates_integral_iff (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (α : K) :
    (∃ k : IdealModuleFrequencyIndex K I hI → ℤ,
      idealModuleTraceCoordinates K I hI α = fun j => (k j : ℝ)) ↔
      α ∈ FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [FractionalIdeal.mem_dual (FractionalIdeal.coeIdeal_ne_zero.mpr hI)]
  constructor
  · rintro ⟨k, hk⟩ y hy
    obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hy
    have hq (j : IdealModuleFrequencyIndex K I hI) :
        Algebra.trace ℚ K (α * basisOfFractionalIdeal K (integralIdealFractionalUnit I hI) j) =
          (k j : ℚ) := by
      have hj := congrFun hk j
      change (Algebra.trace ℚ K
        (α * basisOfFractionalIdeal K (integralIdealFractionalUnit I hI) j) : ℝ) = (k j : ℝ) at hj
      exact_mod_cast hj
    refine ⟨∑ j, idealModuleIntegerCoordinates K I hI ⟨a, ha⟩ j * k j, ?_⟩
    change ((∑ j, idealModuleIntegerCoordinates K I hI ⟨a, ha⟩ j * k j : ℤ) : ℚ) =
      Algebra.trace ℚ K (α * (a : K))
    rw [idealModuleTrace_pairing_eq_sum_rat K I hI ⟨a, ha⟩]
    simp only [hq, Int.cast_sum, Int.cast_mul]
  · intro h
    have hi (j : IdealModuleFrequencyIndex K I hI) :
        ∃ n : ℤ, (n : ℚ) = Algebra.trace ℚ K
          (α * basisOfFractionalIdeal K (integralIdealFractionalUnit I hI) j) := by
      apply h
      rw [basisOfFractionalIdeal_apply]
      exact (fractionalIdealBasis K (integralIdealFractionalUnit I hI).val j).property
    choose k hk using hi
    refine ⟨k, funext fun j => ?_⟩
    change (Algebra.trace ℚ K
      (α * basisOfFractionalIdeal K (integralIdealFractionalUnit I hI) j) : ℝ) = (k j : ℝ)
    exact_mod_cast (hk j).symm

theorem idealModuleTraceIntegerLift_mem_dual (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (k : IdealModuleFrequencyIndex K I hI → ℤ) :
    idealModuleTraceIntegerLift K I hI k ∈
      FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) :=
  (idealModuleTraceCoordinates_integral_iff K I hI _).mp
    ⟨k, idealModuleTraceIntegerLift_coordinates K I hI k⟩

def idealModuleTraceReconstructionConstant (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) : ℝ :=
  1 + ∑ j, ‖mixedEmbedding K
    ((basisOfFractionalIdeal K (integralIdealFractionalUnit I hI)).traceDual j)‖

theorem idealModuleTraceReconstructionConstant_pos (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    0 < idealModuleTraceReconstructionConstant K I hI := by
  unfold idealModuleTraceReconstructionConstant
  positivity

theorem mixedEmbedding_eq_idealModule_trace_coordinate_sum
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (α : K) :
    mixedEmbedding K α = ∑ j, idealModuleTraceCoordinates K I hI α j •
      mixedEmbedding K ((basisOfFractionalIdeal K (integralIdealFractionalUnit I hI)).traceDual j) := by
  conv_lhs => rw [← ((basisOfFractionalIdeal K (integralIdealFractionalUnit I hI)).traceDual).sum_repr α]
  simp only [map_sum, map_rat_smul, Basis.traceDual_repr_apply,
    Algebra.traceForm_apply, idealModuleTraceCoordinates]
  apply Finset.sum_congr rfl
  intro j _
  exact ratCast_smul_eq ℚ ℝ _ _

theorem mixedEmbedding_norm_le_idealModule_trace_coordinates
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (α : K) :
    ‖mixedEmbedding K α‖ ≤ idealModuleTraceReconstructionConstant K I hI *
      ‖idealModuleTraceCoordinates K I hI α‖ := by
  rw [mixedEmbedding_eq_idealModule_trace_coordinate_sum K I hI α]
  calc
    ‖∑ j, idealModuleTraceCoordinates K I hI α j • mixedEmbedding K
        ((basisOfFractionalIdeal K (integralIdealFractionalUnit I hI)).traceDual j)‖ ≤
      ∑ j, ‖idealModuleTraceCoordinates K I hI α j • mixedEmbedding K
        ((basisOfFractionalIdeal K (integralIdealFractionalUnit I hI)).traceDual j)‖ := norm_sum_le _ _
    _ = ∑ j, ‖idealModuleTraceCoordinates K I hI α j‖ * ‖mixedEmbedding K
        ((basisOfFractionalIdeal K (integralIdealFractionalUnit I hI)).traceDual j)‖ := by
      simp only [norm_smul]
    _ ≤ ∑ j, ‖idealModuleTraceCoordinates K I hI α‖ * ‖mixedEmbedding K
        ((basisOfFractionalIdeal K (integralIdealFractionalUnit I hI)).traceDual j)‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (norm_le_pi_norm (idealModuleTraceCoordinates K I hI α) j)
        (norm_nonneg _)
    _ ≤ idealModuleTraceReconstructionConstant K I hI * ‖idealModuleTraceCoordinates K I hI α‖ := by
      rw [← Finset.mul_sum]
      simp only [idealModuleTraceReconstructionConstant, add_mul, one_mul]
      nlinarith [norm_nonneg (idealModuleTraceCoordinates K I hI α)]

def idealModuleLabelCoordinates (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (ℓ : IdealFrequencyLabel K) :
    IdealModuleFrequencyIndex K I hI → ℝ :=
  idealModuleTraceCoordinates K I hI (idealModuleFrequencyLabelValue K I hI ℓ)

def idealModuleCoordinateSeparationRadius (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (U : ℝ) : ℝ :=
  (1 / (|(NumberField.discr K : ℝ)| * (Ideal.absNorm I : ℝ) * U ^ 2)) ^
      (Module.finrank ℚ K : ℝ)⁻¹ / idealModuleTraceReconstructionConstant K I hI

theorem idealModuleCoordinateSeparationRadius_pos (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    {U : ℝ} (hU : 0 < U) : 0 < idealModuleCoordinateSeparationRadius K I hI U := by
  have hD : 0 < |(NumberField.discr K : ℝ)| := abs_pos.mpr (by
    exact_mod_cast NumberField.discr_ne_zero K)
  have hIN : 0 < (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero ((Ideal.absNorm_eq_zero_iff).not.mpr hI)
  exact div_pos
    (Real.rpow_pos_of_pos (one_div_pos.mpr (mul_pos (mul_pos hD hIN) (sq_pos_of_pos hU))) _)
    (idealModuleTraceReconstructionConstant_pos K I hI)

theorem idealModuleLabel_coordinates_separation (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    {ℓ ℓ' : IdealFrequencyLabel K} (hne : ℓ ≠ ℓ') (k : IdealModuleFrequencyIndex K I hI → ℤ)
    {U : ℝ} (hℓU : (Ideal.absNorm ℓ.1.val : ℝ) ≤ U) (hℓ'U : (Ideal.absNorm ℓ'.1.val : ℝ) ≤ U) :
    idealModuleCoordinateSeparationRadius K I hI U ≤
      ‖idealModuleLabelCoordinates K I hI ℓ - idealModuleLabelCoordinates K I hI ℓ' +
        fun j => (k j : ℝ)‖ := by
  have hs := idealModuleFrequencyLabel_mixed_separation_norm_cutoff K I hI hne
    (idealModuleTraceIntegerLift_mem_dual K I hI k) hℓU hℓ'U
  have hb := mixedEmbedding_norm_le_idealModule_trace_coordinates K I hI
    (idealModuleFrequencyLabelValue K I hI ℓ - idealModuleFrequencyLabelValue K I hI ℓ' +
      idealModuleTraceIntegerLift K I hI k)
  rw [idealModuleTraceCoordinates_add, idealModuleTraceCoordinates_sub,
    idealModuleTraceIntegerLift_coordinates] at hb
  have hpow := hs.trans (pow_le_pow_left₀ (norm_nonneg _) hb (Module.finrank ℚ K))
  have hn : Module.finrank ℚ K ≠ 0 := (Module.finrank_pos : 0 < Module.finrank ℚ K).ne'
  have hroot := Real.rpow_le_rpow (by positivity :
      0 ≤ 1 / (|(NumberField.discr K : ℝ)| * (Ideal.absNorm I : ℝ) * U ^ 2)) hpow
    (inv_nonneg.mpr (Nat.cast_nonneg (Module.finrank ℚ K)))
  rw [Real.pow_rpow_inv_natCast
    (mul_nonneg (idealModuleTraceReconstructionConstant_pos K I hI).le (norm_nonneg _)) hn] at hroot
  exact (div_le_iff₀ (idealModuleTraceReconstructionConstant_pos K I hI)).mpr
    (by simpa only [idealModuleLabelCoordinates, mul_comm] using hroot)

end
end ArtinMatthews.VaryingKummerAnalytic

module

public import ArtinMatthews.VaryingKummerAnalyticMixedTraceDualNormIdeal
public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindCompletion
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Convex.Contractible


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine trace-dual permutation of ideal classes and representative
independence of the entire normalized ideal xi functions. -/
noncomputable section
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField Set
open scoped NumberField nonZeroDivisors Classical BigOperators Topology

variable (K : Type*) [Field K] [NumberField K]

/-- The trace-dual operation as an identity of actual fractional-ideal units. -/
theorem mixedTraceDualIdeal_eq_mul_inv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    mixedTraceDualIdeal K I = mixedTraceDualIdeal K 1 * I⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_inv_eq_inv_val]
  change FractionalIdeal.dual ℤ ℚ I.1 =
    FractionalIdeal.dual ℤ ℚ 1 * I.1⁻¹
  exact FractionalIdeal.dual_eq_mul_inv ℤ ℚ I.1

/-- Trace duality acts on ideal classes by codifferent times inverse class. -/
theorem mixedTraceDualIdeal_class (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ClassGroup.mk K (mixedTraceDualIdeal K I) =
      ClassGroup.mk K (mixedTraceDualIdeal K 1) * (ClassGroup.mk K I)⁻¹ := by
  rw [mixedTraceDualIdeal_eq_mul_inv, map_mul, map_inv]

/-- The actual trace-dual class permutation is an involution. -/
def mixedTraceDualClassEquiv : ClassGroup (𝓞 K) ≃ ClassGroup (𝓞 K) where
  toFun c := ClassGroup.mk K (mixedTraceDualIdeal K 1) * c⁻¹
  invFun c := ClassGroup.mk K (mixedTraceDualIdeal K 1) * c⁻¹
  left_inv c := by simp [mul_comm, mul_left_comm]
  right_inv c := by simp [mul_comm, mul_left_comm]

@[simp] theorem mixedTraceDualClassEquiv_apply (c : ClassGroup (𝓞 K)) :
    mixedTraceDualClassEquiv K c =
      ClassGroup.mk K (mixedTraceDualIdeal K 1) * c⁻¹ := rfl

theorem mixedTraceDual_classRepresentative (c : ClassGroup (𝓞 K)) :
    ClassGroup.mk K (mixedTraceDualIdeal K (classRepresentative K c)) =
      mixedTraceDualClassEquiv K c := by
  rw [mixedTraceDualIdeal_class, classRepresentative_spec]
  rfl

/-- The actual partial ideal Dirichlet series depends only on the ideal class. -/
theorem mixedPartialDedekindDirichlet_eq_of_class_eq
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hclass : ClassGroup.mk K I = ClassGroup.mk K J) (s : ℂ) :
    mixedPartialDedekindDirichlet K I s = mixedPartialDedekindDirichlet K J s := by
  let e : integralIdealClassFiber I ≃ integralIdealClassFiber J :=
    Equiv.subtypeEquivRight (fun L => by
      rw [hclass])
  exact e.tsum_eq (fun L : integralIdealClassFiber J =>
    ((FractionalIdeal.absNorm L.1.val : ℝ) : ℂ) ^ (-s))

/-- Normalize the actual ideal xi by its ideal norm to remove the representative. -/
def mixedNormalizedIdealXi (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) : ℂ :=
  ((FractionalIdeal.absNorm I.1 : ℝ) : ℂ)^s * mixedIdealUnitXi K I s

theorem mixedNormalizedIdealXi_entire (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Differentiable ℂ (mixedNormalizedIdealXi K I) := by
  exact (Differentiable.const_cpow differentiable_id
    (Or.inl (Complex.ofReal_ne_zero.mpr (fractionalIdeal_absNorm_pos I).ne'))).mul
    (mixedIdealUnitXi_entire K I)

/-- The entire normalized xi depends only on the ideal class. Equality is first
proved on the convergent half-plane, then continued by the identity theorem. -/
theorem mixedNormalizedIdealXi_eq_of_class_eq
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hclass : ClassGroup.mk K I = ClassGroup.mk K J) :
    mixedNormalizedIdealXi K I = mixedNormalizedIdealXi K J := by
  apply ((mixedNormalizedIdealXi_entire K I).differentiableOn.analyticOnNhd
    isOpen_univ).eq_of_eventuallyEq
      ((mixedNormalizedIdealXi_entire K J).differentiableOn.analyticOnNhd isOpen_univ)
      (z₀ := (2 : ℂ))
  have h2 : (1 : ℝ) < (2 : ℂ).re := by norm_num
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h2] with s hs
  unfold mixedNormalizedIdealXi
  rw [mixedIdealUnitXi_normalized K hs I, mixedIdealUnitXi_normalized K hs J,
    mixedPartialDedekindDirichlet_eq_of_class_eq K I J hclass]

/-- Replacing a representative by the actual trace dual does not alter the
finite normalized class sum, at any complex argument. -/
theorem mixedNormalizedIdealXi_traceDual_class_sum (s : ℂ) :
    (∑ c : ClassGroup (𝓞 K),
      mixedNormalizedIdealXi K (mixedTraceDualIdeal K (classRepresentative K c)) s) =
    ∑ c : ClassGroup (𝓞 K), mixedNormalizedIdealXi K (classRepresentative K c) s := by
  calc
    _ = ∑ c : ClassGroup (𝓞 K),
        mixedNormalizedIdealXi K (classRepresentative K (mixedTraceDualClassEquiv K c)) s := by
      apply Finset.sum_congr rfl
      intro c _
      exact congrFun (mixedNormalizedIdealXi_eq_of_class_eq K _ _
        ((mixedTraceDual_classRepresentative K c).trans
          (classRepresentative_spec K (mixedTraceDualClassEquiv K c)).symm)) s
    _ = _ := (mixedTraceDualClassEquiv K).sum_comp
      (fun c : ClassGroup (𝓞 K) => mixedNormalizedIdealXi K (classRepresentative K c) s)

/-- The same class reindexing in the literal norm-times-xi expression used by
the whole-field functional equation. -/
theorem mixedIdealUnitXi_traceDual_normalized_class_sum (s : ℂ) :
    (∑ c : ClassGroup (𝓞 K),
      ((FractionalIdeal.absNorm (mixedTraceDualIdeal K (classRepresentative K c)).1 : ℝ) : ℂ)^s *
        mixedIdealUnitXi K (mixedTraceDualIdeal K (classRepresentative K c)) s) =
    ∑ c : ClassGroup (𝓞 K),
      ((FractionalIdeal.absNorm (classRepresentative K c).1 : ℝ) : ℂ)^s *
        mixedIdealUnitXi K (classRepresentative K c) s :=
  mixedNormalizedIdealXi_traceDual_class_sum K s

end ArtinMatthews.VaryingKummerAnalytic

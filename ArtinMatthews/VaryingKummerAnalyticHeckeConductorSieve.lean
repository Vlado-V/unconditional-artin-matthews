module

public import ArtinMatthews.VaryingKummerAnalyticIdealModuleBalancedSieveScale
public import ArtinMatthews.VaryingKummerAnalyticRayIdealClassSeries


set_option backward.privateInPublic true
@[expose] public section

/-! The general-field conductor sieve for actual ideal-ray character
coefficients. The fixed ideal-class scalar is constructed from the genuine
principal law and has norm one. Residue-fiber multiplicities are retained
explicitly, so no injectivity of global characters into residue characters
is silently assumed. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal OAI.SevenEighths.FiniteFourier
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section

namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)

theorem exists_fixedIdeal_balanced_coefficient
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ∃ κ : ℂ, ‖κ‖ = 1 ∧
      ∀ J : integralIdealClassFiber (integralIdealFractionalUnit I hI),
        ψ.coefficient ⟨J.val,J.property.1⟩ = κ * ψ.residue
          (idealResidueCoordinate I M hI hM (idealModuleBalancedElement K I hI J)) := by
  obtain ⟨κ,hκ,H⟩ := ψ.exists_fixedIdeal_coefficient_residue hM I hI
  refine ⟨κ,hκ,fun J => ?_⟩
  let a := idealModuleIntegerElement K I hI (idealElementRepresentative _ J)
  have ha : (a:𝓞 K) ≠ 0 := by
    rw [show (a:𝓞 K) = idealIntegerElement I hI (idealElementRepresentative _ J) from
      idealModuleIntegerElement_eq_integer I hI _]
    exact EvenRayCharacter.generator_integer_ne_zero I hI J
  have hprod : Ideal.span {(a:𝓞 K)} = I * EvenRayCharacter.underlyingIdeal ⟨J.val,J.property.1⟩ := by
    rw [show (a:𝓞 K) = idealIntegerElement I hI (idealElementRepresentative _ J) from
      idealModuleIntegerElement_eq_integer I hI _]
    exact EvenRayCharacter.generator_principal_product I hI J
  have HC := H (EvenRayCharacter.underlyingIdeal ⟨J.val,J.property.1⟩)
    (EvenRayCharacter.underlyingIdeal_ne_bot _) a ha hprod
  rw [EvenRayCharacter.underlyingIdeal_unit ⟨J.val,J.property.1⟩] at HC
  change ψ.coefficient ⟨J.val,J.property.1⟩ =
    κ * idealModuleResidueCoefficient I M hI hM ψ.residue J at HC
  have HB := idealModuleResidueCoefficient_eq_of_generator I M hI hM ψ.residue
    ψ.residue_unit (idealModuleBalancedRepresentative K I hI J)
  rw [idealModuleBalancedRepresentative_spec] at HB
  rw [HC,HB]
  rfl

def idealClassHeckePolynomial (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (B : Finset (integralIdealClassFiber (integralIdealFractionalUnit I hI)))
    (v : integralIdealClassFiber (integralIdealFractionalUnit I hI) → ℂ) : ℂ :=
  ∑ J ∈ B, v J * ψ.coefficient ⟨J.val,J.property.1⟩

theorem idealClassHeckePolynomial_norm_eq_residue
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (B : Finset (integralIdealClassFiber (integralIdealFractionalUnit I hI)))
    (v : integralIdealClassFiber (integralIdealFractionalUnit I hI) → ℂ) :
    ‖ψ.idealClassHeckePolynomial I hI B v‖ =
      ‖∑ J ∈ B, v J * ψ.residue
        (idealResidueCoordinate I M hI hM (idealModuleBalancedElement K I hI J))‖ := by
  obtain ⟨κ,hκ,H⟩ := ψ.exists_fixedIdeal_balanced_coefficient hM I hI
  have he : ψ.idealClassHeckePolynomial I hI B v = κ *
      ∑ J ∈ B, v J * ψ.residue
        (idealResidueCoordinate I M hI hM (idealModuleBalancedElement K I hI J)) := by
    unfold idealClassHeckePolynomial
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro J _
    rw [H J]
    ring
  rw [he,norm_mul,hκ,one_mul]

end EvenIdealRayCharacter

private theorem sum_comp_le_fiber_bound {ι κ : Type*} [DecidableEq κ]
    (A : Finset ι) (f : ι → κ) (g : κ → ℝ) (r : ℕ)
    (hg : ∀ y ∈ A.image f, 0 ≤ g y)
    (hr : ∀ y ∈ A.image f, (A.filter fun x => f x = y).card ≤ r) :
    (∑ x ∈ A, g (f x)) ≤ (r:ℝ) * ∑ y ∈ A.image f, g y := by
  have he : (∑ y ∈ A.image f, ((A.filter fun x => f x = y).card:ℝ) * g y) =
      ∑ x ∈ A, g (f x) := by
    simpa only [Finset.sum_const,nsmul_eq_mul] using
      (Finset.sum_fiberwise_of_maps_to' (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩) g)
  rw [← he,Finset.mul_sum]
  exact Finset.sum_le_sum fun y hy =>
    mul_le_mul_of_nonneg_right (by exact_mod_cast hr y hy) (hg y hy)

variable (K : Type*) [Field K] [NumberField K]

def heckeResidueMultiplicity {M : Ideal (𝓞 K)}
    (A : Finset (EvenIdealRayCharacter K M)) (χ : MulChar ((𝓞 K) ⧸ M) ℂ) : ℕ :=
  (A.filter fun ψ => ψ.residue = χ).card

def heckeConductorMultiplicityBound (T : Finset (IdealConductorModulus K))
    (A : ∀ M : IdealConductorModulus K, Finset (EvenIdealRayCharacter K M.val)) : ℕ :=
  T.sup fun M => (A M).sup fun ψ => heckeResidueMultiplicity K (A M) ψ.residue

theorem heckeResidueMultiplicity_le_bound (T : Finset (IdealConductorModulus K))
    (A : ∀ M : IdealConductorModulus K, Finset (EvenIdealRayCharacter K M.val))
    (M : IdealConductorModulus K) (hM : M ∈ T)
    (χ : MulChar ((𝓞 K) ⧸ M.val) ℂ) (hχ : χ ∈ (A M).image (fun ψ => ψ.residue)) :
    heckeResidueMultiplicity K (A M) χ ≤ heckeConductorMultiplicityBound K T A := by
  obtain ⟨ψ,hψ,rfl⟩ := Finset.mem_image.mp hχ
  exact (Finset.le_sup (f := fun φ => heckeResidueMultiplicity K (A M) φ.residue) hψ).trans
    (Finset.le_sup (f := fun N => (A N).sup fun φ =>
      heckeResidueMultiplicity K (A N) φ.residue) hM)

/-- Genuine Hecke coefficients satisfy the conductor sieve once the finite
residue fibers are bounded. Only this cardinality condition is supplied;
the coefficient transport and all balanced lattice estimates are proved. -/
theorem actualHeckeClass_conductor_sieve_of_fiber_bound
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) {U X : ℝ} (hU : 1 ≤ U) (hX : 1 ≤ X)
    (T : Finset (IdealConductorModulus K))
    (hT : ∀ M ∈ T, (Ideal.absNorm M.val:ℝ) ≤ U)
    (A : ∀ M : IdealConductorModulus K, Finset (EvenIdealRayCharacter K M.val))
    (hA : ∀ M ∈ T, ∀ ψ ∈ A M, IsPrimitiveOnIdeals ψ.residue)
    (r : ℕ) (hr : ∀ M ∈ T, ∀ χ ∈ (A M).image (fun ψ => ψ.residue),
      heckeResidueMultiplicity K (A M) χ ≤ r)
    (B : Finset (integralIdealClassFiber (integralIdealFractionalUnit I hI)))
    (hB : ∀ J ∈ B, (FractionalIdeal.absNorm J.val.val:ℝ) ≤ X)
    (v : integralIdealClassFiber (integralIdealFractionalUnit I hI) → ℂ) :
    (∑ M ∈ T, ∑ ψ ∈ A M, ‖ψ.idealClassHeckePolynomial I hI B v‖^2) ≤
      ((r:ℝ) * idealModuleBalancedSieveConstant K I hI * (X+U^2)) * ∑ J ∈ B, ‖v J‖^2 := by
  let S := fun M : IdealConductorModulus K => (A M).image (fun ψ => ψ.residue)
  have hS : ∀ M ∈ T, ∀ χ ∈ S M, IsPrimitiveOnIdeals χ := by
    intro M hM χ hχ
    obtain ⟨ψ,hψ,rfl⟩ := Finset.mem_image.mp hχ
    exact hA M hM ψ hψ
  have hlocal (M : IdealConductorModulus K) (hM : M ∈ T) :
      (∑ ψ ∈ A M, ‖ψ.idealClassHeckePolynomial I hI B v‖^2) ≤
        (r:ℝ) * ∑ χ ∈ S M, ‖∑ J ∈ B, v J * χ
          (idealResidueCoordinate I M.val hI M.property (idealModuleBalancedElement K I hI J))‖^2 := by
    simp_rw [EvenIdealRayCharacter.idealClassHeckePolynomial_norm_eq_residue _ M.property]
    exact sum_comp_le_fiber_bound (A M) (fun ψ => ψ.residue)
      (fun χ => ‖∑ J ∈ B, v J * χ
        (idealResidueCoordinate I M.val hI M.property (idealModuleBalancedElement K I hI J))‖^2)
      r (fun _ _ => sq_nonneg _) (hr M hM)
  calc
    _ ≤ ∑ M ∈ T, (r:ℝ) * ∑ χ ∈ S M, ‖∑ J ∈ B, v J * χ
        (idealResidueCoordinate I M.val hI M.property (idealModuleBalancedElement K I hI J))‖^2 :=
      Finset.sum_le_sum hlocal
    _ = (r:ℝ) * ∑ M ∈ T, ∑ χ ∈ S M, ‖∑ J ∈ B, v J * χ
        (idealResidueCoordinate I M.val hI M.property (idealModuleBalancedElement K I hI J))‖^2 :=
      (Finset.mul_sum ..).symm
    _ ≤ (r:ℝ) * ((idealModuleBalancedSieveConstant K I hI * (X+U^2)) * ∑ J ∈ B, ‖v J‖^2) :=
      mul_le_mul_of_nonneg_left
        (idealModule_unweighted_conductor_sieve_norm_scale K I hI hU hX T hT S hS B hB v)
        (Nat.cast_nonneg r)
    _ = _ := by ring

/-- No residue-injectivity assumption is made: the exact finite-family
multiplicity is retained in the bound. In particular it is never replaced
silently by one when distinct class-group twists share the same residue. -/
theorem actualHeckeClass_conductor_sieve
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) {U X : ℝ} (hU : 1 ≤ U) (hX : 1 ≤ X)
    (T : Finset (IdealConductorModulus K))
    (hT : ∀ M ∈ T, (Ideal.absNorm M.val:ℝ) ≤ U)
    (A : ∀ M : IdealConductorModulus K, Finset (EvenIdealRayCharacter K M.val))
    (hA : ∀ M ∈ T, ∀ ψ ∈ A M, IsPrimitiveOnIdeals ψ.residue)
    (B : Finset (integralIdealClassFiber (integralIdealFractionalUnit I hI)))
    (hB : ∀ J ∈ B, (FractionalIdeal.absNorm J.val.val:ℝ) ≤ X)
    (v : integralIdealClassFiber (integralIdealFractionalUnit I hI) → ℂ) :
    (∑ M ∈ T, ∑ ψ ∈ A M, ‖ψ.idealClassHeckePolynomial I hI B v‖^2) ≤
      ((heckeConductorMultiplicityBound K T A:ℝ) * idealModuleBalancedSieveConstant K I hI *
        (X+U^2)) * ∑ J ∈ B, ‖v J‖^2 :=
  actualHeckeClass_conductor_sieve_of_fiber_bound K I hI hU hX T hT A hA
    (heckeConductorMultiplicityBound K T A) (heckeResidueMultiplicity_le_bound K T A) B hB v

theorem actualHeckeClass_conductor_sieve_of_residue_injective
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) {U X : ℝ} (hU : 1 ≤ U) (hX : 1 ≤ X)
    (T : Finset (IdealConductorModulus K))
    (hT : ∀ M ∈ T, (Ideal.absNorm M.val:ℝ) ≤ U)
    (A : ∀ M : IdealConductorModulus K, Finset (EvenIdealRayCharacter K M.val))
    (hA : ∀ M ∈ T, ∀ ψ ∈ A M, IsPrimitiveOnIdeals ψ.residue)
    (hinj : ∀ M ∈ T, Set.InjOn (fun ψ : EvenIdealRayCharacter K M.val => ψ.residue) (A M))
    (B : Finset (integralIdealClassFiber (integralIdealFractionalUnit I hI)))
    (hB : ∀ J ∈ B, (FractionalIdeal.absNorm J.val.val:ℝ) ≤ X)
    (v : integralIdealClassFiber (integralIdealFractionalUnit I hI) → ℂ) :
    (∑ M ∈ T, ∑ ψ ∈ A M, ‖ψ.idealClassHeckePolynomial I hI B v‖^2) ≤
      (idealModuleBalancedSieveConstant K I hI * (X+U^2)) * ∑ J ∈ B, ‖v J‖^2 := by
  have hr : ∀ M ∈ T, ∀ χ ∈ (A M).image (fun ψ => ψ.residue),
      heckeResidueMultiplicity K (A M) χ ≤ 1 := by
    intro M hM χ _
    apply Finset.card_le_one.mpr
    intro ψ hψ φ hφ
    exact hinj M hM (Finset.mem_filter.mp hψ).1 (Finset.mem_filter.mp hφ).1
      ((Finset.mem_filter.mp hψ).2.trans (Finset.mem_filter.mp hφ).2.symm)
  simpa only [Nat.cast_one,one_mul] using
    actualHeckeClass_conductor_sieve_of_fiber_bound K I hI hU hX T hT A hA 1 hr B hB v

end
end ArtinMatthews.VaryingKummerAnalytic

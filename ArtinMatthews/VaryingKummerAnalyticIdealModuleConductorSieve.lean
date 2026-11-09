module

public import ArtinMatthews.VaryingKummerAnalyticIdealModuleBalancedSupport
public import ArtinMatthews.VaryingKummerAnalyticIdealModuleAdditiveSieve
public import ArtinMatthews.VaryingKummerAnalyticIdealModuleConductorEnergy
public import ArtinMatthews.VaryingKummerAnalyticIdealGaussFourier


set_option backward.privateInPublic true
@[expose] public section

/-! Actual finite conductor energy on balanced ideal-class support. All
trace phases, injective support embeddings and additive-sieve hypotheses
are discharged. Field and fixed-ideal dependencies are retained explicitly. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal OAI.SevenEighths.FiniteFourier
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

abbrev IdealConductorModulus := {M : Ideal (𝓞 K) // M ≠ ⊥}

local instance conductorQuotient_finite (M : IdealConductorModulus K) :
    Finite ((𝓞 K) ⧸ M.val) := Ring.HasFiniteQuotients.finiteQuotient M.property
local instance conductorQuotient_fintype (M : IdealConductorModulus K) :
    Fintype ((𝓞 K) ⧸ M.val) := Fintype.ofFinite _

def idealModuleConductorLabels (T : Finset (IdealConductorModulus K)) :
    Finset (IdealFrequencyLabel K) := T.sigma fun _ => Finset.univ

def idealModuleConductorWeight (M : IdealConductorModulus K) : ℝ :=
  (Ideal.absNorm M.val : ℝ) / (Nat.card (((𝓞 K) ⧸ M.val)ˣ) : ℝ)

theorem idealModuleConductorWeight_one_le (M : IdealConductorModulus K) :
    1 ≤ idealModuleConductorWeight K M := by
  let : NeZero M.val := ⟨M.property⟩
  have hu : 0 < (Nat.card (((𝓞 K) ⧸ M.val)ˣ) : ℝ) := by
    exact_mod_cast (Nat.card_pos (α := ((𝓞 K) ⧸ M.val)ˣ))
  apply (one_le_div hu).mpr
  have hc : Fintype.card (((𝓞 K) ⧸ M.val)ˣ) ≤ Ideal.absNorm M.val := by
    rw [← idealQuotient_card_eq_absNorm K M.val]
    exact Fintype.card_le_of_injective Units.val Units.val_injective
  rw [Nat.card_eq_fintype_card]
  exact_mod_cast hc

theorem idealModule_conductor_weighted_le_additive_energy {ι : Type*}
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (M : IdealConductorModulus K)
    (B : Finset ι) (n : ι → I) (v : ι → ℂ)
    (S : Finset (MulChar ((𝓞 K) ⧸ M.val) ℂ)) (hS : ∀ χ ∈ S, IsPrimitiveOnIdeals χ) :
    idealModuleConductorWeight K M *
      (∑ χ ∈ S, ‖∑ i ∈ B, v i * χ (idealResidueCoordinate I M.val hI M.property (n i))‖^2) ≤
      ∑ u : ((𝓞 K) ⧸ M.val)ˣ, ‖∑ i ∈ B, v i *
        idealModuleTraceChar K I (idealModuleFrequencyValue K I M.val hI M.property u) (n i)‖^2 := by
  let : NeZero M.val := ⟨M.property⟩
  have H := primitive_character_family_energy B
    (fun i => idealResidueCoordinate I M.val hI M.property (n i)) v S hS
    (idealTraceAddChar K M.val M.property) (idealTraceAddChar_isPrimitive K M.val M.property)
  have he : (Ideal.absNorm M.val : ℝ) *
      (∑ χ ∈ S, ‖∑ i ∈ B, v i * χ (idealResidueCoordinate I M.val hI M.property (n i))‖^2) ≤
      (Nat.card (((𝓞 K) ⧸ M.val)ˣ) : ℝ) *
        ∑ u : ((𝓞 K) ⧸ M.val)ˣ, ‖∑ i ∈ B, v i *
          idealModuleTraceChar K I (idealModuleFrequencyValue K I M.val hI M.property u) (n i)‖^2 := by
    simpa only [idealQuotient_card_eq_absNorm, Nat.card_eq_fintype_card,
      idealModuleFrequencyValue_character, mul_comm] using H
  have hu : 0 < (Nat.card (((𝓞 K) ⧸ M.val)ˣ) : ℝ) := by
    exact_mod_cast (Nat.card_pos (α := ((𝓞 K) ⧸ M.val)ˣ))
  rw [idealModuleConductorWeight, div_mul_eq_mul_div]
  exact (div_le_iff₀ hu).mpr (by simpa only [mul_comm] using he)

def idealModuleConductorSieveBound (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (U X : ℝ) : ℝ :=
  coordinateOptimizedSieveConstant (IdealModuleFrequencyIndex K I hI) *
    ((idealModuleBalancedSupportRadius K I hI X) ^ Module.finrank ℚ K +
      (idealModuleSieveReciprocalRadius K I hI U) ^ Module.finrank ℚ K)

/-- The finite ideal support is embedded injectively into the fixed-I
integer lattice, preserving its literal trace phase and coefficient energy. -/
theorem idealModule_balanced_additive_sieve (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    {U X : ℝ} (hU : 0 < U) (hX : 0 < X) (P : Finset (IdealFrequencyLabel K))
    (hP : ∀ ℓ ∈ P, (Ideal.absNorm ℓ.1.val : ℝ) ≤ U)
    (B : Finset (integralIdealClassFiber (integralIdealFractionalUnit I hI)))
    (hB : ∀ J ∈ B, (FractionalIdeal.absNorm J.val.val : ℝ) ≤ X)
    (v : integralIdealClassFiber (integralIdealFractionalUnit I hI) → ℂ) :
    (∑ ℓ ∈ P, ‖∑ J ∈ B, v J * idealModuleTraceChar K I
      (idealModuleFrequencyLabelValue K I hI ℓ) (idealModuleBalancedElement K I hI J)‖^2) ≤
      idealModuleConductorSieveBound K I hI U X * ∑ J ∈ B, ‖v J‖^2 := by
  classical
  let n := idealModuleBalancedElement K I hI
  let w := Function.extend n v (fun _ => 0)
  have hn := idealModuleBalancedElement_injective K I hI
  have hs : ∀ a ∈ B.image n,
      (∑ j, (idealModuleIntegerCoordinates K I hI a j : ℝ)^2) ≤
        (idealModuleBalancedSupportRadius K I hI X)^2 := by
    intro a ha
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp ha
    exact idealModuleBalancedElement_squared_support K I hI J (hB J hJ)
  have H := idealModule_modular_additive_sieve K I hI hU
    (idealModuleBalancedSupportRadius_pos K I hI hX) P hP (B.image n) hs w
  simpa only [Finset.sum_image hn.injOn, w, hn.extend_apply,
    idealModuleConductorSieveBound, n] using H

/-- The genuine conductor-energy inequality, including the standard
Norm(M)/#(O_K/M)^× weight, on arbitrary finite balanced ideal support. -/
theorem idealModule_weighted_conductor_sieve (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    {U X : ℝ} (hU : 0 < U) (hX : 0 < X) (T : Finset (IdealConductorModulus K))
    (hT : ∀ M ∈ T, (Ideal.absNorm M.val : ℝ) ≤ U)
    (S : ∀ M : IdealConductorModulus K, Finset (MulChar ((𝓞 K) ⧸ M.val) ℂ))
    (hS : ∀ M ∈ T, ∀ χ ∈ S M, IsPrimitiveOnIdeals χ)
    (B : Finset (integralIdealClassFiber (integralIdealFractionalUnit I hI)))
    (hB : ∀ J ∈ B, (FractionalIdeal.absNorm J.val.val : ℝ) ≤ X)
    (v : integralIdealClassFiber (integralIdealFractionalUnit I hI) → ℂ) :
    (∑ M ∈ T, idealModuleConductorWeight K M *
      ∑ χ ∈ S M, ‖∑ J ∈ B, v J * χ
        (idealResidueCoordinate I M.val hI M.property (idealModuleBalancedElement K I hI J))‖^2) ≤
      idealModuleConductorSieveBound K I hI U X * ∑ J ∈ B, ‖v J‖^2 := by
  have hlocal := Finset.sum_le_sum fun M hM =>
    idealModule_conductor_weighted_le_additive_energy K I hI M B
      (idealModuleBalancedElement K I hI) v (S M) (hS M hM)
  have hP : ∀ ℓ ∈ idealModuleConductorLabels K T, (Ideal.absNorm ℓ.1.val : ℝ) ≤ U := by
    intro ℓ hℓ
    exact hT ℓ.1 (Finset.mem_sigma.mp hℓ).1
  apply hlocal.trans
  have H := idealModule_balanced_additive_sieve K I hI hU hX
    (idealModuleConductorLabels K T) hP B hB v
  simpa only [idealModuleConductorLabels, Finset.sum_sigma, idealModuleFrequencyLabelValue] using H

theorem idealModule_unweighted_conductor_sieve (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    {U X : ℝ} (hU : 0 < U) (hX : 0 < X) (T : Finset (IdealConductorModulus K))
    (hT : ∀ M ∈ T, (Ideal.absNorm M.val : ℝ) ≤ U)
    (S : ∀ M : IdealConductorModulus K, Finset (MulChar ((𝓞 K) ⧸ M.val) ℂ))
    (hS : ∀ M ∈ T, ∀ χ ∈ S M, IsPrimitiveOnIdeals χ)
    (B : Finset (integralIdealClassFiber (integralIdealFractionalUnit I hI)))
    (hB : ∀ J ∈ B, (FractionalIdeal.absNorm J.val.val : ℝ) ≤ X)
    (v : integralIdealClassFiber (integralIdealFractionalUnit I hI) → ℂ) :
    (∑ M ∈ T, ∑ χ ∈ S M, ‖∑ J ∈ B, v J * χ
      (idealResidueCoordinate I M.val hI M.property (idealModuleBalancedElement K I hI J))‖^2) ≤
      idealModuleConductorSieveBound K I hI U X * ∑ J ∈ B, ‖v J‖^2 := by
  apply (Finset.sum_le_sum fun M _ => ?_).trans
    (idealModule_weighted_conductor_sieve K I hI hU hX T hT S hS B hB v)
  exact le_mul_of_one_le_left (Finset.sum_nonneg fun χ _ => sq_nonneg _)
    (idealModuleConductorWeight_one_le K M)

end
end ArtinMatthews.VaryingKummerAnalytic

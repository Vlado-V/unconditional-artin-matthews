module

public import ArtinMatthews.SourceKPRetainedReflectedClassMultiplier
public import ArtinMatthews.SourceKPReflectedC1Pointwise
public import ArtinMatthews.SourceKPAdelicOutgoingRetainedDiagonalPhase
public import ArtinMatthews.SourceKPAdelicUnitNorm


set_option backward.privateInPublic true
@[expose] public section

/-! After principal frequency dilation the allowed-class gate, the
Weyl phase, and the retained diagonal phase are one function on the
actual sixth-power class labels. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain ClassFieldTheory AllowedGenerators SourcePhysical SourceEulerAssembly
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "U" => SWholeUnits K S
local notation "Q" => SWholePowerClasses K 6 S
local notation "L" => SLocalPowerClasses K 6 S
local notation "D" => sWholeDiagonal K S
local notation "cl" => sWholeGlobalClassMap K 6 S
local notation "a₀" => sourceKPSLocalReflectionArgument K S
local notation "r₆" => sourceKPRetainedFiniteSixthClass K S
local notation "q₆" =>
  (QuotientGroup.mk' (MonoidHom.range (powMonoidHom ((6 : ℕ+) : ℕ) : U →* U)) : U →* Q)
local notation "q₃" =>
  (QuotientGroup.mk' (MonoidHom.range (powMonoidHom ((3 : ℕ+) : ℕ) : U →* U)) :
    U →* SWholePowerClasses K 3 S)

private def retainedCube (P : S) :
    PowerClassGroup (P.val.adicCompletion K) 6 →* PowerClassGroup (P.val.adicCompletion K) 3 :=
  powerQuotientMapOfDvd (P.val.adicCompletion K)ˣ 6 3 (by decide)

def sourceKPRetainedNegativeClass (a m : Q) (r : L) : ℂ := by
  let : IsTotallyComplex K := source_isTotallyComplex K hζ
  let e := sWholePowerEquiv K 6 S
  let c := sourceKPRetainedReflectedArgumentClass K hζ S₀ a m r
  let c₃ := sourceReflectionCubeClassMap K S₀
  exact (if (sLocalRingPowerEquiv K 6 S).symm c ∈ chosenB K hζ S₀ then 1 else 0) *
    (sourceKPAdelicCentralComplex K hζ
      (sourceSLocalWeylClassPhase K S hζ (c₃ a) (c₃ (a / e.symm r))) : ℂ) *
    ∏ P : S, (sourceKPAdelicOutgoingRetainedDiagonalPhaseOfClasses K hζ P.val
      (retainedCube K S₀ P (e m P)) (retainedCube K S₀ P (r P)) : ℂ)

theorem sourceKPRetainedNegativeClass_eq (b m : Kˣ) (x : U) :
    let z := D m*x
    sourceKPRetainedNegativeClass K hζ S₀ (cl ((b⁻¹)^2)) (cl m) (r₆ z.2) =
      sourceKPAllowedClassGate K hζ S₀ (a₀ b*x⁻¹) *
        sourceKPReflectedC1WeylPhase K hζ S₀ b z *
        ∏ P : S, (sourceKPTameUniformizerCharacter K hζ P.val
          (sourceKPTraceJacquetFrequencyAt K P.val m) (z.2 P) : ℂ) := by
  let : IsTotallyComplex K := source_isTotallyComplex K hζ
  let z := D m*x
  let a := a₀ b
  let e := sWholePowerEquiv K 6 S
  have ha : cl ((b⁻¹)^2) = q₆ a := rfl
  have hz : e.symm (r₆ z.2) = q₆ z := by
    have he : e (q₆ z) = r₆ z.2 := sWholePowerEquiv_mk K 6 S z
    exact (congrArg e.symm he.symm).trans (e.symm_apply_apply _)
  have hw : sourceReflectionCubeClassMap K S₀ (q₆ a / e.symm (r₆ z.2)) = q₃ (a*z⁻¹) := by
    rw [hz,div_eq_mul_inv,← map_inv (q₆),← map_mul (q₆)]
    rfl
  dsimp only [sourceKPRetainedNegativeClass]
  change (_ : ℂ) = _
  rw [ha,sourceKPRetainedReflectedArgumentClass_eq K hζ S₀ a x m]
  change sourceKPAllowedClassGate K hζ S₀ (a*x⁻¹) * _ * _ = _
  have hw₀ : sourceSLocalWeylClassPhase K S hζ
      (sWholeGlobalClassMap K 3 S ((b⁻¹)^2)) (q₃ (a*z⁻¹)) =
        sourceSLocalWeylPhase K S hζ b (a*z⁻¹) :=
    (sourceSLocalWeylPhase_eq_classPhase K S hζ b (a*z⁻¹)).symm
  rw [hw,← ha,sourceReflectionCubeClassMap_global,hw₀]
  change sourceKPAllowedClassGate K hζ S₀ (a*x⁻¹) *
    sourceKPReflectedC1WeylPhase K hζ S₀ b z * _ =
      sourceKPAllowedClassGate K hζ S₀ (a*x⁻¹) * sourceKPReflectedC1WeylPhase K hζ S₀ b z * _
  congr 1

private theorem retainedDiagonalClass_norm (P : S)
    (u v : PowerClassGroup (P.val.adicCompletion K) 3) :
    ‖(sourceKPAdelicOutgoingRetainedDiagonalPhaseOfClasses K hζ P.val u v : ℂ)‖ = 1 := by
  obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective _ u
  obtain ⟨z,rfl⟩ := QuotientGroup.mk'_surjective _ v
  exact sourceKPAdelicOutgoingRetainedDiagonalPhase_norm K hζ P.val y z

theorem sourceKPRetainedNegativeClass_norm_le (a m : Q) (r : L) :
    ‖sourceKPRetainedNegativeClass K hζ S₀ a m r‖ ≤ 1 := by
  unfold sourceKPRetainedNegativeClass
  dsimp only
  rw [norm_mul,norm_mul,sourceKPAdelicCentralComplex_norm,Complex.norm_prod]
  simp only [retainedDiagonalClass_norm,Finset.prod_const_one,mul_one]
  split <;> simp

end
end ArtinMatthews

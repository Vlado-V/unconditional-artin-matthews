module

public import ArtinMatthews.SourceKPRetainedFiniteClassTensor
public import ArtinMatthews.SourceReflectionWeylClassSelector
public import ArtinMatthews.SourceKPAllowedClassGate
public import ArtinMatthews.SourceKPAdelicExceptionalCharacter


set_option backward.privateInPublic true
@[expose] public section

/-! The actual allowed-class gate and cubic Weyl multiplier depend on
the finite sixth-class tuple after the original frequency dilation. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain AllowedGenerators SourcePhysical SourceEulerAssembly
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "U" => SWholeUnits K S
local notation "U₀" => SFiniteUnits K S
local notation "Q" => SWholePowerClasses K 6 S
local notation "Q₀" => SLocalPowerClasses K 6 S
local notation "Q₃" => SWholePowerClasses K 3 S
local notation "D" => sWholeDiagonal K S
local notation "q₆" =>
  (QuotientGroup.mk' (MonoidHom.range (powMonoidHom ((6 : ℕ+) : ℕ) : U →* U)) : U →* Q)
local notation "cl" => sWholeGlobalClassMap K 6 S
local notation "cl₃" => sWholeGlobalClassMap K 3 S

def sourceKPRetainedReflectedArgumentClass (a m : Q) (r : Q₀) : Q := by
  letI : IsTotallyComplex K := source_isTotallyComplex K hζ
  exact a * m / (sWholePowerEquiv K 6 S).symm r

theorem sourceKPRetainedReflectedArgumentClass_eq (a x : U) (m : Kˣ) :
    sourceKPRetainedReflectedArgumentClass K hζ S₀ (q₆ a) (cl m)
      (sourceKPRetainedFiniteSixthClass K S (D m * x).2) =
      q₆ (a * x⁻¹) := by
  let : IsTotallyComplex K := source_isTotallyComplex K hζ
  let e := sWholePowerEquiv K 6 S
  let qa : Q := q₆ a
  let qm : Q := cl m
  let qx : Q := q₆ x
  let qz : Q := e.symm (sourceKPRetainedFiniteSixthClass K S (D m * x).2)
  have hz : e (q₆ (D m * x)) = sourceKPRetainedFiniteSixthClass K S (D m * x).2 :=
    sWholePowerEquiv_mk K 6 S _
  have hmz : qz = qm * qx := calc
    _ = e.symm (e (q₆ (D m * x))) := congrArg e.symm hz.symm
    _ = q₆ (D m * x) := e.symm_apply_apply _
    _ = _ := map_mul (q₆) (D m) x
  have hax : q₆ (a * x⁻¹) = qa * qx⁻¹ := by
    exact (map_mul (q₆) a x⁻¹).trans (congrArg (fun t : Q => qa * t) (map_inv (q₆) x))
  change qa * qm / qz = _
  calc
    _ = (qa * qm) / (qm * qx) := congrArg (fun t : Q => (qa * qm) / t) hmz
    _ = (qm * qa) / (qm * qx) := congrArg (fun t : Q => t / (qm * qx)) (mul_comm qa qm)
    _ = qa / qx := mul_div_mul_left_eq_div qa qx qm
    _ = _ := (div_eq_mul_inv qa qx).trans hax.symm

/-- The class scalar at fixed classes of the reflection argument, the
frequency, and the inverse squared denominator. -/
def sourceKPRetainedGateWeylClassScalar (a m : Q) (b : Q₃) (r : Q₀) : ℂ :=
  let c := sourceKPRetainedReflectedArgumentClass K hζ S₀ a m r
  (if (sLocalRingPowerEquiv K 6 S).symm c ∈ chosenB K hζ S₀ then 1 else 0) *
    (sourceKPAdelicCentralComplex K hζ
      (sourceSLocalWeylClassPhase K S hζ b (sourceReflectionCubeClassMap K S₀ c)) : ℂ)

theorem sourceKPRetainedGateWeylClassScalar_eq (a x : U) (b m : Kˣ) :
    sourceKPRetainedGateWeylClassScalar K hζ S₀ (q₆ a) (cl m) (cl₃ (b⁻¹ ^ 2))
      (sourceKPRetainedFiniteSixthClass K S (D m * x).2) =
    sourceKPAllowedClassGate K hζ S₀ (a * x⁻¹) *
      (sourceKPAdelicCentralComplex K hζ (sourceSLocalWeylPhase K S hζ b (a * x⁻¹)) : ℂ) := by
  unfold sourceKPRetainedGateWeylClassScalar
  dsimp only
  rw [sourceKPRetainedReflectedArgumentClass_eq, sourceSLocalWeylPhase_eq_classPhase]
  rfl

theorem sourceKPRetainedReflectedClassMultiplier_split (a x : U) (b m : Kˣ) (χ : U₀ →* ℂˣ)
    (V : ∀ P : S, (P.val.adicCompletion K)ˣ → ℂ) :
    sourceKPAllowedClassGate K hζ S₀ (a * x⁻¹) *
      (sourceKPAdelicCentralComplex K hζ (sourceSLocalWeylPhase K S hζ b (a * x⁻¹)) : ℂ) *
      (χ (D m * x).2 : ℂ) * (∏ P : S, V P ((D m * x).2 P)) =
      ∑ r ∈ sourceKPRetainedFiniteSixthClassLabels K hζ S₀,
        sourceKPRetainedGateWeylClassScalar K hζ S₀ (q₆ a) (cl m) (cl₃ (b⁻¹ ^ 2)) r *
          ∏ P : S, sourceKPRetainedLocalClassProfile K P.val
            (sourceKPRetainedFiniteCharacterAt K S χ P) (r P) (V P) ((D m * x).2 P) := by
  rw [← sourceKPRetainedGateWeylClassScalar_eq K hζ S₀ a x b m]
  exact sourceKPRetainedFiniteClassTensor K hζ S₀ _ χ V (D m * x).2

end
end ArtinMatthews

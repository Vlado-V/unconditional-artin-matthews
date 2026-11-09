module

public import ArtinMatthews.SourceReflectionTameWeyl
public import ArtinMatthews.SourceReflectionTameFourier


set_option backward.privateInPublic true
@[expose] public section

/-! The finite Fourier rows are the sums of actual rotated Whittaker
values. The terminal additive phase uses the residue of the unit part
and becomes trivial at positive frequency order. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic StandardAdelic QuadraticWeil
open SIntegerFourier LocalFieldTheory GlobalClassFieldTheory.Reciprocity
open LocalFieldTheory.IsNonarchimedeanLocalField
open scoped NumberField Classical BigOperators ValuativeRel MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "R" => (𝓞 K) ⧸ P.val.asIdeal
local notation "L" => P.val.adicCompletion K
local notation "ν₀" => sourceKPFiniteVal K P.val
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "res₀" => sourceKPLocalUnitResidue K P.val
local notation "χ₀" => reflectionPrimeCharacters K hζ S₀ P
local notation "ψ₀" => localFiniteCharacter K P.val
local notation "φ₀" => sourceJacquetActualPositivePhase K hζ S₀ P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P.val
local notation "D₀" => fun a : Lˣ => l₀ (sourceGL2Diagonal a)
local notation "w₀" => l₀ sourceGL2Weyl
local notation "N₀" => fun x : L => l₀ (sourceGL2Upper x)
local notation "C₀" => sourceReflectionTameFourierCoefficient K hζ S₀ P
local notation "A₀" => sourceReflectionTameActiveFourier K hζ S₀ P

local instance rotationResidueField : Field R :=
  letI : P.val.asIdeal.IsMaximal := P.val.isMaximal
  Ideal.Quotient.field _
local instance rotationAdicRelation : ValuativeRel L := adicRelation K P.val
local instance rotationAdicLocalField : IsNonarchimedeanLocalField L := adicLocalField K P.val
local instance rotationResidueFinite : Finite R := Ring.HasFiniteQuotients.finiteQuotient P.val.ne_bot
local instance rotationResidueFintype : Fintype R := Fintype.ofFinite _

private theorem exists_completed_unit_of_residue (h : Rˣ) :
    ∃ u : Lˣ, ∃ hu : ν₀ (u : L) = 1, res₀ u hu = (h : R) := by
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (h : R)
  have hx₀ : x ∉ P.val.asIdeal :=
    fun hn => Units.ne_zero h (hx.symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr hn))
  let u := Units.map (algebraMap K L).toMonoidHom (primeAvoidingIntegralFieldUnit K P.val x hx₀)
  let hu := sourceKPIntegralUnit_completion_valuation K P.val x hx₀
  refine ⟨u, hu, ?_⟩
  have he : sourceKPLocalUnitInteger K P.val u hu = sourceKPCompletedIntegral K P.val x := by
    apply Subtype.ext
    change algebraMap K L (x : K) = (sourceKPCompletedIntegral K P.val x : L)
    exact (sourceKPCompletedIntegral_val K P.val x).symm
  rw [sourceKPLocalUnitResidue, he, sourceKPCompletedIntegral_residue, hx]

def sourceReflectionTameUnitLift (h : Rˣ) : Lˣ :=
  (exists_completed_unit_of_residue K S₀ P h).choose

theorem sourceReflectionTameUnitLift_valuation (h : Rˣ) :
    ν₀ (sourceReflectionTameUnitLift K S₀ P h : L) = 1 :=
  (exists_completed_unit_of_residue K S₀ P h).choose_spec.choose

theorem sourceReflectionTameUnitLift_residue (h : Rˣ) :
    res₀ (sourceReflectionTameUnitLift K S₀ P h) (sourceReflectionTameUnitLift_valuation K S₀ P h) =
      (h : R) :=
  (exists_completed_unit_of_residue K S₀ P h).choose_spec.choose_spec

theorem sourceReflectionTamePositivePhase_reduction
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (x : sourceJacquetIntegers K P.val) :
    φ₀ (sourceJacquetReduction K P.val x) = ψ₀ ((π₀ : L)⁻¹ * (x : L)) := by
  have hbad : P.val ∉ traceBadPlaces K := fun hp => P.property (hS (Finset.mem_union_left _ hp))
  let hψ := localFiniteCharacter_conductorZero K P.val hbad
  let φ := idealPrimeResidueChar K P.val ψ₀ hψ (π₀ : L) hπ₀
  have he : φ₀ = φ := by
    unfold sourceJacquetActualPositivePhase
    rw [residueSourcePhase_eq_negativeIdeal K (sourceHilbertSeed K S₀) P.val P.property
      (sourceAllowedPrimeGenerator K hζ S₀ P) (sourceAllowedPrimeGenerator_ideal K hζ S₀ P) hbad]
    ext y
    change (φ.mulShift (-1))⁻¹ y = φ y
    rw [AddChar.inv_apply, AddChar.mulShift_apply, neg_one_mul, neg_neg]
  rw [he]
  let E := adicIntegerResidueEquiv K P.val
  change adicPrimeResidueChar K P.val ψ₀ hψ (π₀ : L) hπ₀
    (E (E.symm (integerReduction L x))) = _
  rw [E.apply_symm_apply, integerReduction_apply, adicPrimeResidueChar_apply]

private theorem local_unit_div_val (v u : Lˣ) (hv : ν₀ (v : L) = 1) (hu : ν₀ (u : L) = 1) :
    ν₀ ((v / u : Lˣ) : L) = 1 := by
  rw [Units.val_div_eq_div_val, map_div₀, hv, hu, div_one]

theorem sourceReflectionTameUnitResidue_div (v u : Lˣ)
    (hv : ν₀ (v : L) = 1) (hu : ν₀ (u : L) = 1) :
    res₀ (v / u) (local_unit_div_val K S₀ P v u hv hu) = res₀ v hv / res₀ u hu := by
  let a : 𝒪[L] := ⟨(v / u : Lˣ), (sourceKPLocalUnitInteger K P.val (v / u)
    (local_unit_div_val K S₀ P v u hv hu)).property⟩
  let b : 𝒪[L] := ⟨(u : L), (sourceKPLocalUnitInteger K P.val u hu).property⟩
  let c : 𝒪[L] := ⟨(v : L), (sourceKPLocalUnitInteger K P.val v hv).property⟩
  have hab : a * b = c := by
    apply Subtype.ext
    change ((v / u : Lˣ) : L) * (u : L) = (v : L)
    rw [Units.val_div_eq_div_val, div_mul_cancel₀ _ (Units.ne_zero u)]
  let E := adicIntegerResidueEquiv K P.val
  have hr := congrArg (fun x : 𝒪[L] => E.symm (IsLocalRing.residue 𝒪[L] x)) hab
  change E.symm (IsLocalRing.residue 𝒪[L] (a * b)) = _ at hr
  rw [map_mul, map_mul] at hr
  apply (eq_div_iff (sourceKPLocalUnitResidue_ne_zero K P.val u hu)).mpr
  exact hr

theorem sourceReflectionTameActivePhase
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (e : ℕ) (u v : Lˣ)
    (hu : ν₀ (u : L) = 1) (hv : ν₀ (v : L) = 1) :
    ψ₀ ((π₀ : L) ^ ((e : ℤ) - 1) * (v : L) / (u : L)) =
      φ₀ ((if e = 0 then res₀ v hv else 0) / res₀ u hu) := by
  have ha := local_unit_div_val K S₀ P v u hv hu
  by_cases he : e = 0
  · subst e
    rw [Nat.cast_zero, zero_sub, zpow_neg_one, ite_eq_left rfl,
      ← sourceReflectionTameUnitResidue_div K S₀ P v u hv hu]
    have h := sourceReflectionTamePositivePhase_reduction K hζ S₀ P hS
      (sourceKPLocalUnitInteger K P.val (v / u) ha)
    change φ₀ (res₀ (v / u) ha) = ψ₀ ((π₀ : L)⁻¹ * ((v / u : Lˣ) : L)) at h
    rw [h, Units.val_div_eq_div_val, mul_div_assoc]
  · have harg : (π₀ : L) ^ ((e : ℤ) - 1) * (v : L) / (u : L) =
        ((π₀ ^ ((e : ℤ) - 1) * (v / u) : Lˣ) : L) := by
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_div_eq_div_val, mul_div_assoc]
    have hval : ν₀ (((π₀ ^ ((e : ℤ) - 1) * (v / u) : Lˣ) : L)) ≤ 1 := by
      rw [sourceKPValuationOrder_spec,
        sourceKPValuationOrder_uniformizer_unit K P.val π₀ hπ₀ _ _ ha]
      exact WithZero.exp_le_one_iff.mpr (by omega)
    rw [harg, localFiniteCharacter_integral K P.val _
      ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K P.val).mpr hval),
      ite_eq_right he, zero_div, AddChar.map_zero_eq_one]

variable (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
local notation "W₀" => sourceKPTameCyclicWhittakerValue K hζ S₀ P hS
local notation "u₀" => sourceReflectionTameUnitLift K S₀ P

def sourceReflectionTameRotatedActive (j : Fin 6) (e : ℕ) (v : Lˣ) : ℂ :=
  ∑ h : Rˣ, C₀ j h *
    W₀ (D₀ (π₀ ^ ((e : ℤ) - 2) * v) * w₀ * N₀ ((π₀ ^ (-1 : ℤ) * u₀ h : Lˣ) : L))

theorem sourceReflectionTameRotatedActive_eq (j : Fin 6) (e : ℕ) (v : Lˣ)
    (hv : ν₀ (v : L) = 1) :
    sourceReflectionTameRotatedActive K hζ S₀ P hS j e v =
      A₀ j (if e = 0 then res₀ v hv else 0) *
        (χ₀ (res₀ v hv) ^ (4 : ℤ) * W₀ (D₀ (π₀ ^ (e : ℤ) * v))) := by
  unfold sourceReflectionTameRotatedActive sourceReflectionTameActiveFourier
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _
  let hu := sourceReflectionTameUnitLift_valuation K S₀ P h
  have hχ : χ₀ (h : R) ^ (-2 : ℤ) = ((χ₀⁻¹) ^ (2 : ℕ)) h := by
    change χ₀ (h : R) ^ (-((2 : ℕ) : ℤ)) = _
    rw [zpow_neg, zpow_natCast, MulChar.pow_apply_coe, MulChar.inv_apply_eq_inv', inv_pow]
  rw [sourceKPTameCyclicWhittakerValue_weyl_translate K hζ S₀ P hS (e : ℤ) (u₀ h) v hu hv,
    sourceReflectionTameActivePhase K hζ S₀ P hS e (u₀ h) v hu hv,
    sourceReflectionTameUnitLift_residue K S₀ P h, hχ, div_eq_mul_inv, ← Units.val_inv_eq_inv_val]
  ring

theorem sourceReflectionTameRotatedInactive_eq (j : Fin 6) (t : Lˣ) :
    C₀ j 0 * W₀ (D₀ t * w₀ * N₀ 0) =
      (if j = 0 then 1 - (Ideal.absNorm P.val.asIdeal : ℂ)⁻¹ else 0) * W₀ (D₀ t) := by
  have hz : N₀ 0 = 1 := by
    change l₀ (sourceGL2Upper (0 : L)) = 1
    rw [sourceGL2Upper_zero]
    exact (sourceFiniteKP2ProjectiveMk K hζ P.val).map_one
  rw [hz, mul_one, sourceKPTameCyclicWhittakerValue_weyl_right,
    sourceReflectionTameFourierCoefficient_zero]

end
end ArtinMatthews

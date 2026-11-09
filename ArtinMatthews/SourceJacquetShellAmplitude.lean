module

public import ArtinMatthews.SourceJacquetBallShells
public import ArtinMatthews.SourceKPIntegralResiduePhase
public import Mathlib.MeasureTheory.Function.LocallyIntegrable


set_option backward.privateInPublic true
@[expose] public section

/-! The scalar shell amplitude is the literal finite residue weight
with the actual additive character. Its unit-shell integral equals
the earlier integral over the full integer ball because the residue
weight vanishes on the nonunit ball, even for exponent zero. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical QuadraticWeil VaryingKummerAnalytic
open scoped NumberField SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))
local notation "L" => P.adicCompletion K
local notation "B" => sourceLocalBall K P

theorem sourceJacquetWeight_zero_of_nonunit (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ)
    (x : L) (hx : sourceLocalValuation K P x < 1) : sourceJacquetWeight K P χ x = 0 := by
  have hx0 : x ∈ B 0 := by
    change sourceLocalValuation K P x ≤ WithZero.exp (0 : ℤ)
    rw [WithZero.exp_zero]
    exact hx.le
  rw [sourceLocalBall_zero_eq_integerOpen] at hx0
  let a : sourceJacquetIntegers K P := ⟨x, hx0⟩
  change sourceJacquetWeight K P χ (a : L) = 0
  rw [sourceJacquetWeight_on_integers]
  have h : sourceJacquetReduction K P a = sourceJacquetReduction K P 0 := by
    apply (sourceJacquetReduction_eq_iff K P a 0).mpr
    change ‖x - 0‖ < 1
    rw [sub_zero]
    exact Valued.toNormedField.norm_lt_one_iff.mpr hx
  rw [h, map_zero, MulChar.map_zero]

theorem sourceJacquetShellIntegral_eq_unit_shell (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (t : L) :
    (∫ u in sourceJacquetValuationShell K P 0,
      sourceJacquetWeight K P χ u * localFiniteCharacter K P (-(t * u)) ∂(sourceJacquetHaar K P)) =
      sourceJacquetShellIntegral K P χ t := by
  let f := fun u : L => sourceJacquetWeight K P χ u * localFiniteCharacter K P (-(t * u))
  let μ := sourceJacquetHaar K P
  let : μ.IsAddHaarMeasure := sourceJacquetHaar_isAddHaar K P
  have hcont : Continuous f := (sourceJacquetWeight_locallyConstant K P χ).continuous.mul
    ((localFiniteCharacter_continuous K P).comp (continuous_const.mul continuous_id).neg)
  have hpart : B 0 = B (-1) ∪ sourceJacquetValuationShell K P 0 := by
    simpa using sourceJacquetBall_succ K P (-1)
  have hd : Disjoint (B (-1)) (sourceJacquetValuationShell K P 0) := by
    rw [sourceJacquetValuationShell, zero_sub]
    exact Set.disjoint_left.mpr (fun _ hx hy => hy.2 hx)
  have hShell := sourceJacquetValuationShell_isCompact K P 0
  have hminus := sourceLocalBall_isCompact K P (-1)
  have hz : (∫ u in B (-1), f u ∂μ) = 0 := by
    rw [setIntegral_congr_fun hminus.measurableSet (g := fun _ => 0), integral_zero]
    intro u hu
    have huv : sourceLocalValuation K P u < 1 := (show sourceLocalValuation K P u ≤ WithZero.exp (-1 : ℤ) from hu).trans_lt
      (WithZero.exp_lt_one_iff.mpr (by norm_num))
    change sourceJacquetWeight K P χ u * localFiniteCharacter K P (-(t * u)) = 0
    rw [sourceJacquetWeight_zero_of_nonunit K P χ u huv, zero_mul]
  have h := setIntegral_union hd hShell.measurableSet
    (hcont.continuousOn.integrableOn_compact (μ := μ) hminus)
    (hcont.continuousOn.integrableOn_compact (μ := μ) hShell)
  change (∫ u in sourceJacquetValuationShell K P 0, f u ∂μ) = ∫ u in (sourceJacquetIntegers K P : Set L), f u ∂μ
  rw [← sourceLocalBall_zero_eq_integerOpen K P, hpart, h, hz, zero_add]

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (p : SourceExteriorPrime K S₀)
local notation "k" => p.val.adicCompletion K

def sourceKPTameJacquetShellAmplitude (e l : ℕ) (u : k) : ℂ :=
  sourceJacquetWeight K p.val (sourceJacquetShellCharacter K p.val (reflectionPrimeCharacters K hζ S₀ p) l) u *
    localFiniteCharacter K p.val (-((sourceKPTameExteriorUniformizer K hζ S₀ p : k) ^ ((e : ℤ) - (l : ℤ)) * u))

theorem sourceKPTameJacquetShellAmplitude_continuous (e l : ℕ) :
    Continuous (sourceKPTameJacquetShellAmplitude K hζ S₀ p e l) :=
  (sourceJacquetWeight_locallyConstant K p.val _).continuous.mul
    ((localFiniteCharacter_continuous K p.val).comp (continuous_const.mul continuous_id).neg)

theorem sourceKPTameJacquetShellAmplitude_integral (e l : ℕ) :
    (∫ u in sourceJacquetValuationShell K p.val 0,
      sourceKPTameJacquetShellAmplitude K hζ S₀ p e l u ∂(sourceJacquetHaar K p.val)) =
      sourceJacquetActualShell K hζ S₀ p e l :=
  sourceJacquetShellIntegral_eq_unit_shell K p.val _ _

end
end ArtinMatthews

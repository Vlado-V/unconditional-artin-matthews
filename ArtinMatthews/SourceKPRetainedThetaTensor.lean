module

public import ArtinMatthews.SourceKPRetainedJacquetClassProfile
public import ArtinMatthews.SourceThetaBesselTensorLiteral


set_option backward.privateInPublic true
@[expose] public section

/-! The retained Jacquet coordinates and sixth-class indicators give
actual local factors for a Bessel tensor with exponent (1/3). -/
namespace ArtinMatthews

open NumberField IsDedekindDomain ClassFieldTheory QuadraticWeil
open SourcePhysical SourceReflection VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀

private theorem retainedThetaParameter_pos : 0 < (1 / 6 : ℂ).re := by norm_num

abbrev SourceKPRetainedThetaLabel (I : Type*) :=
  I × (SourceKPAdelicOutgoingRetainedJacquetLabel K hζ retainedThetaParameter_pos S ×
    SLocalPowerClasses K 6 S)

@[instance_reducible] def sourceKPRetainedThetaLabel_fintype (I : Type*) [Fintype I] :
    Fintype (SourceKPRetainedThetaLabel K hζ S₀ I) := by
  let : Fintype (SLocalPowerClasses K 6 S) :=
    ⟨sourceKPRetainedFiniteSixthClassLabels K hζ S₀,
      mem_sourceKPRetainedFiniteSixthClassLabels K hζ S₀⟩
  infer_instance

theorem sourceKPRetainedThetaLabel_finite (I : Type*) [Finite I] :
    Finite (SourceKPRetainedThetaLabel K hζ S₀ I) := by
  let : Fintype I := Fintype.ofFinite I
  let : Fintype (SourceKPRetainedThetaLabel K hζ S₀ I) :=
    sourceKPRetainedThetaLabel_fintype K hζ S₀ I
  infer_instance

variable {I : Type*}
variable (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
variable {J : Ideal (𝓞 K)} (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
variable (rowU : I → exteriorUnitSubgroup (sourceHilbertSet K S₀))
variable (a : I → ∀ P : ↥(sourceHilbertSet K S₀), SourceFiniteKP2Projective K hζ P.val)

local notation "Label" => SourceKPRetainedThetaLabel K hζ S₀ I
local notation "c" => (fun _ : InfinitePlace K => (4 : ℝ) * Real.pi)

def sourceKPRetainedThetaFiniteFactor (d : Label) (P : S) : (P.val.adicCompletion K)ˣ → ℂ := by
  let : IsTotallyComplex K := source_isTotallyComplex K hζ
  let χ := sourceKPRetainedFiniteRowCharacter K hζ S₀ hS η hJ (rowU d.1)
  let V := sourceKPAdelicOutgoingRetainedJacquetBasisDiagonalProfile K hζ P.val
    retainedThetaParameter_pos (d.2.1 P) (a d.1 P)
  exact sourceKPRetainedLocalClassProfile K P.val
    (sourceKPRetainedFiniteCharacterAt K S χ P) (d.2.2 P) V

local notation "F" => sourceKPRetainedThetaFiniteFactor K hζ S₀ hS η hJ rowU a

theorem sourceKPRetainedThetaFiniteFactor_data (d : Label) (P : S) :
    Continuous (F d P) ∧ ∃ n : ℤ, ∃ B : ℝ, 0 < B ∧
      (∀ z : (P.val.adicCompletion K)ˣ, z ∉ sourceLocalMulBall K P.val n → F d P z = 0) ∧
      ∀ z : (P.val.adicCompletion K)ˣ, z ∈ sourceLocalMulBall K P.val 0 →
        ‖F d P z‖ ≤ B * (sourceSheetFiniteNorm S P z) ^ (1 / 3 : ℝ) := by
  let : IsTotallyComplex K := source_isTotallyComplex K hζ
  exact sourceKPRetainedJacquetClassProfile_data K hζ S₀ hS η hJ (rowU d.1) P
    retainedThetaParameter_pos (d.2.1 P) (a d.1 P) (d.2.2 P)

private def retainedThetaFiniteBounds (d : Label) :
    {p : (S → ℤ) × (S → ℝ) //
      (∀ P : S, 0 ≤ p.2 P) ∧
      (∀ (P : S) (z : (P.val.adicCompletion K)ˣ),
        z ∉ sourceLocalMulBall K P.val (p.1 P) → F d P z = 0) ∧
      ∀ (P : S) (z : (P.val.adicCompletion K)ˣ), z ∈ sourceLocalMulBall K P.val 0 →
        ‖F d P z‖ ≤ p.2 P * (sourceSheetFiniteNorm S P z) ^ (1 / 3 : ℝ)} := by
  have h (P : S) := (sourceKPRetainedThetaFiniteFactor_data K hζ S₀ hS η hJ rowU a d P).2
  choose n B hB hSupport hSmall using h
  exact ⟨(n,B), fun P => (hB P).le, hSupport, hSmall⟩

variable (v : InfinitePlace K)

def sourceKPRetainedThetaTensor (d : Label) : SourceThetaRotatedTensor K S hζ v (1 / 3) :=
  let p := retainedThetaFiniteBounds K hζ S₀ hS η hJ rowU a d
  sourceThetaBesselTensor K S hζ v c (fun _ => mul_pos (by norm_num) Real.pi_pos)
    (fun _ => 0) (1 / 3) (by norm_num) (by norm_num) (F d)
    (fun P => (sourceKPRetainedThetaFiniteFactor_data K hζ S₀ hS η hJ rowU a d P).1)
    p.val.1 p.val.2 p.property.1 p.property.2.1 p.property.2.2

local notation "D" => sourceKPRetainedThetaTensor K hζ S₀ hS η hJ rowU a v

theorem sourceKPRetainedThetaTensor_literal (d : Label) (x : SWholeUnits K S) :
    sourceThetaSLocalTensor K S hζ v ((D d).localDeriv 0) (D d).retained x =
      (∏ w : InfinitePlace K, sourceThetaBesselProfile (4 * Real.pi) (sourceSheetArchNorm w (x.1 w))) *
        ∏ P : S, F d P (x.2 P) := by
  unfold sourceKPRetainedThetaTensor
  dsimp only
  rw [sourceThetaBesselTensor_literal]
  congr 1
  apply Finset.prod_congr rfl
  intro w _
  rw [sourceThetaBesselCompletedFactor_eq, zpow_zero, one_mul]

end
end ArtinMatthews

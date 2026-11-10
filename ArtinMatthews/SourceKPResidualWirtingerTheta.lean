module

public import ArtinMatthews.SourceKPCuspWirtingerSeries
public import ArtinMatthews.SourceKPCuspResidualGeneralTheta
public import ArtinMatthews.SourceKPResidualUnitNormalization
public import ArtinMatthews.SourceReflectionAngularIdeal
public import Std.Tactic.BVDecide.Normalize.BitVec


set_option backward.privateInPublic true
@[expose] public section

/-! The literal oriented horizontal derivative cancels the frequency
norm in the archimedean Jacquet profile. -/
namespace ArtinMatthews
open NumberField NumberField.InfinitePlace.Completion SourceArchJacquet SourceReflection AngularLambda VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 12)
local notation "V" => InfinitePlace K
local notation "B" => sourceThetaBesselProfile (4*Real.pi)
local notation "i₂π" => (2 * (Real.pi : ℂ) * Complex.I)

def sourceKPOrientedHorizontal (v : V) : Bool :=
  decide (sourceReflectionAngularInfinityExponent K hζ v = 1)

def sourceKPAllInfinitePlaces : List V := (Finset.univ : Finset V).toList

theorem sourceKPAllInfinitePlaces_nodup : (sourceKPAllInfinitePlaces K).Nodup :=
  Finset.nodup_toList _

theorem sourceKPAllInfinitePlaces_ne_nil : sourceKPAllInfinitePlaces K ≠ [] := by
  intro he
  let v : V := Classical.choice inferInstance
  have hv : v ∈ sourceKPAllInfinitePlaces K := Finset.mem_toList.mpr (Finset.mem_univ v)
  simp [he] at hv

def sourceKPResidualArchDerivativeConstant : ℂ :=
  (i₂π * (sourceArchJacquetConstant : ℂ)) ^ Fintype.card V

theorem sourceKPResidualArchDerivativeConstant_ne_zero :
    sourceKPResidualArchDerivativeConstant K ≠ 0 := by
  unfold sourceKPResidualArchDerivativeConstant
  exact pow_ne_zero _ (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr sourceArchJacquetConstant_ne_zero))

def sourceKPResidualArchAngular (ε : V → Bool) (m : Kˣ) : ℂ :=
  ∏ v : V, complexAngular (v.embedding (m : K)) ^ (if ε v then (-1 : ℤ) else 1)

theorem sourceKPResidualArchAngular_oriented (m : Kˣ) :
    sourceKPResidualArchAngular K (sourceKPOrientedHorizontal K hζ) m =
      ((sourceReflectionAngularField K hζ m)⁻¹ : ℂˣ).val := by
  rw [Units.val_inv_eq_inv_val, sourceReflectionAngularField_place_product K hζ,
    ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro v _
  rcases sourceReflectionAngularInfinityExponent_sign K hζ v with hv | hv
  · simp [sourceKPOrientedHorizontal,hv]
  · simp [sourceKPOrientedHorizontal,hv]

theorem sourceKPCuspRationalComplexUnit_val (m : Kˣ) (v : V) :
    (sourceKPCuspRationalComplexUnit K hζ m v : ℂ) = v.embedding (m : K) := by
  change ringEquivComplexOfIsComplex ((source_isTotallyComplex K hζ).isComplex v)
    (algebraMap K v.Completion (m : K)) = _
  rw [ringEquivComplexOfIsComplex_apply]
  change extensionEmbedding v (((WithAbs.equiv v.1).symm (m : K) : WithAbs v.1) : v.Completion) = _
  rw [extensionEmbedding_coe, RingEquiv.apply_symm_apply]

private theorem sourceKPCuspWirtingerFrequency_polar (ε : Bool) (m : Kˣ) (v : V) (y : ℝ) :
    sourceKPCuspWirtingerFrequency K ε (m : K) v y =
      i₂π * (y : ℂ) * (‖(sourceKPCuspRationalComplexUnit K hζ m v : ℂ)‖ : ℂ) *
        complexAngular (v.embedding (m : K)) ^ (if ε then (-1 : ℤ) else 1) := by
  let z := v.embedding (m : K)
  have hz : z ≠ 0 := map_ne_zero v.embedding |>.mpr m.ne_zero
  have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  rw [sourceKPCuspWirtingerFrequency, sourceKPCuspRationalComplexUnit_val]
  change i₂π * (y : ℂ) * (if ε then star z else z) =
    i₂π * (y : ℂ) * (‖z‖ : ℂ) * complexAngular z ^ (if ε then (-1 : ℤ) else 1)
  cases ε
  · simp only [Bool.false_eq_true,ite_false,zpow_one,complexAngular]
    field_simp
  · simp only [ite_true,zpow_neg_one]
    rw [← complexAngular_conjugate z]
    simp only [complexAngular,norm_star]
    field_simp

theorem sourceKPCuspWirtingerProductFrequency_theta (ε : V → Bool) (m : Kˣ)
    (y : V → ℝ) (hy : ∀ v, 0 < y v) :
    sourceKPCuspWirtingerProductFrequency K ε (sourceKPAllInfinitePlaces K) (m : K) y *
        sourceKPTraceJacquetArchProfile K hζ m (1/6) y =
      sourceKPResidualArchDerivativeConstant K * sourceKPCuspResidualFrequencyScale K hζ m (1/6) *
        sourceKPResidualArchAngular K ε m *
        ∏ v : V, B ((sourceKPCuspRationalHeight K hζ m y v)^2) := by
  let Q : ℂ := ∏ v : V, (‖(sourceKPCuspRationalComplexUnit K hζ m v : ℂ)‖ : ℂ)
  let L : ℂ := sourceKPCuspResidualFrequencyScale K hζ m (1/6)
  let A : ℂ := sourceKPResidualArchAngular K ε m
  let H : ℂ := ∏ v : V, (y v : ℂ)
  let C : ℂ := sourceArchJacquetConstant
  let J : ℂ := sourceKPTraceJacquetArchProfile K hζ m (1/6) y
  let F : ℂ := ∏ v : V, B ((sourceKPCuspRationalHeight K hζ m y v)^2)
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun v _ =>
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (sourceKPCuspRationalComplexUnit K hζ m v).ne_zero))
  have hΘ : H * J = (L/Q) * C^Fintype.card V * F :=
    sourceKPTraceJacquetArchProfile_theta K hζ m y hy
  have hP : sourceKPCuspWirtingerProductFrequency K ε (sourceKPAllInfinitePlaces K) (m : K) y =
      i₂π ^ Fintype.card V * H * Q * A := by
    unfold sourceKPCuspWirtingerProductFrequency sourceKPAllInfinitePlaces
    rw [Finset.prod_map_toList]
    simp_rw [sourceKPCuspWirtingerFrequency_polar K hζ]
    simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,H,Q,A,sourceKPResidualArchAngular,mul_pow]
  rw [hP]
  change i₂π ^ Fintype.card V * H * Q * A * J = (i₂π * C)^Fintype.card V * L * A * F
  calc
    _ = (i₂π ^ Fintype.card V * Q * A) * (H * J) := by ring
    _ = _ := by rw [hΘ,mul_pow]; field_simp [hQ]; ring

theorem sourceKPResidualWirtingerTheta_term (ε : V → Bool) (m : Kˣ)
    (qf : SourceKPFiniteAdeleProjective K hζ) {T : ℝ} (hT : 1 ≤ T)
    (y : V → ℝ) (hy : ∀ v, 0 < y v) :
    sourceKPCuspWirtingerProductFrequency K ε (sourceKPAllInfinitePlaces K) (m : K) y *
        (sourceKPCuspResidualFourierValue K hζ m hT qf * sourceKPTraceJacquetArchProfile K hζ m (1/6) y) =
      sourceKPResidualArchDerivativeConstant K *
        sourceKPCuspResidualFourierValue K hζ 1 hT (sourceKPCuspResidualUnitTranslate K hζ m qf) *
        sourceKPResidualArchAngular K ε m *
        ∏ v : V, B ((sourceKPCuspRationalHeight K hζ m y v)^2) := by
  let c := sourceKPCuspResidualFourierValue K hζ m hT qf
  let A := sourceKPTraceJacquetArchProfile K hζ m (1/6) y
  let J := sourceKPCuspWirtingerProductFrequency K ε (sourceKPAllInfinitePlaces K) (m : K) y
  change J * (c * A) = _
  rw [show J * (c * A) = (J * A) * c by ring]
  dsimp only [J,A,c]
  rw [sourceKPCuspWirtingerProductFrequency_theta K hζ ε m y hy,
    sourceKPCuspResidualFourierValue_unit_translate K hζ m qf hT]
  ring

end
end ArtinMatthews

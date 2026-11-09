module

public import ArtinMatthews.CubicThetaActualCusps
public import ArtinMatthews.ShiftedVoronoiCharacter


set_option backward.privateInPublic true
@[expose] public section

/-! Actual all-cusp vanishing and explicit level arithmetic for the cubic
numerator theta cusp-form construction. -/
noncomputable section
namespace ArtinMatthews

open scoped MatrixGroups Topology Manifold
open Complex UpperHalfPlane ModularForm OnePoint CongruenceSubgroup
open OAI OAI.SevenEighths

/-- An even rational coordinate period containing the actual conductor. -/
def cubicNumeratorThetaPeriod (A : ℤ) : ℕ := 18 * A.natAbs

/-- An explicit level satisfying the finite-adelic lattice conditions. -/
def cubicNumeratorThetaLevel (A : ℤ) : ℕ := 6 * cubicNumeratorThetaPeriod A ^ 2

theorem cubicNumeratorThetaPeriod_ne_zero {A : ℤ} (hA : A ≠ 0) :
    cubicNumeratorThetaPeriod A ≠ 0 := by
  exact mul_ne_zero (by decide) (Int.natAbs_ne_zero.mpr hA)

theorem cubicNumeratorThetaPeriod_even (A : ℤ) :
    2 ∣ cubicNumeratorThetaPeriod A := by
  exact ⟨9 * A.natAbs, by simp [cubicNumeratorThetaPeriod]; ring⟩

theorem cubicNumeratorThetaPeriod_conductor_dvd (A : ℤ) :
    9 * A ∣ (cubicNumeratorThetaPeriod A : ℤ) := by
  change 9 * A ∣ ((18 * A.natAbs : ℕ) : ℤ)
  rw [Nat.cast_mul, Int.natCast_natAbs]
  have ha : A ∣ |A| := (dvd_abs A A).mpr (dvd_refl A)
  obtain ⟨k, hk⟩ := ha
  exact ⟨2 * k, by rw [hk]; ring⟩

theorem cubicNumeratorThetaLevel_ne_zero {A : ℤ} (hA : A ≠ 0) :
    cubicNumeratorThetaLevel A ≠ 0 := by
  exact mul_ne_zero (by decide) (pow_ne_zero _ (cubicNumeratorThetaPeriod_ne_zero hA))

theorem cubicNumeratorThetaLevel_three_dvd (A : ℤ) :
    3 ∣ cubicNumeratorThetaLevel A := by
  exact ⟨2 * cubicNumeratorThetaPeriod A ^ 2,
    by simp [cubicNumeratorThetaLevel]; ring⟩

theorem cubicNumeratorThetaLevel_eq (A : ℤ) :
    cubicNumeratorThetaLevel A = 1944 * A.natAbs ^ 2 := by
  unfold cubicNumeratorThetaLevel cubicNumeratorThetaPeriod
  ring

/-- The already proved rational cusp limits are the native slash-zero
condition at every cusp of the precise theta kernel subgroup. -/
theorem cubicNumeratorHeckeTheta_zeroAt_cusp
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein))
    (N : ℕ) [NeZero N] {c : OnePoint ℝ}
    (hc : IsCusp c (cubicThetaKernel N : Subgroup (GL (Fin 2) ℝ))) :
    c.IsZeroAt (heckeTheta (cubicNumeratorHeckeCharacter A hA)) 1 := by
  have hSL : IsCusp c 𝒮ℒ :=
    (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc
  apply (OnePoint.isZeroAt_iff_forall_SL2Z hSL).mpr
  intro γ _
  change Filter.Tendsto
    (heckeTheta (cubicNumeratorHeckeCharacter A hA) ∣[(1 : ℤ)] γ)
    atImInfty (𝓝 0)
  have he : (heckeTheta (cubicNumeratorHeckeCharacter A hA) ∣[(1 : ℤ)] γ) =
      (fun τ : ℍ => heckeTheta (cubicNumeratorHeckeCharacter A hA) (γ • τ) /
        ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ))) := by
    funext τ
    rw [SL_slash_apply, zpow_neg_one]
    erw [ModularGroup.denom_apply]
    rfl
  rw [he]
  exact tendsto_cubicNumeratorHeckeTheta_cusp A hA hnoncube γ

end ArtinMatthews

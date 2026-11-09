module

public import ArtinMatthews.SourceNarrowPrimitiveBounds
public import ArtinMatthews.SourceRowContinuedEuler


set_option backward.privateInPublic true
@[expose] public section

/-! Bind the narrow-strip estimate and right-hand Euler bounds to the
actual source row. The height degree is fixed by the field, and the
only varying numerator conductor cost is in the literal frequency norm. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic
open scoped NumberField Classical BigOperators nonZeroDivisors
noncomputable section
variable (F : Type) [Field F] [NumberField F]

theorem exists_sourceRayNonprincipalContinued_source06_bound :
    ∃ m : ℕ, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ {N : Ideal (𝓞 F)} (ψ : EvenIdealRayCharacter F N) (hN : N ≠ ⊥)
        (_hnp : ψ.IsNonprincipal) (s : ℂ), (3/1000 : ℝ) ≤ s.re →
        ‖sourceRayNonprincipalContinued F ψ hN s‖ ≤
          C*(N.absNorm : ℝ)^(1/2+ε)*(|s.im|+2)^m := by
  obtain ⟨C, m, hC, h⟩ := exists_sourcePrimitiveContinued_source06_bound F
  refine ⟨m, ?_⟩
  intro ε hε
  obtain ⟨D, hD, hdel⟩ := exists_sourceIdealEulerDeletion_norm_le_subpower F ε hε
  refine ⟨C*D, mul_pos hC hD, ?_⟩
  intro N ψ hN hnp s hs
  let d := sourceRayPrimitiveDatum F ψ hN
  have hnd := ψ.primitiveIdeal_isNonprincipal hN d.modulus.val d.old_le d.character d.agrees hnp
  have hp := h d.character d.modulus.property d.primitive hnd s hs
  have hd := hdel d.character N hN s (by linarith)
  have hq : (d.modulus.val.absNorm : ℝ)^(1/2 : ℝ) ≤ (N.absNorm : ℝ)^(1/2 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr d.norm_le) (by norm_num)
  have hN' : 0 < (N.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hN)
  have hp' := hp.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq hC.le) (by positivity))
  change ‖d.character.primitiveContinued d.modulus.property d.primitive s*
    d.character.idealEulerDeletion N s‖ ≤ _
  rw [norm_mul]
  calc
    _ ≤ (C*(N.absNorm : ℝ)^(1/2 : ℝ)*(|s.im|+2)^m)*(D*(N.absNorm : ℝ)^ε) :=
      mul_le_mul hp' hd (norm_nonneg _) (by positivity)
    _ = (C*D)*((N.absNorm : ℝ)^(1/2 : ℝ)*(N.absNorm : ℝ)^ε)*(|s.im|+2)^m := by ring
    _ = _ := by rw [← Real.rpow_add hN']

variable [IsTotallyComplex F] {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀

theorem exists_sourceRowNumeratorContinued_source06_bound :
    ∃ m : ℕ, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (u : R) (hu : u ≠ 0), (¬ ∃ a : F, a ^ 6 = (u : F)) →
        ∀ s : ℂ, (3/1000 : ℝ) ≤ s.re →
        ‖sourceRowNumeratorContinued F hζ S₀ u hu s‖ ≤ C*
          (sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀ u hu) : ℝ)^(1/2+ε)*
          (|s.im|+2)^m := by
  obtain ⟨m, hb⟩ := exists_sourceRayNonprincipalContinued_source06_bound F
  refine ⟨m, ?_⟩
  intro ε hε
  obtain ⟨C, hC, h⟩ := hb ε hε
  let D := ((sixthKummerFixedIdeal S).absNorm : ℝ)
  have hD : 0 < D := by
    dsimp only [D]
    exact_mod_cast sixthKummerFixedIdeal_absNorm_pos S
  refine ⟨C*D^(1/2+ε), mul_pos hC (Real.rpow_pos_of_pos hD _), ?_⟩
  intro u hu hu₆ s hs
  let v := sourceRowFieldUnit F S₀ u hu
  let N := sixthKummerSharpIdeal S v
  let hN := sixthKummerSharpIdeal_ne_zero S v
  let ψ := sourceRowKummerRay F hζ S₀ u hu
  have hψ : ψ.IsNonprincipal := sourceRowKummerRay_isNonprincipal F hζ S₀ u hu hu₆
  have he : sourceRowNumeratorContinued F hζ S₀ u hu s = sourceRayNonprincipalContinued F ψ hN s :=
    ite_eq_left hψ
  let Q := sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀ u hu)
  have hNQ : (N.absNorm : ℝ) ≤ D*Q := by
    dsimp only [N,v,D,Q]
    exact_mod_cast sourceRowKummerSharpIdeal_norm_le F hζ S₀ u hu
  have hNQ' : (N.absNorm : ℝ)^(1/2+ε) ≤ (D*Q)^(1/2+ε) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hNQ (by positivity)
  rw [he]
  calc
    _ ≤ C*(N.absNorm : ℝ)^(1/2+ε)*(|s.im|+2)^m := h ψ hN hψ s hs
    _ ≤ C*(D*Q)^(1/2+ε)*(|s.im|+2)^m :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNQ' hC.le) (by positivity)
    _ = _ := by rw [Real.mul_rpow hD.le (Nat.cast_nonneg _)]; ring

theorem exists_sourceRowNumeratorContinued_dyadic_bound :
    ∃ m : ℕ, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (u : R) (hu : u ≠ 0), (¬ ∃ a : F, a ^ 6 = (u : F)) →
        ∀ U : ℝ, (sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀ u hu) : ℝ) ≤ 2*U →
        ∀ s : ℂ, (3/1000 : ℝ) ≤ s.re →
        ‖sourceRowNumeratorContinued F hζ S₀ u hu s‖ ≤ C*U^(1/2+ε)*(|s.im|+2)^m := by
  obtain ⟨m, h⟩ := exists_sourceRowNumeratorContinued_source06_bound F hζ S₀
  refine ⟨m, ?_⟩
  intro ε hε
  obtain ⟨C, hC, hb⟩ := h ε hε
  refine ⟨C*(2 : ℝ)^(1/2+ε), mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  intro u hu hu₆ U hU s hs
  have hq : 0 ≤ (sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀ u hu) : ℝ) :=
    Nat.cast_nonneg _
  have hU' : 0 ≤ U := by linarith
  have hp := Real.rpow_le_rpow hq hU (show 0 ≤ 1/2+ε from by positivity)
  apply (hb u hu hu₆ s hs).trans
  calc
    _ ≤ C*(2*U)^(1/2+ε)*(|s.im|+2)^m :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC.le) (by positivity)
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hU']; ring

variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M) (hM : M ≠ ⊥)

theorem sourceRowTwistReciprocal_norm_le_right (u : R) (hu : u ≠ 0) {a : ℝ} (ha : 1 < a)
    {s : ℂ} (hs : a ≤ s.re) :
    ‖sourceRowTwistReciprocal F hζ S₀ u hu η hM s‖ ≤ sourceRayAbsoluteEulerBound F a := by
  rw [sourceRowTwistReciprocal_eq_dirichlet F hζ S₀ u hu η hM s (ha.trans_le hs)]
  exact (sourceRayDirichlet_norm_bounds F (sourceRowKummerTwist F hζ S₀ u hu η hM) ha hs).2

theorem sourceRowNumeratorContinued_norm_le_right (u : R) (hu : u ≠ 0) {a : ℝ} (ha : 1 < a)
    {s : ℂ} (hs : a ≤ s.re) :
    ‖sourceRowNumeratorContinued F hζ S₀ u hu s‖ ≤ sourceRayAbsoluteEulerBound F a := by
  rw [sourceRowNumeratorContinued_eq_dirichlet F hζ S₀ u hu s (ha.trans_le hs)]
  exact (sourceRayDirichlet_norm_bounds F (sourceRowKummerRay F hζ S₀ u hu) ha hs).1

end
end ArtinMatthews.SourceEulerAssembly

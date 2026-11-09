module

public import ArtinMatthews.SourceRowTwistGoodFamily


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine old-conductor budget on a dyad is a fixed multiple of
the frequency bound. This transports the exceptional count and the
analytic box to the manuscript's dyadic parameter. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic
open scoped NumberField Classical BigOperators nonZeroDivisors
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀

def sourceRowTwistDyadicConductorScale (M : Ideal (𝓞 F)) : ℝ :=
  2*(M.absNorm : ℝ)*(sixthKummerFixedIdeal S).absNorm

theorem sourceRowTwistDyadicConductorScale_ge_one {M : Ideal (𝓞 F)} (hM : M ≠ ⊥) :
    1 ≤ sourceRowTwistDyadicConductorScale F S₀ M := by
  have h₁ : 1 ≤ (M.absNorm : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hM)
  have h₂ : 1 ≤ ((sixthKummerFixedIdeal S).absNorm : ℝ) := by
    exact_mod_cast sixthKummerFixedIdeal_absNorm_pos S
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by norm_num) h₁) h₂

variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

include hζ in
theorem sourceRowTwistFamilyOldModulus_norm_le_dyad {M : Ideal (𝓞 F)}
    {ι : Type} (f : ι → {u : R // u ≠ 0}) (U : ℝ)
    (hQ : ∀ i, (sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀
      (f i).val (f i).property) : ℝ) ≤ 2*U) (i : ι) :
    ((sourceRowTwistFamilyOldModulus F S₀ (M := M) f i).absNorm : ℝ) ≤
      sourceRowTwistDyadicConductorScale F S₀ M * U := by
  have h : ((sourceRowTwistFamilyOldModulus F S₀ (M := M) f i).absNorm : ℝ) ≤
      (M.absNorm : ℝ)*(sixthKummerFixedIdeal S).absNorm *
        sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀ (f i).val (f i).property) := by
    exact_mod_cast sourceRowTwistFamilyOldModulus_norm_le F hζ S₀ (M := M) f i
  calc
    _ ≤ _ := h
    _ ≤ (M.absNorm : ℝ)*(sixthKummerFixedIdeal S).absNorm * (2*U) :=
      mul_le_mul_of_nonneg_left (hQ i) (by positivity)
    _ = _ := by unfold sourceRowTwistDyadicConductorScale; ring

variable [IsTotallyComplex F]
variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M) (hM : M ≠ ⊥)

def sourceRowTwistDyadicExceptionalRows {ι : Type} [Fintype ι]
    (f : ι → {u : R // u ≠ 0}) (U r : ℝ) : Finset (SourceNonprincipalTwistRow F hζ S₀ η hM f) :=
  sourceRowTwistExceptionalRows F hζ S₀ η hM f (sourceRowTwistDyadicConductorScale F S₀ M * U) r

local notation "Δ" => sourceRowTwistDyadicConductorScale F S₀ M

theorem exists_sourceRowTwist_dyadic_good_family :
    ∃ r C U₀ : ℝ, 0 < r ∧ r < 1/10 ∧ 0 < C ∧ 2 ≤ U₀ ∧
      (∀ {ι : Type} [Fintype ι] (f : ι → {u : R // u ≠ 0}) (U : ℝ), U₀ ≤ U →
        (∀ i, (sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀
          (f i).val (f i).property) : ℝ) ≤ 2*U) →
        (∀ i j, (∃ a : F, a ^ 6 = ((f i).val : F) / ((f j).val : F)) → i = j) →
        ((sourceRowTwistDyadicExceptionalRows F S₀ hζ η hM f U r).card : ℝ) ≤ C*U^(1/2 : ℝ)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 < B ∧
        ∀ {ι : Type} [Fintype ι] (f : ι → {u : R // u ≠ 0}) (U : ℝ), U₀ ≤ U →
        (∀ i, (sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀
          (f i).val (f i).property) : ℝ) ≤ 2*U) →
        ∀ i : SourceNonprincipalTwistRow F hζ S₀ η hM f,
          i ∉ sourceRowTwistDyadicExceptionalRows F S₀ hζ η hM f U r →
          ∀ s : ℂ, (499/500 : ℝ) ≤ s.re → |s.im| ≤ 2*U^r →
            ‖sourceRowTwistReciprocal F hζ S₀ (f i.val).val (f i.val).property η hM s‖ ≤ B*U^ε) := by
  obtain ⟨r,C,U₀,hr,hr',hC,hU₀,hcount,hgood⟩ := exists_sourceRowTwist_good_family F hζ S₀ η hM
  have hΔ₁ : 1 ≤ Δ := sourceRowTwistDyadicConductorScale_ge_one F S₀ hM
  have hΔ : 0 < Δ := zero_lt_one.trans_le hΔ₁
  have hscale (U : ℝ) (hU : U₀ ≤ U) : U ≤ Δ*U := le_mul_of_one_le_left (by linarith) hΔ₁
  refine ⟨r,C*Δ^(1/2 : ℝ),U₀,hr,hr',mul_pos hC (Real.rpow_pos_of_pos hΔ _),hU₀,?_,?_⟩
  · intro ι inst f U hU hQ hf
    have h := hcount f (Δ*U) (hU.trans (hscale U hU))
      (sourceRowTwistFamilyOldModulus_norm_le_dyad F S₀ hζ f U hQ) hf
    apply h.trans_eq
    rw [Real.mul_rpow hΔ.le (by linarith : 0 ≤ U), mul_assoc]
  · intro ε hε
    obtain ⟨B,hB,hrec⟩ := hgood ε hε
    refine ⟨B*Δ^ε, mul_pos hB (Real.rpow_pos_of_pos hΔ _), ?_⟩
    intro ι inst f U hU hQ i hi s hs him
    have H := hrec f (Δ*U) (hU.trans (hscale U hU))
      (sourceRowTwistFamilyOldModulus_norm_le_dyad F S₀ hζ f U hQ) i hi s hs
      (him.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by linarith : 0 ≤ U) (hscale U hU) hr.le) (by norm_num)))
    apply H.trans_eq
    rw [Real.mul_rpow hΔ.le (by linarith : 0 ≤ U), mul_assoc]

theorem sourceRowTwistDyadicExceptionalRows_complement_reciprocalDomain
    {ι : Type} [Fintype ι] (f : ι → {u : R // u ≠ 0}) (U r : ℝ) (hU : 0 ≤ U) (hr : 0 ≤ r)
    (i : SourceNonprincipalTwistRow F hζ S₀ η hM f)
    (hi : i ∉ sourceRowTwistDyadicExceptionalRows F S₀ hζ η hM f U r)
    (z : ℂ) (hz : (249/250 : ℝ) ≤ z.re) (him : |z.im| ≤ 4*U^r) :
    z ∈ sourceRayReciprocalDomain F (sourceRowKummerTwist F hζ S₀
      (f i.val).val (f i.val).property η hM)
      (sourceRowTwistFamilyOldModulus_ne_bot F S₀ hM f i.val) := by
  have hΔ : 1 ≤ Δ := sourceRowTwistDyadicConductorScale_ge_one F S₀ hM
  have hscale : U ≤ Δ*U := le_mul_of_one_le_left hU hΔ
  exact sourceRowTwistExceptionalRows_complement_reciprocalDomain F hζ S₀ η hM f (Δ*U) r i hi z hz
    (him.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hU hscale hr) (by norm_num)))

end
end ArtinMatthews.SourceEulerAssembly

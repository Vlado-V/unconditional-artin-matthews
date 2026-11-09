module

public import ArtinMatthews.SourceKPRetainedUpperQuotient
public import ArtinMatthews.SourceKPRetainedPhases


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite sum of right translates produces the product of
the retained additive annihilator indicators. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain StandardAdelic SourcePhysical
open scoped NumberField AdeleRing SourcePhysical Classical BigOperators

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (R M : S → ℕ)

local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "Kf" => sourceKPFiniteLevelSubgroup K hζ
local notation "D" => sourceKPFiniteAdeleProjectiveDiagonalLift K hζ
local notation "Nf" => sourceKPFiniteAdeleUpperLift K hζ
abbrev SourceKPRetainedSeedIndex :=
  ∀ P : S, SourceJacquetUpperQuotient K P.val (R P) (M P)

local notation "A" => SourceKPRetainedSeedIndex K S R M

private def seedRep (a : A) (P : S) : P.val.adicCompletion K :=
  sourceJacquetUpperRepresentative K P.val (R P) (M P) (a P)

def sourceKPRetainedSeedTranslate (qf : Gf) (a : A) : Gf :=
  Nf (∑ P : S, sourceKPFiniteAdditiveSingle K P.val (seedRep K S R M a P)) * qf

def sourceKPRetainedSeedWeight (a : A) : ℂ :=
  (Fintype.card A : ℂ)⁻¹ * ∏ P : S, localFiniteCharacter K P.val (-seedRep K S R M a P)

def sourceKPRetainedSeedCoefficient {T : ℝ} (hT : 1 ≤ T)
    (qf : Gf) (z : ∀ P : S, (P.val.adicCompletion K)ˣ) : ℂ :=
  ∑ a : A, sourceKPRetainedSeedWeight K S R M a *
    sourceKPCuspResidualFourierValue K hζ 1 hT
      (D (sourceKPRetainedDiagonalUnit K S z) * sourceKPRetainedSeedTranslate K hζ S R M qf a)

private theorem finite_upper_phase {T : ℝ} (hT : 1 ≤ T) (v : 𝔸ᶠ[K]ˣ)
    (qf : Gf) (a : A) (U : Finset S) :
    sourceKPCuspResidualFourierValue K hζ 1 hT
      (D v * (Nf (∑ P ∈ U, sourceKPFiniteAdditiveSingle K P.val (seedRep K S R M a P)) * qf)) =
      (∏ P ∈ U, localFiniteCharacter K P.val ((v : 𝔸ᶠ[K]) P.val * seedRep K S R M a P)) *
        sourceKPCuspResidualFourierValue K hζ 1 hT (D v * qf) := by
  induction U using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty, sourceKPFiniteAdeleUpperLift_zero,
      one_mul]
  | @insert P U hP ih =>
    rw [Finset.sum_insert hP, Finset.prod_insert hP, sourceKPFiniteAdeleUpperLift_add, mul_assoc]
    rw [← mul_assoc (D v), ← sourceKPRetainedLocalUpper,
      sourceKPRetainedResidual_diagonal_upper, ih, mul_assoc]

theorem sourceKPRetainedSeedCoefficient_eq {T : ℝ} (hT : 1 ≤ T) (qf : Gf)
    (hperiod : ∀ (P : S) (x : P.val.adicCompletion K),
      x ∈ sourceLocalBall K P.val (-(M P : ℤ)) →
      qf⁻¹ * sourceKPRetainedLocalUpper K hζ P.val x * qf ∈ Kf)
    (z : ∀ P : S, (P.val.adicCompletion K)ˣ) :
    sourceKPRetainedSeedCoefficient K hζ S R M hT qf z =
      sourceKPCuspResidualFourierValue K hζ 1 hT (D (sourceKPRetainedDiagonalUnit K S z)*qf) *
        ∏ P : S, (if (z P : P.val.adicCompletion K)-1 ∈
          sourceLocalBall K P.val ((sourceDifferentExponent K P.val:ℤ)-(R P:ℤ)) then 1 else 0) := by
  let v := sourceKPRetainedDiagonalUnit K S z
  let C := sourceKPCuspResidualFourierValue K hζ 1 hT (D v*qf)
  let phase (P : S) (q : SourceJacquetUpperQuotient K P.val (R P) (M P)) : ℂ :=
    localFiniteCharacter K P.val (((z P : P.val.adicCompletion K)-1) *
      (sourceJacquetUpperRepresentative K P.val (R P) (M P) q : P.val.adicCompletion K))
  have hphase (a : A) :
      sourceKPRetainedSeedWeight K S R M a *
        sourceKPCuspResidualFourierValue K hζ 1 hT
          (D v * sourceKPRetainedSeedTranslate K hζ S R M qf a) =
        C * ((Fintype.card A : ℂ)⁻¹ * ∏ P : S, phase P (a P)) := by
    rw [sourceKPRetainedSeedTranslate, finite_upper_phase, sourceKPRetainedSeedWeight]
    change ((Fintype.card A : ℂ)⁻¹ *
      ∏ P : S, localFiniteCharacter K P.val (-seedRep K S R M a P)) *
      ((∏ P : S, localFiniteCharacter K P.val ((v : 𝔸ᶠ[K]) P.val * seedRep K S R M a P))*C) = _
    rw [show ∀ a b c d : ℂ, (a*b)*(c*d) = d*(a*(b*c)) by intros; ring,
      ← Finset.prod_mul_distrib]
    congr 2
    apply Finset.prod_congr rfl
    intro P _
    rw [sourceKPRetainedDiagonalUnit_at, ← AddChar.map_add_eq_mul]
    unfold phase seedRep
    congr 1
    ring
  change (∑ a : A, sourceKPRetainedSeedWeight K S R M a *
    sourceKPCuspResidualFourierValue K hζ 1 hT
      (D v * sourceKPRetainedSeedTranslate K hζ S R M qf a)) = C * _
  simp_rw [hphase]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  by_cases hzero : C = 0
  · simp only [hzero, zero_mul]
  · congr 1
    rw [← Fintype.prod_sum phase, Fintype.card_pi, Nat.cast_prod,
      ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro P _
    have hsmall : ∀ x ∈ sourceLocalBall K P.val (-(M P : ℤ)),
        localFiniteCharacter K P.val (((z P : P.val.adicCompletion K)-1)*x) = 1 := by
      intro x hx
      rw [← sourceKPRetainedDiagonalUnit_at K S z P]
      exact sourceKPRetained_phase_trivial_of_coefficient_ne_zero K hζ P.val hT v qf
        (M P) (hperiod P) hzero x hx
    exact sourceKPRetainedPhaseAverage_eq_indicator K P.val (R P) (M P)
      ((z P : P.val.adicCompletion K)-1) hsmall

end
end ArtinMatthews

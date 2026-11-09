module

public import ArtinMatthews.ProbeIdealGaussLifting
public import ArtinMatthews.ProbeIdealCharacterCancellation


set_option backward.privateInPublic true
@[expose] public section

/-! Higher outer-modulus local sums vanish at every nonzero prime ideal. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain
open scoped NumberField BigOperators Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def probeIdealLocalHigher (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n m J : ℕ) : ℂ :=
  ∑' d : ((𝓞 K) ⧸ P.asIdeal ^ (m + 1)),
    if hd : probeIdealUniformizer P ^ J -
        probeIdealUniformizer P ^ (n + 1) * Quotient.out d ∈ P.asIdeal ^ (m + 1) then
      (χ ^ (m + 1)) (probeIdealResidueReduction K P (m + 1) (Nat.succ_pos m) d) *
        probeIdealResidueGauss K P (χ ^ (n + 1)) (n + 1) (Nat.succ_pos n)
          (probeIdealDivideResidue P (n + 1) (m + 1) _ hd)
    else 0

theorem probeIdealLocalHigher_lift (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n m J : ℕ) :
    probeIdealLocalHigher K P χ n m J =
      ((Ideal.absNorm P.asIdeal : ℂ) ^ (m + 1))⁻¹ *
        ∑' d : ((𝓞 K) ⧸ P.asIdeal ^ (m + 1)),
          (χ ^ (m + 1)) (probeIdealResidueReduction K P (m + 1) (Nat.succ_pos m) d) *
            probeIdealGaussAt K P (χ ^ (n + 1)) ((m + 1) + (n + 1)) (by omega)
              (probeIdealUniformizer P ^ J -
                probeIdealUniformizer P ^ (n + 1) * Quotient.out d) := by
  unfold probeIdealLocalHigher
  rw [← tsum_mul_left]
  apply tsum_congr
  intro d
  let H := probeIdealUniformizer P ^ J -
    probeIdealUniformizer P ^ (n + 1) * Quotient.out d
  have he := probeIdealGaussAt_exactQuotient K P (χ ^ (n + 1))
    (n + 1) (m + 1) (Nat.succ_pos n) H
  have he' : (if hd : H ∈ P.asIdeal ^ (m + 1) then
      probeIdealResidueGauss K P (χ ^ (n + 1)) (n + 1) (Nat.succ_pos n)
        (probeIdealDivideResidue P (n + 1) (m + 1) H hd) else 0) =
      ((Ideal.absNorm P.asIdeal : ℂ) ^ (m + 1))⁻¹ *
        probeIdealGaussAt K P (χ ^ (n + 1)) ((m + 1) + (n + 1)) (by omega) H := by
    simpa only [Nat.add_comm] using he
  by_cases hd : H ∈ P.asIdeal ^ (m + 1)
  · rw [dite_eq_left hd] at he' ⊢
    rw [he']
    ring
  · rw [dite_eq_right hd] at he' ⊢
    linear_combination
      (χ ^ (m + 1)) (probeIdealResidueReduction K P (m + 1) (Nat.succ_pos m) d) * he'

theorem probeIdealLocalHigher_eq_zero (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n m J : ℕ) (hm : 0 < m) :
    probeIdealLocalHigher K P χ n m J = 0 := by
  let ψ := probeIdealPhase K P ((m + 1) + (n + 1))
  have hψ : ψ.IsPrimitive := probeIdealPhase_primitive K P _
  let : Finite ((𝓞 K) ⧸ P.asIdeal ^ (m + 1)) :=
    Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero _ P.ne_bot)
  let : Fintype ((𝓞 K) ⧸ P.asIdeal ^ (m + 1)) := Fintype.ofFinite _
  let : Finite ((𝓞 K) ⧸ P.asIdeal ^ ((m + 1) + (n + 1))) :=
    Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero _ P.ne_bot)
  let : Fintype ((𝓞 K) ⧸ P.asIdeal ^ ((m + 1) + (n + 1))) := Fintype.ofFinite _
  have hG (d : ((𝓞 K) ⧸ P.asIdeal ^ (m + 1))) :
      probeIdealGaussAt K P (χ ^ (n + 1)) ((m + 1) + (n + 1)) (by omega)
          (probeIdealUniformizer P ^ J - probeIdealUniformizer P ^ (n + 1) * Quotient.out d) =
        ∑' v : ((𝓞 K) ⧸ P.asIdeal ^ ((m + 1) + (n + 1))),
          (χ ^ (n + 1)) (probeIdealResidueReduction K P (m + 1) (Nat.succ_pos m)
            (probePrimePowerReduction P ((m + 1) + (n + 1)) (m + 1)
              (Nat.le_add_right _ _) v)) *
          ψ (Ideal.Quotient.mk _ (probeIdealUniformizer P ^ J -
            probeIdealUniformizer P ^ (n + 1) * Quotient.out d) * v) := by
    unfold probeIdealGaussAt
    apply tsum_congr
    intro v
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective v
    rfl
  have hphase (d : ((𝓞 K) ⧸ P.asIdeal ^ (m + 1)))
      (v : ((𝓞 K) ⧸ P.asIdeal ^ ((m + 1) + (n + 1)))) :
      ψ (Ideal.Quotient.mk _ (probeIdealUniformizer P ^ J -
        probeIdealUniformizer P ^ (n + 1) * Quotient.out d) * v) =
        ψ (Ideal.Quotient.mk _ (probeIdealUniformizer P ^ J) * v) *
          ψ (-(probePrimePowerScale P (m + 1) (n + 1) d * v)) := by
    have hd : probePrimePowerScale P (m + 1) (n + 1) d =
        Ideal.Quotient.mk _ (probeIdealUniformizer P ^ (n + 1) * Quotient.out d) := by
      conv_lhs => rw [show d = Ideal.Quotient.mk _ (Quotient.out d) from
        (Ideal.Quotient.mk_out d).symm]
      exact probePrimePowerScale_mk _ _ _ _
    rw [hd, map_sub, sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul]
  have hdouble :
      (∑' d : ((𝓞 K) ⧸ P.asIdeal ^ (m + 1)),
          (χ ^ (m + 1)) (probeIdealResidueReduction K P (m + 1) (Nat.succ_pos m) d) *
            probeIdealGaussAt K P (χ ^ (n + 1)) ((m + 1) + (n + 1)) (by omega)
              (probeIdealUniformizer P ^ J -
                probeIdealUniformizer P ^ (n + 1) * Quotient.out d)) =
        probeIdealHigherMixedSum K P m (n + 1) (χ ^ (m + 1)) (χ ^ (n + 1))
          ψ (probeIdealUniformizer P ^ J) := by
    simp only [hG, probeIdealHigherMixedSum, tsum_fintype, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro d _
    rw [hphase]
    ring
  rw [probeIdealLocalHigher_lift, hdouble,
    probeIdealHigherMixedSum_eq_zero K P m (n + 1) hm _ _ ψ hψ, mul_zero]

end

end ArtinMatthews.VaryingKummerAnalytic

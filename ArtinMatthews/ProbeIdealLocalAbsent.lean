module

public import ArtinMatthews.ProbeIdealPrimeGauss
public import ArtinMatthews.ProbePrimeLocalAbsent


set_option backward.privateInPublic true
@[expose] public section

/-! Missing-modulus cases, with the positive modulus still zero-extended. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain
open scoped NumberField BigOperators Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def probeIdealLocalInnerAbsent (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (m J : ℕ) : ℂ :=
  ∑' d : ((𝓞 K) ⧸ P.asIdeal ^ (m + 1)),
    if d = Ideal.Quotient.mk _ (probeIdealUniformizer P ^ J) then
      (χ ^ (m + 1)) (probeIdealResidueReduction K P (m + 1) (Nat.succ_pos m) d) else 0

theorem probeIdealLocalInnerAbsent_eq (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (m J : ℕ) :
    probeIdealLocalInnerAbsent K P χ m J = if J = 0 then 1 else 0 := by
  let : Field ((𝓞 K) ⧸ P.asIdeal) := Ideal.Quotient.field _
  unfold probeIdealLocalInnerAbsent
  rw [tsum_eq_single (Ideal.Quotient.mk (P.asIdeal ^ (m + 1)) (probeIdealUniformizer P ^ J))]
  · rw [ite_eq_left rfl]
    change (χ ^ (m + 1)) (Ideal.Quotient.mk P.asIdeal (probeIdealUniformizer P ^ J)) = _
    cases J with
    | zero => simp
    | succ J =>
        have hz : Ideal.Quotient.mk P.asIdeal (probeIdealUniformizer P ^ (J + 1)) = 0 := by
          rw [map_pow]
          have hpz : Ideal.Quotient.mk P.asIdeal (probeIdealUniformizer P) = 0 :=
            Ideal.Quotient.eq_zero_iff_mem.mpr (probeIdealUniformizer_mem P)
          rw [hpz, zero_pow (Nat.succ_ne_zero J)]
        rw [hz, MulChar.map_zero, ite_eq_right (Nat.succ_ne_zero J)]
  · intro d hd
    exact ite_eq_right hd

end

end ArtinMatthews.VaryingKummerAnalytic

module

public import ArtinMatthews.SourceJacquetShellVector


set_option backward.privateInPublic true
@[expose] public section

/-! The three exact valuation rows of the literal Jacquet shell vector.
The modular and measure exponent is kept in the common factor from
Appendix 10, and the second row uses the actual normalized Gauss pair. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators QuadraticWeil VaryingKummerAnalytic
open scoped NumberField BigOperators Classical
noncomputable section

theorem sourceJacquetScale_mul_div_sqrt {Q : ℝ} (hQ : 0 < Q) (a b : ℝ) (z : ℂ) :
    sourceJacquetScale Q a * (sourceJacquetScale Q b * (z / (Real.sqrt Q : ℂ))) =
      sourceJacquetScale Q (a + b - 1 / 2) * z := by
  rw [div_eq_mul_inv, ← sourceJacquetScale_neg_half hQ.le, sub_eq_add_neg,
    show -(1 / 2 : ℝ) = -1 / 2 by ring, sourceJacquetScale_add hQ, sourceJacquetScale_add hQ]
  ring

variable (F : Type) [Field F] [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (P : SourceExteriorPrime F S₀)

theorem sourceJacquetActualGauss_mod_six (j : ℕ) :
    sourceJacquetActualGauss F hζ S₀ P j = sourceJacquetActualGauss F hζ S₀ P (j % 6) := by
  have h := pow_mod_orderOf (reflectionPrimeCharacters F hζ S₀ P) j
  rw [sourceJacquetActualCharacter_order F hζ S₀ P] at h
  unfold sourceJacquetActualGauss sourceJacquetGauss
  erw [← h]

theorem sourceJacquetActualShell_terminal_nonprincipal
    (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀) (e : ℕ) (he : ¬3 ∣ e + 1) :
    sourceJacquetActualShell F hζ S₀ P e (e + 1) =
      sourceJacquetActualGauss F hζ S₀ P ((4 * (e + 1)) % 6) /
        (Real.sqrt (Ideal.absNorm P.val.asIdeal : ℝ) : ℂ) := by
  rw [sourceJacquetActualShell_table F hζ S₀ P hS, ite_eq_right (by omega : ¬e + 1 ≤ e),
    ite_eq_left rfl, ite_eq_right he, sourceJacquetActualGauss_mod_six]

theorem sourceJacquetActualShell_terminal_principal
    (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀) (e : ℕ) (he : 3 ∣ e + 1) :
    sourceJacquetActualShell F hζ S₀ P e (e + 1) = -(Ideal.absNorm P.val.asIdeal : ℂ)⁻¹ := by
  rw [sourceJacquetActualShell_table F hζ S₀ P hS, ite_eq_right (by omega : ¬e + 1 ≤ e),
    ite_eq_left rfl, ite_eq_left he]

theorem sourceJacquetShellVector_three
    (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀) (k : ℕ) :
    sourceJacquetShellVector F hζ S₀ P (3 * k) =
      let Q : ℝ := Ideal.absNorm P.val.asIdeal
      sourceJacquetScale Q (-(k : ℝ)) •
        (sourceJacquetBasis 0 + (sourceJacquetScale Q (-1 / 6) *
          sourceJacquetActualGauss F hζ S₀ P 4) • sourceJacquetBasis 2) := by
  let Q : ℝ := Ideal.absNorm P.val.asIdeal
  have hQ : 0 < Q := sourceJacquetPrimeNorm_pos F S₀ P
  have hK : (↑(3 * k : ℕ) : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr ⟨k, rfl⟩
  have hI : -(↑(3 * k : ℕ) : ZMod 3) = 0 := by
    rw [hK]
    decide
  have hJ : -(↑(3 * k : ℕ) : ZMod 3) + 2 * ↑(3 * k + 1 : ℕ) = 2 := by
    rw [hI, Nat.cast_add, hK]
    decide
  have hA : sourceJacquetScale Q (-2 * ↑(3 * k : ℕ) / 3) * sourceJacquetScale Q (k : ℝ) =
      sourceJacquetScale Q (-(k : ℝ)) := by
    rw [← sourceJacquetScale_add hQ]
    congr 1
    push_cast
    ring
  have hB : sourceJacquetScale Q (-2 * ↑(3 * k : ℕ) / 3) *
      (sourceJacquetScale Q (↑(3 * k + 1 : ℕ) / 3) *
        (sourceJacquetActualGauss F hζ S₀ P 4 / (Real.sqrt Q : ℂ))) =
      sourceJacquetScale Q (-(k : ℝ)) *
        (sourceJacquetScale Q (-1 / 6) * sourceJacquetActualGauss F hζ S₀ P 4) := by
    rw [sourceJacquetScale_mul_div_sqrt hQ, ← mul_assoc, ← sourceJacquetScale_add hQ]
    congr 2
    push_cast
    ring
  rw [sourceJacquetShellVector_reduce F hζ S₀ P hS]
  dsimp only
  rw [show (3 * k) / 3 = k by omega, hJ, hI, sourceJacquetActualShell_terminal_nonprincipal F hζ S₀ P hS _
    (by omega), show (4 * (3 * k + 1)) % 6 = 4 by omega]
  dsimp only [Q] at hA hB
  simp only [smul_add, smul_smul]
  rw [hA, hB]

theorem sourceJacquetShellVector_three_add_one
    (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀) (k : ℕ) :
    sourceJacquetShellVector F hζ S₀ P (3 * k + 1) =
      let Q : ℝ := Ideal.absNorm P.val.asIdeal
      (sourceJacquetScale Q (-(k : ℝ) - 1 / 2) * sourceJacquetActualGauss F hζ S₀ P 2) •
        (sourceJacquetBasis 0 + (sourceJacquetScale Q (-1 / 6) *
          sourceJacquetActualGauss F hζ S₀ P 4) • sourceJacquetBasis 2) := by
  let Q : ℝ := Ideal.absNorm P.val.asIdeal
  have hQ : 0 < Q := sourceJacquetPrimeNorm_pos F S₀ P
  have hK : (↑(3 * k : ℕ) : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr ⟨k, rfl⟩
  have hI : -(↑(3 * k + 1 : ℕ) : ZMod 3) = 2 := by
    rw [Nat.cast_add, hK, zero_add]
    decide
  have hJ : -(↑(3 * k + 1 : ℕ) : ZMod 3) + 2 * ↑(3 * k + 1 + 1 : ℕ) = 0 := by
    rw [hI, Nat.cast_add, Nat.cast_add, hK]
    decide
  have hA : sourceJacquetScale Q (-2 * ↑(3 * k + 1 : ℕ) / 3) * sourceJacquetScale Q (k : ℝ) =
      sourceJacquetScale Q (-(k : ℝ) - 2 / 3) := by
    rw [← sourceJacquetScale_add hQ]
    congr 1
    push_cast
    ring
  have hB : sourceJacquetScale Q (-2 * ↑(3 * k + 1 : ℕ) / 3) *
      (sourceJacquetScale Q (↑(3 * k + 1 + 1 : ℕ) / 3) *
        (sourceJacquetActualGauss F hζ S₀ P 2 / (Real.sqrt Q : ℂ))) =
      sourceJacquetScale Q (-(k : ℝ) - 1 / 2) * sourceJacquetActualGauss F hζ S₀ P 2 := by
    rw [sourceJacquetScale_mul_div_sqrt hQ]
    congr 2
    push_cast
    ring
  have hC : (sourceJacquetScale Q (-(k : ℝ) - 1 / 2) * sourceJacquetActualGauss F hζ S₀ P 2) *
      (sourceJacquetScale Q (-1 / 6) * sourceJacquetActualGauss F hζ S₀ P 4) =
      sourceJacquetScale Q (-(k : ℝ) - 2 / 3) := by
    calc
      _ = (sourceJacquetScale Q (-(k : ℝ) - 1 / 2) * sourceJacquetScale Q (-1 / 6)) *
          (sourceJacquetActualGauss F hζ S₀ P 2 * sourceJacquetActualGauss F hζ S₀ P 4) := by ring
      _ = _ := by
        rw [sourceJacquetActualGauss_two_four F hζ S₀ P hS, mul_one, ← sourceJacquetScale_add hQ]
        congr 1
        ring
  rw [sourceJacquetShellVector_reduce F hζ S₀ P hS]
  dsimp only
  rw [show (3 * k + 1) / 3 = k by omega, hJ, hI,
    sourceJacquetActualShell_terminal_nonprincipal F hζ S₀ P hS _ (by omega),
    show (4 * (3 * k + 1 + 1)) % 6 = 2 by omega]
  dsimp only [Q] at hA hB hC
  simp only [smul_add, smul_smul]
  rw [hA, hB, hC, add_comm]

theorem sourceJacquetShellVector_three_add_two
    (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀) (k : ℕ) :
    sourceJacquetShellVector F hζ S₀ P (3 * k + 2) = 0 := by
  let Q : ℝ := Ideal.absNorm P.val.asIdeal
  have hQ : 0 < Q := sourceJacquetPrimeNorm_pos F S₀ P
  have hK : (↑(3 * k : ℕ) : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr ⟨k, rfl⟩
  have hI : -(↑(3 * k + 2 : ℕ) : ZMod 3) = 1 := by
    rw [Nat.cast_add, hK, zero_add]
    decide
  have hJ : -(↑(3 * k + 2 : ℕ) : ZMod 3) + 2 * ↑(3 * k + 2 + 1 : ℕ) = 1 := by
    rw [hI, Nat.cast_add, Nat.cast_add, hK]
    decide
  have hA : sourceJacquetScale Q (↑(3 * k + 2 + 1 : ℕ) / 3) * -(Q : ℂ)⁻¹ =
      -(sourceJacquetScale Q (k : ℝ)) := by
    rw [mul_neg, ← sourceJacquetScale_neg_one Q, ← sourceJacquetScale_add hQ]
    congr 2
    push_cast
    ring
  have hA' : sourceJacquetScale (Ideal.absNorm P.val.asIdeal : ℝ) (↑(3 * k + 2 + 1 : ℕ) / 3) *
      -(Ideal.absNorm P.val.asIdeal : ℂ)⁻¹ =
      -(sourceJacquetScale (Ideal.absNorm P.val.asIdeal : ℝ) (k : ℝ)) := by
    simpa only [Q, Complex.ofReal_natCast] using hA
  rw [sourceJacquetShellVector_reduce F hζ S₀ P hS]
  dsimp only
  rw [show (3 * k + 2) / 3 = k by omega, hJ, hI,
    sourceJacquetActualShell_terminal_principal F hζ S₀ P hS _ (by omega), hA', ← add_smul,
    add_neg_cancel, zero_smul, smul_zero]

theorem sourceJacquetShellVector_zero_at_zero
    (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀) :
    sourceJacquetShellVector F hζ S₀ P 0 0 = 1 := by
  have h := congrFun (sourceJacquetShellVector_three F hζ S₀ P hS 0) 0
  simpa [sourceJacquetBasis, sourceJacquetScale, Pi.single_eq_of_ne (by decide : (0 : ZMod 3) ≠ 2)] using h

theorem sourceJacquetShellVector_zero_ne_zero
    (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀) :
    sourceJacquetShellVector F hζ S₀ P 0 ≠ 0 := by
  intro h
  have hz := sourceJacquetShellVector_zero_at_zero F hζ S₀ P hS
  rw [h, Pi.zero_apply] at hz
  exact zero_ne_one hz

end
end ArtinMatthews

module

public import ArtinMatthews.SourceJacquetActualShell
public import ArtinMatthews.SourceJacquetGeometric
public import Mathlib.Algebra.Module.BigOperators


set_option backward.privateInPublic true
@[expose] public section

/-! The finite shell vector assembled from the literal Haar integrals.
The basis is indexed by the actual valuation classes modulo three.
This calculation does not identify it with a Whittaker functional. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators QuadraticWeil VaryingKummerAnalytic
open scoped NumberField BigOperators Classical
noncomputable section

def sourceJacquetScale (Q a : ℝ) : ℂ := (Q ^ a : ℝ)

theorem sourceJacquetScale_add {Q : ℝ} (hQ : 0 < Q) (a b : ℝ) :
    sourceJacquetScale Q (a + b) = sourceJacquetScale Q a * sourceJacquetScale Q b := by
  rw [sourceJacquetScale, Real.rpow_add hQ, Complex.ofReal_mul]
  rfl

theorem sourceJacquetScale_nat (Q : ℝ) (k : ℕ) :
    sourceJacquetScale Q k = (Q : ℂ) ^ k := by
  rw [sourceJacquetScale, Real.rpow_natCast, Complex.ofReal_pow]

theorem sourceJacquetScale_neg_one (Q : ℝ) :
    sourceJacquetScale Q (-1) = (Q : ℂ)⁻¹ := by
  rw [sourceJacquetScale, Real.rpow_neg_one, Complex.ofReal_inv]

theorem sourceJacquetScale_neg_half {Q : ℝ} (hQ : 0 ≤ Q) :
    sourceJacquetScale Q (-1 / 2) = (Real.sqrt Q : ℂ)⁻¹ := by
  rw [sourceJacquetScale, Real.sqrt_eq_rpow, show (-1 / 2 : ℝ) = -(1 / 2) by ring,
    Real.rpow_neg hQ, Complex.ofReal_inv]

def sourceJacquetBasis (i : ZMod 3) : ZMod 3 → ℂ := Pi.single i 1

variable (F : Type) [Field F] [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (P : SourceExteriorPrime F S₀)

theorem sourceJacquetPrimeNorm_pos : 0 < (Ideal.absNorm P.val.asIdeal : ℝ) :=
  Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.val.ne_bot))

def sourceJacquetShellVector (e : ℕ) : ZMod 3 → ℂ :=
  let Q : ℝ := Ideal.absNorm P.val.asIdeal
  sourceJacquetScale Q (-2 * (e : ℝ) / 3) •
    (sourceJacquetBasis (-(e : ZMod 3)) +
      ∑ l ∈ Finset.Icc 1 (e + 1),
        (sourceJacquetScale Q ((l : ℝ) / 3) * sourceJacquetActualShell F hζ S₀ P e l) •
          sourceJacquetBasis (-(e : ZMod 3) + 2 * (l : ZMod 3)))

theorem sourceJacquetShellVector_reduce
    (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀) (e : ℕ) :
    sourceJacquetShellVector F hζ S₀ P e =
      let Q : ℝ := Ideal.absNorm P.val.asIdeal
      sourceJacquetScale Q (-2 * (e : ℝ) / 3) •
        (sourceJacquetScale Q (↑(e / 3 : ℕ)) • sourceJacquetBasis (-(e : ZMod 3)) +
          (sourceJacquetScale Q (↑(e + 1 : ℕ) / 3) * sourceJacquetActualShell F hζ S₀ P e (e + 1)) •
            sourceJacquetBasis (-(e : ZMod 3) + 2 * (↑(e + 1 : ℕ) : ZMod 3))) := by
  let Q : ℝ := Ideal.absNorm P.val.asIdeal
  have hQ : 0 < Q := sourceJacquetPrimeNorm_pos F S₀ P
  have hQ0 : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ.ne'
  let b : ZMod 3 → ℂ := sourceJacquetBasis (-(e : ZMod 3))
  let f : ℕ → ℂ := fun l => if 3 ∣ l then (Q : ℂ) ^ (l / 3) * (1 - (Q : ℂ)⁻¹) else 0
  have hsum : (∑ l ∈ Finset.Icc 1 e,
        (sourceJacquetScale Q ((l : ℝ) / 3) * sourceJacquetActualShell F hζ S₀ P e l) •
          sourceJacquetBasis (-(e : ZMod 3) + 2 * (l : ZMod 3))) =
      (∑ l ∈ Finset.Icc 1 e, f l) • b := by
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro l hl
    have hle := (Finset.mem_Icc.mp hl).2
    rw [sourceJacquetActualShell_table F hζ S₀ P hS, ite_eq_left hle]
    by_cases hd : 3 ∣ l
    · have hcast : (l : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff l 3).mpr hd
      have hh : (↑(l / 3 : ℕ) : ℝ) * 3 = l := by exact_mod_cast Nat.div_mul_cancel hd
      have he : (l : ℝ) / 3 = (↑(l / 3 : ℕ) : ℝ) := by linarith
      rw [ite_eq_left hd, hcast, mul_zero, add_zero, he, sourceJacquetScale_nat]
      dsimp only [f]
      rw [ite_eq_left hd]
      rfl
    · dsimp only [f]
      rw [ite_eq_right hd, ite_eq_right hd, mul_zero, zero_smul, zero_smul]
  have hbulk : b + (∑ l ∈ Finset.Icc 1 e, f l) • b = sourceJacquetScale Q (↑(e / 3 : ℕ)) • b := by
    rw [sourceJacquetScale_nat, ← sourceJacquet_geometric_bulk (Q : ℂ) hQ0 e, add_smul, one_smul]
  unfold sourceJacquetShellVector
  dsimp only
  rw [Finset.sum_Icc_succ_top (by omega), hsum, ← add_assoc, hbulk]

end
end ArtinMatthews

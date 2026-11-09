module

public import ArtinMatthews.CubicThetaResidueActual
public import ArtinMatthews.HeckeDirichletNormResidue
public import Mathlib.NumberTheory.DirichletCharacter.Bounds


set_option backward.privateInPublic true
@[expose] public section

/-! The actual complete norm classes for Section 6.2, including nonunit
classes and the exact Dirichlet twist. -/

noncomputable section
namespace ArtinMatthews

open OAI OAI.SevenEighths
open scoped BigOperators

def cubicNormClassWeight (η : HeckeFamily.Character) {M q : ℕ}
    (χ : DirichletCharacter ℂ M) (b : ZMod q) (z : ℤ × ℤ) : ℂ :=
  HeckeFamily.elementCoeff η (HeckeFamily.coordinateElement z.1 z.2) *
    (if (eisensteinIntegerNorm z : ZMod q) = b then
      χ (eisensteinIntegerNorm z : ZMod M) else 0)

theorem cubicNormClassWeight_norm_le (η : HeckeFamily.Character) {M q : ℕ} [NeZero M]
    (χ : DirichletCharacter ℂ M) (b : ZMod q) (z : ℤ × ℤ) :
    ‖cubicNormClassWeight η χ b z‖ ≤ 1 := by
  let : Finite (HeckeFamily.O ⧸ η.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  have hη : ‖HeckeFamily.elementCoeff η (HeckeFamily.coordinateElement z.1 z.2)‖ ≤ 1 :=
    IdealCharacter.norm_residue_le_one η.modulus η.residue _
  have hχ : ‖if (eisensteinIntegerNorm z : ZMod q) = b then
      χ (eisensteinIntegerNorm z : ZMod M) else 0‖ ≤ 1 := by
    split_ifs
    · exact χ.norm_le_one _
    · simp only [norm_zero, zero_le_one]
  rw [cubicNormClassWeight, norm_mul]
  simpa only [one_mul] using mul_le_mul hη hχ (norm_nonneg _) zero_le_one

def cubicNormClassResidueWeight (η : HeckeFamily.Character) {M q : ℕ}
    (χ : DirichletCharacter ℂ M) (b : ZMod q) (P : ℕ) (r : Fin P × Fin P) : ℂ :=
  cubicNormClassWeight η χ b ((r.1 : ℤ), (r.2 : ℤ))

theorem cubicNormClassResidueWeight_periodic (A : ℤ) (hA : A ≠ 0) {M q P : ℕ} [NeZero P]
    (χ : DirichletCharacter ℂ M) (b : ZMod q)
    (hAdiv : 9 * A ∣ (P : ℤ)) (hM : M ∣ P) (hq : q ∣ P) (z : ℤ × ℤ) :
    HeckeTheta.periodicCoeff
      (cubicNormClassResidueWeight (cubicNumeratorHeckeCharacter A hA) χ b P) z =
      cubicNormClassWeight (cubicNumeratorHeckeCharacter A hA) χ b z := by
  let r := (HeckeTheta.residueEquiv P z).1
  let p : ℤ × ℤ := ((r.1 : ℤ), (r.2 : ℤ))
  have hd := eisensteinIntegerNorm_residue_dvd P z
  have hcong (m : ℕ) (hm : m ∣ P) :
      (eisensteinIntegerNorm z : ZMod m) = (eisensteinIntegerNorm p : ZMod m) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ m).mpr
      ((show (m : ℤ) ∣ (P : ℤ) by exact_mod_cast hm).trans (dvd_sub_comm.mp hd))
  have hη := cubicThetaActual_periodicCoeff A hA P hAdiv z
  change HeckeFamily.elementCoeff (cubicNumeratorHeckeCharacter A hA)
    (HeckeFamily.coordinateElement p.1 p.2) = _ at hη
  change cubicNormClassWeight (cubicNumeratorHeckeCharacter A hA) χ b p = _
  rw [cubicNormClassWeight, cubicNormClassWeight, hη, ← hcong M hM, ← hcong q hq]

theorem cubicNormClassResidueWeight_sum_zero (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {M q P : ℕ} [NeZero P] (χ : DirichletCharacter ℂ M) (b : ZMod q)
    (hAdiv : 9 * A ∣ (P : ℤ)) (hM : M ∣ P) (hq : q ∣ P) :
    (∑ r, cubicNormClassResidueWeight (cubicNumeratorHeckeCharacter A hA) χ b P r) = 0 := by
  let f := cubicThetaResidueReduction A P hAdiv
  let e := cubicThetaFiniteCoordinates P
  let ψ := cubicNumeratorHeckeResidue A hA
  let g (s : ZMod P) : ℂ :=
    if ZMod.castHom hq (ZMod q) s = b then χ (ZMod.castHom hM (ZMod M) s) else 0
  let F (s : CubicThetaResidue P) : ℂ := g ((cubicThetaCoordinateEquiv P).symm s).1
  have hanti : ∀ u : (HeckeFamily.O ⧸ cubicNumeratorHeckeModulus A)ˣ,
      ψ (cubicNumeratorResidueConjugation A u) = (ψ u)⁻¹ :=
    fun u => cubicNumeratorHeckeCharacter_residue_conjugate_inv A hA u
  have hcube (u : (HeckeFamily.O ⧸ cubicNumeratorHeckeModulus A)ˣ) : ψ u ^ 3 = 1 := by
    have h := congrArg (fun ψ : MulChar (HeckeFamily.O ⧸ cubicNumeratorHeckeModulus A) ℂ =>
      ψ u) (cubicNumeratorHeckeResidue_cube A hA)
    simpa only [MulChar.pow_apply_coe, MulChar.one_apply u.isUnit] using h
  have hsum := anticyclotomic_cubic_inflated_sum_norm_eq_zero
    f (cubicThetaResidueReduction_surjective A P hAdiv)
    (cubicThetaResidueConjugation P) (cubicNumeratorResidueConjugation A)
    (cubicThetaResidueConjugation_involutive P)
    (cubicThetaResidueReduction_conjugate A P hAdiv) ψ hanti hcube
    (cubicNumeratorHeckeCharacter_nonprincipal A hA hnoncube) F
  have hF (s : CubicThetaResidue P) :
      F (s * cubicThetaResidueConjugation P s) = g (heckeResidueNormValue P s) := by
    rw [← heckeResidueNormValue_scalar, heckeNormScalar_eq_coordinates]
    simp only [F, Equiv.symm_apply_apply]
  have hnorm (r : Fin P × Fin P) : heckeResidueNormValue P (e r) =
      (eisensteinIntegerNorm ((r.1 : ℤ), (r.2 : ℤ)) : ZMod P) := by
    change heckeResidueNormValue P (cubicThetaCoordinateEquiv P
      ((r.1 : ℕ), (r.2 : ℕ))) = _
    rw [heckeResidueNormValue_coordinates]
    simp only [eisensteinIntegerNorm, Int.cast_add, Int.cast_sub, Int.cast_mul,
      Int.cast_pow, Int.cast_natCast]
  calc
    _ = ∑ r : Fin P × Fin P, ψ (f (e r)) * F (e r * cubicThetaResidueConjugation P (e r)) := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [hF, hnorm]
      change _ = ψ (cubicThetaResidueReduction A P hAdiv
        (cubicThetaFiniteCoordinates P r)) * _
      rw [cubicThetaFiniteCoordinates_apply, cubicThetaResidueReduction_mk]
      simp only [g, map_intCast]
      rfl
    _ = ∑ s : CubicThetaResidue P, ψ (f s) * F (s * cubicThetaResidueConjugation P s) :=
      e.bijective.sum_comp (fun s : CubicThetaResidue P =>
        ψ (f s) * F (s * cubicThetaResidueConjugation P s))
    _ = 0 := hsum

end ArtinMatthews

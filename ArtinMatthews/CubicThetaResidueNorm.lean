module

public import ArtinMatthews.CubicThetaResidueCoordinates
public import ArtinMatthews.CubicThetaRationalTwist


set_option backward.privateInPublic true
@[expose] public section

/-! The rational-translation phase factors through the actual residue norm. -/

noncomputable section
namespace ArtinMatthews

open OAI OAI.SevenEighths
open scoped BigOperators

local notation "EO" => HeckeFamily.O

theorem heckeIntegerConjugation_eq_conjO (x : EO) :
    heckeIntegerConjugation x = ActualEisensteinCubic.conjO x := by
  apply ConcreteTraceCRT.eisEmbedding_injective
  rw [heckeIntegerConjugation_embedding, ActualEisensteinCubic.eisEmbedding_conjO]

theorem coordinateElement_mul_conjugation (a b : ℤ) :
    HeckeFamily.coordinateElement a b *
      heckeIntegerConjugation (HeckeFamily.coordinateElement a b) =
        (eisensteinIntegerNorm (a, b) : EO) := by
  rw [heckeIntegerConjugation_eq_conjO]
  change ActualEisensteinCoordinates.eval a b *
    ActualEisensteinCubic.conjO (ActualEisensteinCoordinates.eval a b) = _
  rw [← ActualEisensteinCubic.coordinate_norm_eq_mul_conjO,
    ShortDraftLatticeCount.coords_eval]
  rfl

def cubicThetaScalarPhase (a : ℤ) (M : ℕ) (z : ℤ) : ℂ :=
  Complex.exp ((a : ℂ) / M * (2 * (Real.pi : ℂ) * Complex.I) * (z : ℂ))

theorem cubicThetaScalarPhase_congr (a : ℤ) (M : ℕ) [NeZero M] {z w : ℤ}
    (h : (M : ℤ) ∣ z - w) :
    cubicThetaScalarPhase a M z = cubicThetaScalarPhase a M w := by
  obtain ⟨k, hk⟩ := h
  unfold cubicThetaScalarPhase
  apply Complex.exp_eq_exp_iff_exp_sub_eq_one.mpr
  apply Complex.exp_eq_one_iff.mpr
  refine ⟨a * k, ?_⟩
  have hkc := congrArg (fun z : ℤ => (z : ℂ)) hk
  push_cast at hkc ⊢
  have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  calc
    _ = (a : ℂ) / M * (2 * (Real.pi : ℂ) * Complex.I) * ((z : ℂ) - w) := by ring
    _ = _ := by rw [hkc]; field_simp

theorem cubicThetaScalarPhase_val (a : ℤ) (M : ℕ) [NeZero M] (z : ℤ) :
    cubicThetaScalarPhase a M (((z : ZMod M).val : ℕ) : ℤ) =
      cubicThetaScalarPhase a M z := by
  apply cubicThetaScalarPhase_congr
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub z _ M).mp
  simp

/-- A function of the residue-ring norm alone. Its value on `x κ(x)` is
the exact rational-translation phase at any integer coordinates for `x`. -/
def cubicThetaResidueNormPhase (a : ℤ) (M : ℕ) [NeZero M]
    (x : CubicThetaResidue M) : ℂ :=
  cubicThetaScalarPhase a M ((cubicThetaCoordinateEquiv M).symm x).1.val

theorem cubicThetaResidueNormPhase_coordinates (a : ℤ) (M : ℕ) [NeZero M]
    (b c : ℤ) :
    cubicThetaResidueNormPhase a M
      (cubicThetaCoordinateEquiv M ((b : ZMod M), (c : ZMod M)) *
        cubicThetaResidueConjugation M
          (cubicThetaCoordinateEquiv M ((b : ZMod M), (c : ZMod M)))) =
      eisensteinRationalPhase a M (b, c) := by
  rw [cubicThetaCoordinateEquiv_intCast, cubicThetaResidueConjugation_mk, ← map_mul,
    coordinateElement_mul_conjugation]
  have heq : Ideal.Quotient.mk (cubicThetaRationalModulus M)
      (eisensteinIntegerNorm (b, c) : EO) =
      cubicThetaCoordinateEquiv M ((eisensteinIntegerNorm (b, c) : ZMod M), 0) := by
    rw [show (0 : ZMod M) = ((0 : ℤ) : ZMod M) by simp,
      cubicThetaCoordinateEquiv_intCast]
    simp [HeckeFamily.coordinateElement]
  rw [heq]
  unfold cubicThetaResidueNormPhase
  rw [Equiv.symm_apply_apply]
  exact cubicThetaScalarPhase_val a M _

end ArtinMatthews

module

public import ArtinMatthews.CubicThetaResidueNorm


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Eisenstein norm modulo a rational modulus, as a
multiplicative map. Its unit criterion supports Dirichlet norm pullback. -/

noncomputable section
namespace ArtinMatthews

open OAI OAI.SevenEighths
local notation "EO" => HeckeFamily.O

def heckeNormScalar (q : ℕ) : ZMod q →+* CubicThetaResidue q where
  toFun := cubicThetaZModResidueHom q
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    simpa only [Int.cast_one, map_one] using cubicThetaZModResidueHom_intCast q 1
  map_mul' x y := by
    obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
    obtain ⟨b, rfl⟩ := ZMod.intCast_surjective y
    rw [← Int.cast_mul, cubicThetaZModResidueHom_intCast,
      cubicThetaZModResidueHom_intCast, cubicThetaZModResidueHom_intCast, Int.cast_mul, map_mul]

theorem heckeNormScalar_intCast (q : ℕ) (a : ℤ) :
    heckeNormScalar q (a : ZMod q) = Ideal.Quotient.mk (cubicThetaRationalModulus q) (a : EO) :=
  cubicThetaZModResidueHom_intCast q a

theorem heckeNormScalar_eq_coordinates (q : ℕ) [NeZero q] (a : ZMod q) :
    heckeNormScalar q a = cubicThetaCoordinateEquiv q (a, 0) := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective a
  rw [heckeNormScalar_intCast,
    show (0 : ZMod q) = ((0 : ℤ) : ZMod q) by simp,
    cubicThetaCoordinateEquiv_intCast]
  simp only [HeckeFamily.coordinateElement, Int.cast_zero, zero_mul, add_zero]

theorem heckeNormScalar_injective (q : ℕ) [NeZero q] :
    Function.Injective (heckeNormScalar q) := by
  intro a b hab
  rw [heckeNormScalar_eq_coordinates, heckeNormScalar_eq_coordinates] at hab
  exact congrArg Prod.fst ((cubicThetaCoordinateEquiv q).injective hab)

def heckeResidueNormValue (q : ℕ) [NeZero q] (r : CubicThetaResidue q) : ZMod q :=
  let p := (cubicThetaCoordinateEquiv q).symm r
  p.1^2-p.1*p.2+p.2^2

theorem heckeResidueNormValue_coordinates (q : ℕ) [NeZero q] (a b : ZMod q) :
    heckeResidueNormValue q (cubicThetaCoordinateEquiv q (a,b)) = a^2-a*b+b^2 := by
  simp only [heckeResidueNormValue, Equiv.symm_apply_apply]

theorem heckeResidueNormValue_scalar (q : ℕ) [NeZero q] (r : CubicThetaResidue q) :
    heckeNormScalar q (heckeResidueNormValue q r) = r*cubicThetaResidueConjugation q r := by
  obtain ⟨⟨a,b⟩, rfl⟩ := (cubicThetaCoordinateEquiv q).surjective r
  obtain ⟨u, rfl⟩ := ZMod.intCast_surjective a
  obtain ⟨v, rfl⟩ := ZMod.intCast_surjective b
  rw [heckeResidueNormValue_coordinates]
  have hpoly : (u : ZMod q)^2-(u : ZMod q)*(v : ZMod q)+(v : ZMod q)^2 =
      (eisensteinIntegerNorm (u,v) : ZMod q) := by simp [eisensteinIntegerNorm]
  rw [hpoly, heckeNormScalar_intCast, cubicThetaCoordinateEquiv_intCast,
    cubicThetaResidueConjugation_mk, ← map_mul, coordinateElement_mul_conjugation]

def heckeResidueNorm (q : ℕ) [NeZero q] : CubicThetaResidue q →* ZMod q where
  toFun := heckeResidueNormValue q
  map_one' := by
    apply heckeNormScalar_injective q
    rw [heckeResidueNormValue_scalar, map_one, map_one, mul_one]
  map_mul' r s := by
    apply heckeNormScalar_injective q
    rw [map_mul, heckeResidueNormValue_scalar, heckeResidueNormValue_scalar,
      heckeResidueNormValue_scalar, map_mul]
    ring

theorem heckeResidueNorm_isUnit_iff (q : ℕ) [NeZero q] (r : CubicThetaResidue q) :
    IsUnit (heckeResidueNorm q r) ↔ IsUnit r := by
  constructor
  · intro h
    have hs := h.map (heckeNormScalar q)
    change IsUnit (heckeNormScalar q (heckeResidueNormValue q r)) at hs
    rw [heckeResidueNormValue_scalar] at hs
    exact (IsUnit.mul_iff.mp hs).1
  · exact fun h => h.map (heckeResidueNorm q)

theorem heckeInteger_mul_conjugation_eq_absNorm (z : EO) :
    z*heckeIntegerConjugation z = ((Ideal.span {z}).absNorm : EO) := by
  obtain ⟨⟨a,b⟩, rfl⟩ := HeckeCoordinates.coordinateElement_surjective z
  rw [coordinateElement_mul_conjugation]
  have hi : ((Ideal.span {HeckeFamily.coordinateElement a b}).absNorm : ℤ) =
      eisensteinIntegerNorm (a,b) := by
    change ((Ideal.span {ActualEisensteinCoordinates.eval a b}).absNorm : ℤ) = _
    rw [← ActualEisensteinCubic.qNat_eq_absNorm_span]
    change ((ShortDraftLatticeCount.q (ActualEisensteinCoordinates.coords
      (ActualEisensteinCoordinates.eval a b))).toNat : ℤ) = _
    rw [Int.toNat_of_nonneg (ShortDraftLatticeCount.qO_nonneg _),
      ShortDraftLatticeCount.coords_eval]
    rfl
  exact_mod_cast hi.symm

theorem heckeResidueNorm_mk (q : ℕ) [NeZero q] (z : EO) :
    heckeResidueNorm q (Ideal.Quotient.mk (cubicThetaRationalModulus q) z) =
      ((Ideal.span {z}).absNorm : ZMod q) := by
  apply heckeNormScalar_injective q
  change heckeNormScalar q (heckeResidueNormValue q _) = _
  rw [heckeResidueNormValue_scalar, cubicThetaResidueConjugation_mk, ← map_mul,
    heckeInteger_mul_conjugation_eq_absNorm, map_natCast, map_natCast]

end ArtinMatthews

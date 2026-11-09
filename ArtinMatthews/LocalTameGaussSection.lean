module

public import ArtinMatthews.QuadraticTameHilbert
public import ArtinMatthews.TameQuadraticSection


set_option backward.privateInPublic true
@[expose] public section

/-! An actual function on the multiplicative group of an odd local field,
constructed from its residue Gauss sum and canonical valuation-unit
decomposition.  Its cocycle is the local reciprocity Hilbert symbol.  This
does not identify it with an analytic Weil integral or assert an adelic
product formula. -/

namespace ArtinMatthews.QuadraticGauss

open KummerTheory LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open LocalClassFieldTheory.Kummer
open scoped ValuativeRel Classical

noncomputable section

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

local instance : Fintype 𝓀[K] := Fintype.ofFinite _

def tameUniformizer : Kˣ := inverseIntegerRingUniformizerFieldUnit K

theorem tameUniformizer_valuation :
    valuationMap K (Additive.ofMul (tameUniformizer K)) = 1 := by
  simpa only [tameUniformizer, valuationMap_apply] using
    v_inverseIntegerRingUniformizerFieldUnit K

def tameUnitFactor (x : Kˣ) : 𝒪[K]ˣ :=
  uniformizerUnitFactor K (tameUniformizer K) (tameUniformizer_valuation K) x

theorem tameUnitFactor_decomposition (x : Kˣ) :
    integerUnitsToFieldUnits K (tameUnitFactor K x) *
      tameUniformizer K ^ valuationMap K (Additive.ofMul x) = x :=
  uniformizerUnitFactor_mul_uniformizer_zpow K _ _ x

theorem tameUnitFactor_mul (x y : Kˣ) :
    tameUnitFactor K (x * y) = tameUnitFactor K x * tameUnitFactor K y := by
  apply integerUnitsToFieldUnits_injective K
  simp only [tameUnitFactor, map_mul, integerUnitsToFieldUnits_uniformizerUnitFactor,
    valuationMap_ofMul_mul, zpow_add]
  exact (div_mul_div_comm _ _ _ _).symm

def tameResidueUnit (x : Kˣ) : 𝓀[K]ˣ :=
  localUnitResidue K (tameUnitFactor K x)

theorem tameResidueUnit_mul (x y : Kˣ) :
    tameResidueUnit K (x * y) = tameResidueUnit K x * tameResidueUnit K y := by
  simp only [tameResidueUnit, localUnitResidue, tameUnitFactor_mul, map_mul]

theorem tameResidueUnit_sq (x : Kˣ) :
    tameResidueUnit K (x ^ 2) = tameResidueUnit K x ^ 2 := by
  simp only [pow_two, tameResidueUnit_mul]

theorem tameResidueUnit_uniformizer : tameResidueUnit K (tameUniformizer K) = 1 := by
  have hu : tameUnitFactor K (tameUniformizer K) = 1 := by
    apply integerUnitsToFieldUnits_injective K
    simp only [tameUnitFactor, integerUnitsToFieldUnits_uniformizerUnitFactor,
      tameUniformizer_valuation, zpow_one, map_one]
    exact div_self' _
  rw [tameResidueUnit, hu]
  simp only [localUnitResidue, map_one]

def localTameGaussSection (ψ : AddChar 𝓀[K] ℂ) (x : Kˣ) : ℂ :=
  tameSection ψ (valuationMap K (Additive.ofMul x)) (tameResidueUnit K x)

theorem localTameGaussSection_square_mul (ψ : AddChar 𝓀[K] ℂ) (x y : Kˣ) :
    localTameGaussSection K ψ (x * y ^ 2) = localTameGaussSection K ψ x := by
  unfold localTameGaussSection
  rw [valuationMap_ofMul_mul, valuationMap_ofMul_pow, tameResidueUnit_mul, tameResidueUnit_sq]
  exact tameSection_square_mul ψ _ _ _ _

variable (h2 : ValuativeRel.valuation K (((2 : ℕ+) : ℕ) : K) = 1)
  (hmu : (primitiveRoots ((2 : ℕ+) : ℕ) K).Nonempty)

theorem localQuadraticHilbert_unit_tameUniformizer (u : 𝒪[K]ˣ) :
    localQuadraticHilbert K h2 hmu (integerUnitsToFieldUnits K u) (tameUniformizer K) =
      residueCharacter 𝓀[K] (localUnitResidue K u : 𝓀[K]) :=
  localQuadraticHilbert_unit_uniformizer K h2 hmu (tameResidue_char_ne_two K h2) u

theorem localQuadraticHilbert_uniformizer_self :
    localQuadraticHilbert K h2 hmu (tameUniformizer K) (tameUniformizer K) =
      residueCharacter 𝓀[K] (-1) := by
  have hfield : integerUnitsToFieldUnits K (-1) = (-1 : Kˣ) := by
    apply Units.ext
    rfl
  have hresidue : (localUnitResidue K (-1) : 𝓀[K]) = -1 := by
    change IsLocalRing.residue 𝒪[K] (-1) = -1
    simp only [map_neg, map_one]
  have hm : localQuadraticHilbert K h2 hmu (tameUniformizer K) (-1) =
      residueCharacter 𝓀[K] (-1) := by
    rw [localQuadraticHilbert_symm]
    simpa only [tameUniformizer, hfield, hresidue] using
      localQuadraticHilbert_unit_uniformizer K h2 hmu (tameResidue_char_ne_two K h2) (-1)
  have hn := localQuadraticHilbert_neg_self K h2 hmu (tameUniformizer K)
  rw [← neg_one_mul (tameUniformizer K), localQuadraticHilbert_mul_right, hm] at hn
  apply mul_left_cancel₀ (residueCharacter_ne_zero (F := 𝓀[K])
    (neg_ne_zero.mpr one_ne_zero))
  calc
    _ = 1 := hn
    _ = residueCharacter 𝓀[K] (-1) * residueCharacter 𝓀[K] (-1) := by
      symm
      simpa only [pow_two] using
        residueCharacter_sq (F := 𝓀[K]) (neg_ne_zero.mpr one_ne_zero)

theorem localQuadraticHilbert_coordinates (u v : 𝒪[K]ˣ) (m n : ℤ) :
    localQuadraticHilbert K h2 hmu
      (integerUnitsToFieldUnits K u * tameUniformizer K ^ m)
      (integerUnitsToFieldUnits K v * tameUniformizer K ^ n) =
      tameDefect m n (localUnitResidue K u) (localUnitResidue K v) := by
  rw [localQuadraticHilbert_mul_left, localQuadraticHilbert_mul_right,
    localQuadraticHilbert_mul_right,
    localQuadraticHilbert_unit_unit, one_mul,
    localQuadraticHilbert_zpow_right, localQuadraticHilbert_zpow_left,
    localQuadraticHilbert_zpow_left, localQuadraticHilbert_zpow_right,
    localQuadraticHilbert_uniformizer_self,
    localQuadraticHilbert_unit_tameUniformizer K h2 hmu,
    localQuadraticHilbert_symm K h2 hmu (tameUniformizer K),
    localQuadraticHilbert_unit_tameUniformizer K h2 hmu,
    ← zpow_mul]
  unfold tameDefect
  rw [mul_comm n m]
  ring

theorem localQuadraticHilbert_eq_tameDefect (x y : Kˣ) :
    localQuadraticHilbert K h2 hmu x y =
      tameDefect (valuationMap K (Additive.ofMul x)) (valuationMap K (Additive.ofMul y))
        (tameResidueUnit K x) (tameResidueUnit K y) := by
  calc
    _ = localQuadraticHilbert K h2 hmu
        (integerUnitsToFieldUnits K (tameUnitFactor K x) *
          tameUniformizer K ^ valuationMap K (Additive.ofMul x))
        (integerUnitsToFieldUnits K (tameUnitFactor K y) *
          tameUniformizer K ^ valuationMap K (Additive.ofMul y)) := by
      rw [tameUnitFactor_decomposition, tameUnitFactor_decomposition]
    _ = _ := localQuadraticHilbert_coordinates K h2 hmu _ _ _ _

theorem localTameGaussSection_cocycle (ψ : AddChar 𝓀[K] ℂ) (hψ : ψ ≠ 1)
    (x y : Kˣ) :
    localTameGaussSection K ψ x * localTameGaussSection K ψ y =
      localQuadraticHilbert K h2 hmu x y * localTameGaussSection K ψ (x * y) := by
  rw [localQuadraticHilbert_eq_tameDefect]
  unfold localTameGaussSection
  rw [valuationMap_ofMul_mul, tameResidueUnit_mul]
  exact tameSection_cocycle (tameResidue_char_ne_two K h2) ψ hψ _ _ _ _

theorem localTameGaussSection_unit (ψ : AddChar 𝓀[K] ℂ) (u : 𝒪[K]ˣ) :
    localTameGaussSection K ψ (integerUnitsToFieldUnits K u) = 1 := by
  unfold localTameGaussSection tameSection
  rw [valuationMap_apply, v_integerUnitsToFieldUnits]
  norm_num

theorem localTameGaussSection_uniformizer (ψ : AddChar 𝓀[K] ℂ) :
    localTameGaussSection K ψ (tameUniformizer K) = residueIndex 𝓀[K] ψ := by
  unfold localTameGaussSection
  rw [tameUniformizer_valuation, tameResidueUnit_uniformizer, tameSection_uniformizer]

include h2 in
theorem localTameGaussSection_uniformizer_eq_sexticGamma
    (χ : MulChar 𝓀[K] ℂ) (hχ : orderOf χ = 6) (ψ : AddChar 𝓀[K] ℂ) :
    localTameGaussSection K ψ (tameUniformizer K) =
      VaryingKummerAnalytic.probeGaussGamma χ ψ 3 := by
  rw [localTameGaussSection_uniformizer]
  exact residueIndex_eq_sexticGamma χ hχ (tameResidue_char_ne_two K h2) ψ

include h2 in
theorem localG_eq_localTameGaussSection
    (χ : MulChar 𝓀[K] ℂ) (hχ : orderOf χ = 6) (ψ : AddChar 𝓀[K] ℂ) :
    VaryingKummerAnalytic.probeGaussLocalG χ ψ =
      (χ (4 : 𝓀[K]))⁻¹ * localTameGaussSection K ψ (tameUniformizer K) := by
  rw [localTameGaussSection_uniformizer]
  exact localG_eq_quadraticIndex χ hχ (tameResidue_char_ne_two K h2) ψ

include h2 in
theorem localTameGaussSection_fourth (ψ : AddChar 𝓀[K] ℂ) (hψ : ψ ≠ 1) (x : Kˣ) :
    localTameGaussSection K ψ x ^ 4 = 1 :=
  tameSection_fourth (tameResidue_char_ne_two K h2) ψ hψ _ _

end

end ArtinMatthews.QuadraticGauss

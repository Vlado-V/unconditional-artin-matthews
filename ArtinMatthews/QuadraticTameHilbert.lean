module

public import ArtinMatthews.QuadraticTameResidue
public import ClassFieldTheory.LocalClassFieldTheory.Kummer.PowerResidueTameFormula


set_option backward.privateInPublic true
@[expose] public section

/-! Compare the explicit quadratic residue signs with the actual local Artin
Hilbert symbol.  Its root-of-unity values are mapped canonically to complex
signs by reduction; no embedding of the local field into the complex numbers
is chosen. -/

namespace ArtinMatthews.QuadraticGauss

open KummerTheory LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open LocalClassFieldTheory.Kummer
open scoped ValuativeRel Classical

noncomputable section

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

local instance : Fintype 𝓀[K] := Fintype.ofFinite _

def localUnitResidue (u : 𝒪[K]ˣ) : 𝓀[K]ˣ :=
  residueUnitsConcreteEquiv K (integerUnitsToResidueUnits K u)

variable (h2 : ValuativeRel.valuation K (((2 : ℕ+) : ℕ) : K) = 1)

include h2 in
theorem tameResidue_char_ne_two : ringChar 𝓀[K] ≠ 2 := by
  have hu : IsUnit (2 : 𝒪[K]) := by
    apply (Valuation.integer.integers (ValuativeRel.valuation K)).isUnit_iff_valuation_eq_one.mpr
    exact h2
  have hn : (2 : 𝓀[K]) ≠ 0 := by
    simpa only [map_ofNat] using (IsLocalRing.residue_ne_zero_iff_isUnit (2 : 𝒪[K])).mpr hu
  intro he
  apply hn
  simpa only [he, Nat.cast_ofNat] using CharP.cast_eq_zero 𝓀[K] (ringChar 𝓀[K])

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
include h2 in
theorem tameField_char_ne_two : ringChar K ≠ 2 := by
  have hn : (2 : K) ≠ 0 := natCast_ne_zero_of_valuation_eq_one K 2 h2
  intro he
  apply hn
  simpa only [he, Nat.cast_ofNat] using CharP.cast_eq_zero K (ringChar K)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
include h2 in
theorem tamePrimitiveRoots : (primitiveRoots ((2 : ℕ+) : ℕ) K).Nonempty := by
  change (primitiveRoots 2 K).Nonempty
  exact ⟨-1, (mem_primitiveRoots (by decide : 0 < 2)).mpr
    (IsPrimitiveRoot.neg_one (ringChar K) (tameField_char_ne_two K h2))⟩

variable (hmu : (primitiveRoots ((2 : ℕ+) : ℕ) K).Nonempty)

def localQuadraticSign : nthRootsSubgroup K ((2 : ℕ+) : ℕ) →* ℂ :=
  (rootSign 𝓀[K]).comp (localNthRootsReductionEquiv K 2 h2 hmu).toMonoidHom

def localQuadraticHilbert (a b : Kˣ) : ℂ :=
  localQuadraticSign K h2 hmu
    (localHilbertSymbol K 2 (natCast_ne_zero_of_valuation_eq_one K 2 h2) hmu a b)

theorem localQuadraticSign_injective : Function.Injective (localQuadraticSign K h2 hmu) :=
  (rootSign_injective 𝓀[K]).comp (localNthRootsReductionEquiv K 2 h2 hmu).injective

theorem localQuadraticSign_sq (z : nthRootsSubgroup K ((2 : ℕ+) : ℕ)) :
    localQuadraticSign K h2 hmu z ^ 2 = 1 :=
  rootSign_sq 𝓀[K] _

theorem localQuadraticSign_tame (hF : ringChar 𝓀[K] ≠ 2) (u : 𝒪[K]ˣ) :
    localQuadraticSign K h2 hmu (localTamePowerResidueSymbol K 2 h2 hmu u) =
      residueCharacter 𝓀[K] (localUnitResidue K u : 𝓀[K]) := by
  change rootSign 𝓀[K]
    (localNthRootsReductionEquiv K 2 h2 hmu
      (localTamePowerResidueSymbol K 2 h2 hmu u)) = _
  rw [localNthRootsReductionEquiv_localTamePowerResidueSymbol]
  exact rootSign_powerResidue hF _ _

theorem localQuadraticHilbert_sq (a b : Kˣ) :
    localQuadraticHilbert K h2 hmu a b ^ 2 = 1 :=
  localQuadraticSign_sq K h2 hmu _

theorem localQuadraticHilbert_mul_left (a b c : Kˣ) :
    localQuadraticHilbert K h2 hmu (a * b) c =
      localQuadraticHilbert K h2 hmu a c * localQuadraticHilbert K h2 hmu b c := by
  change localQuadraticSign K h2 hmu
    (localHilbertSymbolHom K 2 (natCast_ne_zero_of_valuation_eq_one K 2 h2) hmu c
      (a * b)) = _
  rw [map_mul, map_mul]
  rfl

theorem localQuadraticHilbert_mul_right (a b c : Kˣ) :
    localQuadraticHilbert K h2 hmu a (b * c) =
      localQuadraticHilbert K h2 hmu a b * localQuadraticHilbert K h2 hmu a c := by
  unfold localQuadraticHilbert
  rw [localHilbertSymbol_mul_right, map_mul]

theorem localQuadraticHilbert_zpow_left (a b : Kˣ) (m : ℤ) :
    localQuadraticHilbert K h2 hmu (a ^ m) b =
      localQuadraticHilbert K h2 hmu a b ^ m := by
  change localQuadraticSign K h2 hmu
    (localHilbertSymbolHom K 2 (natCast_ne_zero_of_valuation_eq_one K 2 h2) hmu b
      (a ^ m)) = _
  rw [map_zpow, map_zpow]
  rfl

theorem localQuadraticHilbert_zpow_right (a b : Kˣ) (m : ℤ) :
    localQuadraticHilbert K h2 hmu a (b ^ m) =
      localQuadraticHilbert K h2 hmu a b ^ m := by
  unfold localQuadraticHilbert
  rw [localHilbertSymbol_zpow_right, map_zpow]

theorem localQuadraticHilbert_symm (a b : Kˣ) :
    localQuadraticHilbert K h2 hmu a b = localQuadraticHilbert K h2 hmu b a := by
  have hs := localQuadraticHilbert_sq K h2 hmu b a
  have hi : (localQuadraticHilbert K h2 hmu b a)⁻¹ =
      localQuadraticHilbert K h2 hmu b a := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [pow_two] using hs
  unfold localQuadraticHilbert at hi ⊢
  rw [localHilbertSymbol_skew, map_inv, hi]

theorem localQuadraticHilbert_neg_self (a : Kˣ) :
    localQuadraticHilbert K h2 hmu a (-a) = 1 := by
  unfold localQuadraticHilbert
  rw [localHilbertSymbol_neg_self, map_one]

theorem localQuadraticHilbert_unit (hF : ringChar 𝓀[K] ≠ 2)
    (u : 𝒪[K]ˣ) (x : Kˣ) :
    localQuadraticHilbert K h2 hmu (integerUnitsToFieldUnits K u) x =
      residueCharacter 𝓀[K] (localUnitResidue K u : 𝓀[K]) ^
        (-valuationMap K (Additive.ofMul x)) := by
  unfold localQuadraticHilbert
  rw [localHilbertSymbol_tame_formula K 2 h2 hmu u x, map_zpow,
    localQuadraticSign_tame K h2 hmu hF]

theorem localQuadraticHilbert_unit_unit (u v : 𝒪[K]ˣ) :
    localQuadraticHilbert K h2 hmu
      (integerUnitsToFieldUnits K u) (integerUnitsToFieldUnits K v) = 1 := by
  unfold localQuadraticHilbert
  rw [localHilbertSymbol_integerUnit_integerUnit_eq_one K 2 h2 hmu u v, map_one]

theorem localQuadraticHilbert_unit_uniformizer (hF : ringChar 𝓀[K] ≠ 2)
    (u : 𝒪[K]ˣ) :
    localQuadraticHilbert K h2 hmu
      (integerUnitsToFieldUnits K u) (inverseIntegerRingUniformizerFieldUnit K) =
      residueCharacter 𝓀[K] (localUnitResidue K u : 𝓀[K]) := by
  rw [localQuadraticHilbert_unit K h2 hmu hF, valuationMap_apply,
    v_inverseIntegerRingUniformizerFieldUnit]
  rw [zpow_neg_one]
  exact residueCharacter_inv (localUnitResidue K u).ne_zero

end

end ArtinMatthews.QuadraticGauss

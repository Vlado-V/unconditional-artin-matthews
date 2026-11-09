module

public import ArtinMatthews.QuadraticTameHilbert
public import ClassFieldTheory.LocalClassFieldTheory.Kummer.MathlibHilbertPairing


set_option backward.privateInPublic true
@[expose] public section

/-! For quadratic roots the norm-residue criterion determines the actual
complex sign. This identifies a transported Hilbert pairing without an
unproved normalization comparison or a choice of complex field embedding. -/

namespace ArtinMatthews.QuadraticWeil

open ClassFieldTheory KummerTheory LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField ArtinMatthews.QuadraticGauss
open LocalClassFieldTheory.Kummer
open scoped ValuativeRel Classical

noncomputable section

variable {K L : Type*} [Field K] [Field L]

theorem rootSign_eq_of_one_iff (z : rootsOfUnity 2 K) (w : rootsOfUnity 2 L)
    (h : z = 1 ↔ w = 1) : rootSign K z = rootSign L w := by
  simp only [rootSign_apply, h]

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

local instance normSignResidueFintype : Fintype 𝓀[K] := Fintype.ofFinite _

theorem localQuadraticHilbert_eq_pairingSign
    (h2 : ValuativeRel.valuation K (((2 : ℕ+) : ℕ) : K) = 1)
    (hmu : (primitiveRoots ((2 : ℕ+) : ℕ) K).Nonempty)
    (B : HilbertPairing K 2) (hB : B.IsLocalHilbertPairing) (a b : Kˣ) :
    localQuadraticHilbert K h2 hmu a b =
      rootSign K (B (powerClass K 2 a) (powerClass K 2 b)) := by
  let e : nthRootsSubgroup K 2 ≃* rootsOfUnity 2 𝓀[K] :=
    localNthRootsReductionEquiv K 2 h2 hmu
  let eK := nthRootsSubgroupEquivRootsOfUnity K 2
  let z : nthRootsSubgroup K 2 := LocalClassFieldTheory.Kummer.localHilbertSymbol K 2
    (natCast_ne_zero_of_valuation_eq_one K 2 h2) hmu a b
  change rootSign 𝓀[K] (e z) = rootSign K (B (powerClass K 2 a) (powerClass K 2 b))
  apply rootSign_eq_of_one_iff
  rw [e.map_eq_one_iff]
  have hnorm : eK z = 1 ↔ IsKummerNorm K 2 a b :=
    ClassFieldTheory.localHilbertSymbol_eq_one_iff_isKummerNorm K 2
      (natCast_ne_zero_of_valuation_eq_one K 2 h2) hmu a b
  have hn : z = 1 ↔ IsKummerNorm K 2 a b := by
    rwa [eK.map_eq_one_iff] at hnorm
  exact hn.trans (hB.2.2.2 a b).symm

end

end ArtinMatthews.QuadraticWeil

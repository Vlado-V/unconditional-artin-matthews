module

public import ArtinMatthews.KummerFrobeniusResidue


set_option backward.privateInPublic true
@[expose] public section

/-! Arithmetic Frobenius on a sixth root of an arbitrary integral unit
at an exterior prime, by the defining residue congruence. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain AlgebraicNumberTheory.PowerResidueSymbols
open VaryingKummerAnalytic.GaloisIdealCharacter
open scoped NumberField Classical
noncomputable section

attribute [local instance] Ideal.Quotient.field

theorem integralPowerRoot_eq_of_reduction_eq {E : Type} [Field E]
    (Q : Ideal (𝓞 E)) [Q.IsMaximal] (n : ℕ) (hn : 0 < n) (hnQ : (n : 𝓞 E) ∉ Q)
    {x y : 𝓞 E} (hp : x ^ n = y ^ n) (hyQ : Ideal.Quotient.mk Q y ≠ 0)
    (hred : Ideal.Quotient.mk Q x = Ideal.Quotient.mk Q y) : x = y := by
  have hy0 : (y : E) ≠ 0 := by
    intro h
    exact hyQ (by rw [show y = 0 from Subtype.ext h, map_zero])
  let t : E := (x : E) / (y : E)
  have ht : t ^ n = 1 := by
    have h := congrArg (fun r : 𝓞 E => (r : E)) hp
    change (x : E) ^ n = (y : E) ^ n at h
    dsimp only [t]
    rw [div_pow, h, div_self (pow_ne_zero _ hy0)]
  let a : 𝓞 E := ⟨t, powerRoot_isIntegral hn (a := 1) (by simpa only [Int.cast_one] using ht)⟩
  have ha : a ^ n = 1 := Subtype.ext ht
  have hay : a * y = x := Subtype.ext (div_mul_cancel₀ _ hy0)
  have haRed : Ideal.Quotient.mk Q a = 1 := by
    apply mul_right_cancel₀ hyQ
    rw [← map_mul, hay, hred, one_mul]
  have ha1 := power_unity_eq_one_of_reduction_eq_one Q hnQ ha haRed
  rw [ha1, one_mul] at hay
  exact hay.symm

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [FiniteDimensional F E] [IsGalois F E]

local instance sourceFrobeniusResidueFintype (P : HeightOneSpectrum (𝓞 F)) :
    Fintype (𝓞 F ⧸ P.asIdeal) := Fintype.ofFinite _

theorem frobenius_sixthRoot_integralUnit
    (P : HeightOneSpectrum (𝓞 F)) (hsix : (6 : 𝓞 F) ∉ P.asIdeal)
    (hmu : (primitiveRoots 6 F).Nonempty)
    (hN : (Ideal.absNorm P.asIdeal).Coprime 6)
    (x : 𝓞 F) (hx : x ∉ P.asIdeal)
    (α : E) (hα : α ^ 6 = algebraMap F E (x : F)) :
    primeFrobenius F E P α / α =
      algebraMap F E (((primeIdealPowerResidueSymbol F P 6 hmu hN x hx :
        rootsOfUnity 6 (𝓞 F)) : (𝓞 F)ˣ) : 𝓞 F) := by
  let Q := primeAbove F E P
  let : Q.val.IsPrime := Q.property.1
  let : Q.val.IsMaximal := Q.property.1.isMaximal (primeAbove_ne_bot F E P)
  have hQ : Q.val.under (𝓞 F) = P.asIdeal := Q.property.2.over.symm
  have h6Q : (6 : 𝓞 E) ∉ Q.val := by
    intro h
    apply hsix
    rw [← hQ]
    change algebraMap (𝓞 F) (𝓞 E) 6 ∈ Q.val
    simpa only [map_ofNat] using h
  let z := primeIdealPowerResidueSymbol F P 6 hmu hN x hx
  let z₀ : 𝓞 F := ((z : (𝓞 F)ˣ) : 𝓞 F)
  have hz : z₀ ^ 6 = 1 := congrArg Units.val ((mem_rootsOfUnity 6 _).mp z.property)
  let xE := algebraMap (𝓞 F) (𝓞 E) x
  let r : 𝓞 E := ⟨α, IsIntegral.of_pow (by decide : 0 < 6)
    (hα.symm ▸ xE.property)⟩
  have hr : r ^ 6 = xE := Subtype.ext hα
  let zE := algebraMap (𝓞 F) (𝓞 E) z₀
  have hzE : zE ^ 6 = 1 := by
    dsimp only [zE]
    rw [← map_pow, hz, map_one]
  have hσr : (primeFrobenius F E P • r) ^ 6 = xE := by
    apply Subtype.ext
    change (primeFrobenius F E P α) ^ 6 = algebraMap F E (x : F)
    rw [← map_pow, hα, AlgEquiv.commutes]
  have hyr : (r * zE) ^ 6 = xE := by rw [mul_pow, hr, hzE, mul_one]
  have hxQ : Ideal.Quotient.mk Q.val xE ≠ 0 := by
    intro h
    apply hx
    have hm := Ideal.Quotient.eq_zero_iff_mem.mp h
    change x ∈ Q.val.under (𝓞 F) at hm
    exact hQ ▸ hm
  have hyr0 : Ideal.Quotient.mk Q.val (r * zE) ≠ 0 := by
    intro hy
    have h := congrArg (Ideal.Quotient.mk Q.val) hyr
    rw [map_pow, hy, zero_pow (by decide : (6 : ℕ) ≠ 0)] at h
    exact hxQ h.symm
  let d := (Ideal.absNorm P.asIdeal - 1) / 6
  have hzP : Ideal.Quotient.mk P.asIdeal z₀ = (Ideal.Quotient.mk P.asIdeal x) ^ d := by
    have h := rootsOfUnityReductionEquiv_primeIdealPowerResidueSymbol F P 6 hmu hN x hx
    have hv := congrArg (fun t : rootsOfUnity 6 (𝓞 F ⧸ P.asIdeal) =>
      ((t : (𝓞 F ⧸ P.asIdeal)ˣ) : 𝓞 F ⧸ P.asIdeal)) h
    change Ideal.Quotient.mk P.asIdeal z₀ =
      (Ideal.Quotient.mk P.asIdeal x) ^ ((Fintype.card (𝓞 F ⧸ P.asIdeal) - 1) / 6) at hv
    simpa only [card_primeIdealResidueField, d] using hv
  have hzmem : z₀ - x ^ d ∈ P.asIdeal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_sub, map_pow, sub_eq_zero] using hzP
  have hzQ : Ideal.Quotient.mk Q.val zE = (Ideal.Quotient.mk Q.val xE) ^ d := by
    have hm : algebraMap (𝓞 F) (𝓞 E) (z₀ - x ^ d) ∈ Q.val := by
      change z₀ - x ^ d ∈ Q.val.under (𝓞 F)
      rwa [hQ]
    have he := Ideal.Quotient.eq_zero_iff_mem.mpr hm
    simpa only [map_sub, map_pow, sub_eq_zero] using he
  have hd : (6 : ℕ) ∣ Ideal.absNorm P.asIdeal - 1 :=
    dvd_absNorm_sub_one_of_primitiveRoots F P 6 hmu hN
  have hnormpos : 0 < Ideal.absNorm P.asIdeal :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot)
  have hexp : 6 * d + 1 = Ideal.absNorm P.asIdeal := by
    dsimp only [d]
    rw [Nat.mul_div_cancel' hd, Nat.sub_add_cancel (Nat.succ_le_iff.mpr hnormpos)]
  have hred : Ideal.Quotient.mk Q.val (primeFrobenius F E P • r) =
      Ideal.Quotient.mk Q.val (r * zE) := by
    have hf := (primeFrobenius_spec F E P).mk_apply r
    have hcard : Nat.card (𝓞 F ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [hQ, hcard] at hf
    have hf' : Ideal.Quotient.mk Q.val (primeFrobenius F E P • r) =
        (Ideal.Quotient.mk Q.val r) ^ Ideal.absNorm P.asIdeal := by
      simpa only [MulSemiringAction.toAlgHom_apply] using hf
    rw [hf', map_mul, hzQ, ← hexp, pow_succ', pow_mul,
      ← map_pow, hr]
  have he := integralPowerRoot_eq_of_reduction_eq Q.val 6 (by decide) h6Q (hσr.trans hyr.symm) hyr0 hred
  have hval := congrArg (fun t : 𝓞 E => (t : E)) he
  have hα0 : α ≠ 0 := by
    intro h
    apply hxQ
    rw [← hr, show r = 0 from Subtype.ext h, zero_pow (by decide : (6 : ℕ) ≠ 0), map_zero]
  change primeFrobenius F E P α = α * algebraMap F E (z₀ : F) at hval
  rw [hval, mul_div_cancel_left₀ _ hα0]

end
end ArtinMatthews

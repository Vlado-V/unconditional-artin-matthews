module

public import ArtinMatthews.KummerFrobeniusResidue


set_option backward.privateInPublic true
@[expose] public section

/-! Arithmetic Frobenius on a radical of an arbitrary prime-to-prime
integral radicand has the literal power-residue value. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain AlgebraicNumberTheory.PowerResidueSymbols
open VaryingKummerAnalytic.GaloisIdealCharacter
open scoped NumberField Classical
noncomputable section

variable {L : Type} [Field L] [NumberField L]

omit [NumberField L] in
theorem integralRadicals_eq_of_reduction {n : ℕ} (hn : 0 < n)
    (Q : Ideal (𝓞 L)) [Q.IsMaximal] (hnQ : (n : 𝓞 L) ∉ Q)
    {x y : 𝓞 L} (hxy : x ^ n = y ^ n)
    (hy : Ideal.Quotient.mk Q y ≠ 0) (hred : Ideal.Quotient.mk Q x = Ideal.Quotient.mk Q y) :
    x = y := by
  have hy' : (y : L) ≠ 0 := by
    intro hz
    exact hy (by rw [show y = 0 from Subtype.ext hz, map_zero])
  let r := (x : L) / y
  have hr : r ^ n = 1 := by
    change ((x : L) / y) ^ n = 1
    rw [div_pow, show (x : L) ^ n = (y : L) ^ n from congrArg (fun z : 𝓞 L => (z : L)) hxy,
      div_self (pow_ne_zero _ hy')]
  let z : 𝓞 L := ⟨r, powerRoot_isIntegral hn (a := 1) (by simpa using hr)⟩
  have hz : z ^ n = 1 := Subtype.ext hr
  have hzy : z * y = x := Subtype.ext (div_mul_cancel₀ _ hy')
  have hzred : Ideal.Quotient.mk Q z = 1 := by
    apply mul_right_cancel₀ hy
    rw [← map_mul, hzy, hred, one_mul]
  have hone := power_unity_eq_one_of_reduction_eq_one Q hnQ hz hzred
  rwa [hone, one_mul, eq_comm] at hzy

variable (F : Type) [Field F] [NumberField F]
variable [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

local instance integralFrobeniusResidueFintype (P : HeightOneSpectrum (𝓞 F)) :
    Fintype (𝓞 F ⧸ P.asIdeal) := Fintype.ofFinite _

theorem frobenius_integral_radical_residue (n : ℕ+) (P : HeightOneSpectrum (𝓞 F))
    (hnP : ((n : ℕ) : 𝓞 F) ∉ P.asIdeal) (hmu : (primitiveRoots n F).Nonempty)
    (hN : (Ideal.absNorm P.asIdeal).Coprime n) (a : 𝓞 F) (ha : a ∉ P.asIdeal)
    (x : L) (hx : x ^ (n : ℕ) = algebraMap (𝓞 F) L a) :
    primeFrobenius F L P x / x =
      algebraMap (𝓞 F) L (((primeIdealPowerResidueSymbol F P n hmu hN a ha :
        rootsOfUnity n (𝓞 F)) : (𝓞 F)ˣ) : 𝓞 F) := by
  have hn : 0 < (n : ℕ) := n.pos
  let Q := primeAbove F L P
  let : Q.val.IsPrime := Q.property.1
  let : Q.val.IsMaximal := Q.property.1.isMaximal (primeAbove_ne_bot F L P)
  have hQ : Q.val.under (𝓞 F) = P.asIdeal := Q.property.2.over.symm
  have hnQ : ((n : ℕ) : 𝓞 L) ∉ Q.val := by
    intro h
    apply hnP
    rw [← hQ]
    change algebraMap (𝓞 F) (𝓞 L) ((n : ℕ) : 𝓞 F) ∈ Q.val
    rwa [map_natCast]
  let aL := algebraMap (𝓞 F) (𝓞 L) a
  have haL : aL ∉ Q.val := by
    change a ∉ Q.val.under (𝓞 F)
    rwa [hQ]
  let r : 𝓞 L := ⟨x, IsIntegral.of_pow hn (by
    rw [hx]
    exact aL.property)⟩
  have hr : r ^ (n : ℕ) = aL := Subtype.ext hx
  let z := primeIdealPowerResidueSymbol F P n hmu hN a ha
  let z₀ : 𝓞 F := ((z : (𝓞 F)ˣ) : 𝓞 F)
  let zL := algebraMap (𝓞 F) (𝓞 L) z₀
  have hz : z₀ ^ (n : ℕ) = 1 := congrArg Units.val ((mem_rootsOfUnity n _).mp z.property)
  have hzL : zL ^ (n : ℕ) = 1 := by
    change (algebraMap (𝓞 F) (𝓞 L) z₀) ^ (n : ℕ) = 1
    rw [← map_pow, hz, map_one]
  have hσr : (primeFrobenius F L P • r) ^ (n : ℕ) = aL := by
    apply Subtype.ext
    change (primeFrobenius F L P x) ^ (n : ℕ) = algebraMap (𝓞 F) L a
    rw [← map_pow, hx, IsScalarTower.algebraMap_apply (𝓞 F) F L,
      (primeFrobenius F L P).commutes]
  have hrz : (r * zL) ^ (n : ℕ) = aL := by rw [mul_pow, hr, hzL, mul_one]
  have hrz₀ : Ideal.Quotient.mk Q.val (r * zL) ≠ 0 := by
    intro hzero
    have h := congrArg (Ideal.Quotient.mk Q.val) hrz
    rw [map_pow, hzero, zero_pow hn.ne'] at h
    exact haL (Ideal.Quotient.eq_zero_iff_mem.mp h.symm)
  let k := (Ideal.absNorm P.asIdeal - 1) / (n : ℕ)
  have hzP : Ideal.Quotient.mk P.asIdeal z₀ = Ideal.Quotient.mk P.asIdeal a ^ k := by
    have h := rootsOfUnityReductionEquiv_primeIdealPowerResidueSymbol F P n hmu hN a ha
    have hv := congrArg (fun t : rootsOfUnity n (𝓞 F ⧸ P.asIdeal) =>
      ((t : (𝓞 F ⧸ P.asIdeal)ˣ) : 𝓞 F ⧸ P.asIdeal)) h
    change Ideal.Quotient.mk P.asIdeal z₀ =
      (Ideal.Quotient.mk P.asIdeal a) ^ ((Fintype.card (𝓞 F ⧸ P.asIdeal) - 1) / (n : ℕ)) at hv
    simpa only [card_primeIdealResidueField] using hv
  have hzP' : z₀ - a ^ k ∈ P.asIdeal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_pow, hzP, sub_self]
  have hzQ : Ideal.Quotient.mk Q.val zL = Ideal.Quotient.mk Q.val aL ^ k := by
    have hm : algebraMap (𝓞 F) (𝓞 L) (z₀ - a ^ k) ∈ Q.val := by
      change z₀ - a ^ k ∈ Q.val.under (𝓞 F)
      rwa [hQ]
    have he := Ideal.Quotient.eq_zero_iff_mem.mpr hm
    simpa only [map_sub, map_pow, sub_eq_zero] using he
  have hd : (n : ℕ) ∣ Ideal.absNorm P.asIdeal - 1 :=
    dvd_absNorm_sub_one_of_primitiveRoots F P n hmu hN
  have hpos : 0 < Ideal.absNorm P.asIdeal :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot)
  have hpower : (n : ℕ) * k + 1 = Ideal.absNorm P.asIdeal := by
    have hdiv : (n : ℕ) * k = Ideal.absNorm P.asIdeal - 1 := Nat.mul_div_cancel' hd
    omega
  have hred : Ideal.Quotient.mk Q.val (primeFrobenius F L P • r) =
      Ideal.Quotient.mk Q.val (r * zL) := by
    have hf := (primeFrobenius_spec F L P).mk_apply r
    have hcard : Nat.card (𝓞 F ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [hQ, hcard] at hf
    have hf' : Ideal.Quotient.mk Q.val (primeFrobenius F L P • r) =
        (Ideal.Quotient.mk Q.val r) ^ Ideal.absNorm P.asIdeal := by
      simpa only [MulSemiringAction.toAlgHom_apply] using hf
    rw [hf', map_mul, hzQ, ← hpower, pow_succ', pow_mul, ← map_pow, hr]
  have he := integralRadicals_eq_of_reduction hn Q.val hnQ (hσr.trans hrz.symm) hrz₀ hred
  have hx₀ : x ≠ 0 := by
    intro h
    apply hrz₀
    rw [show r = 0 from Subtype.ext h, zero_mul, map_zero]
  have hσ := congrArg (fun v : 𝓞 L => (v : L)) he
  change primeFrobenius F L P x = x * algebraMap (𝓞 F) L z₀ at hσ
  rw [hσ, mul_div_cancel_left₀ _ hx₀]

end
end ArtinMatthews

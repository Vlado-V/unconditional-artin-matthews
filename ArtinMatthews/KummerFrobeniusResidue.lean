module

public import ArtinMatthews.ArtinFrobeniusIdealCharacter
public import ArtinMatthews.KummerRootReduction
public import ClassFieldTheory.AlgebraicNumberTheory.PowerResidueSymbols.Ideal


set_option backward.privateInPublic true
@[expose] public section

/-! Arithmetic Frobenius on an actual sixth root of four has the
canonical sixth-power residue value. The proof uses the defining
Frobenius congruence and injectivity of prime-to-characteristic root
reduction, rather than a prescribed prime character value. -/

namespace ArtinMatthews

open NumberField IsDedekindDomain
open AlgebraicNumberTheory.PowerResidueSymbols
open VaryingKummerAnalytic.GaloisIdealCharacter
open scoped NumberField Classical

noncomputable section

variable (F : Type) [Field F] [NumberField F]

local instance frobeniusResidueFintype (P : HeightOneSpectrum (𝓞 F)) :
    Fintype (𝓞 F ⧸ P.asIdeal) := Fintype.ofFinite _

omit [NumberField F] in
theorem four_not_mem_of_six_not_mem (P : HeightOneSpectrum (𝓞 F))
    (hsix : (6 : 𝓞 F) ∉ P.asIdeal) : (4 : 𝓞 F) ∉ P.asIdeal := by
  intro h4
  have h22 : (2 : 𝓞 F) * 2 ∈ P.asIdeal := by norm_num at h4 ⊢; exact h4
  have h2 : (2 : 𝓞 F) ∈ P.asIdeal :=
    P.isPrime.mem_or_mem h22 |>.elim id id
  apply hsix
  have h6 := P.asIdeal.mul_mem_left (3 : 𝓞 F) h2
  norm_num at h6 ⊢
  exact h6

variable (E : Type) [Field E] [NumberField E] [Algebra F E]
  [FiniteDimensional F E] [IsGalois F E]

theorem frobenius_sixthRoot_four
    (P : HeightOneSpectrum (𝓞 F)) (hsix : (6 : 𝓞 F) ∉ P.asIdeal)
    (hmu : (primitiveRoots 6 F).Nonempty)
    (hN : (Ideal.absNorm P.asIdeal).Coprime 6)
    (α : E) (hα : α ^ 6 = 4) :
    primeFrobenius F E P α / α =
      algebraMap F E (((primeIdealPowerResidueSymbol F P 6 hmu hN 4
        (four_not_mem_of_six_not_mem F P hsix) : rootsOfUnity 6 (𝓞 F)) : (𝓞 F)ˣ) : 𝓞 F) := by
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
  let z := primeIdealPowerResidueSymbol F P 6 hmu hN 4
    (four_not_mem_of_six_not_mem F P hsix)
  let z₀ : 𝓞 F := ((z : (𝓞 F)ˣ) : 𝓞 F)
  have hz : z₀ ^ 6 = 1 := congrArg Units.val ((mem_rootsOfUnity 6 _).mp z.property)
  let r : 𝓞 E := ⟨α, powerRoot_isIntegral (by decide : 0 < 6) (a := 4)
    (by simpa only [Int.cast_ofNat] using hα)⟩
  have hr : r ^ 6 = 4 := Subtype.ext hα
  let zE : 𝓞 E := algebraMap (𝓞 F) (𝓞 E) z₀
  have hzE : zE ^ 6 = 1 := by
    dsimp only [zE]
    rw [← map_pow, hz, map_one]
  have hσr : (primeFrobenius F E P • r) ^ 6 = 4 := by
    apply Subtype.ext
    change (primeFrobenius F E P α) ^ 6 = 4
    rw [← map_pow, hα, map_ofNat]
  have hyr : (r * zE) ^ 6 = 4 := by rw [mul_pow, hr, hzE, mul_one]
  have h2Q : (2 : 𝓞 E) ∉ Q.val := by
    intro h
    apply h6Q
    have hm := Q.val.mul_mem_left (3 : 𝓞 E) h
    norm_num at hm ⊢
    exact hm
  have h4Q : (4 : 𝓞 E ⧸ Q.val) ≠ 0 := by
    have h2 : (2 : 𝓞 E ⧸ Q.val) ≠ 0 := by
      simpa only [← map_ofNat (Ideal.Quotient.mk Q.val), ne_eq,
        Ideal.Quotient.eq_zero_iff_mem] using h2Q
    convert pow_ne_zero 2 h2 using 1
    norm_num
  have hyr0 : Ideal.Quotient.mk Q.val (r * zE) ≠ 0 := by
    intro hy
    have hp := congrArg (Ideal.Quotient.mk Q.val) hyr
    rw [map_pow, hy, zero_pow (by decide : 6 ≠ 0), map_ofNat] at hp
    exact h4Q hp.symm
  have hzP : Ideal.Quotient.mk P.asIdeal z₀ =
      (4 : 𝓞 F ⧸ P.asIdeal) ^ ((Ideal.absNorm P.asIdeal - 1) / 6) := by
    have h := rootsOfUnityReductionEquiv_primeIdealPowerResidueSymbol F P 6 hmu hN
      4 (four_not_mem_of_six_not_mem F P hsix)
    have hv := congrArg (fun t : rootsOfUnity 6 (𝓞 F ⧸ P.asIdeal) =>
      ((t : (𝓞 F ⧸ P.asIdeal)ˣ) : 𝓞 F ⧸ P.asIdeal)) h
    change Ideal.Quotient.mk P.asIdeal z₀ =
      (Ideal.Quotient.mk P.asIdeal 4) ^ ((Fintype.card (𝓞 F ⧸ P.asIdeal) - 1) / 6) at hv
    simpa only [map_ofNat, card_primeIdealResidueField] using hv
  have hzmem : z₀ - 4 ^ ((Ideal.absNorm P.asIdeal - 1) / 6) ∈ P.asIdeal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_sub, map_pow, map_ofNat, sub_eq_zero] using hzP
  have hzQ : Ideal.Quotient.mk Q.val zE =
      (4 : 𝓞 E ⧸ Q.val) ^ ((Ideal.absNorm P.asIdeal - 1) / 6) := by
    have hm : algebraMap (𝓞 F) (𝓞 E)
        (z₀ - 4 ^ ((Ideal.absNorm P.asIdeal - 1) / 6)) ∈ Q.val := by
      change z₀ - 4 ^ ((Ideal.absNorm P.asIdeal - 1) / 6) ∈ Q.val.under (𝓞 F)
      rwa [hQ]
    have he := Ideal.Quotient.eq_zero_iff_mem.mpr hm
    simpa only [map_sub, map_pow, map_ofNat, sub_eq_zero] using he
  have hd : 6 ∣ Ideal.absNorm P.asIdeal - 1 :=
    dvd_absNorm_sub_one_of_primitiveRoots F P 6 hmu hN
  have hnormpos : 0 < Ideal.absNorm P.asIdeal :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot)
  have hexp : 6 * ((Ideal.absNorm P.asIdeal - 1) / 6) + 1 = Ideal.absNorm P.asIdeal := by
    have hdiv := Nat.mul_div_cancel' hd
    omega
  have hred : Ideal.Quotient.mk Q.val (primeFrobenius F E P • r) =
      Ideal.Quotient.mk Q.val (r * zE) := by
    have hf := (primeFrobenius_spec F E P).mk_apply r
    have hcard : Nat.card (𝓞 F ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [hQ, hcard] at hf
    have hf' : Ideal.Quotient.mk Q.val (primeFrobenius F E P • r) =
        (Ideal.Quotient.mk Q.val r) ^ Ideal.absNorm P.asIdeal := by
      simpa only [MulSemiringAction.toAlgHom_apply] using hf
    rw [hf', map_mul, hzQ]
    have hp : (Ideal.Quotient.mk Q.val r) ^ 6 = (4 : 𝓞 E ⧸ Q.val) := by
      simpa only [map_pow, map_ofNat] using congrArg (Ideal.Quotient.mk Q.val) hr
    calc
      _ = (Ideal.Quotient.mk Q.val r) ^
          (6 * ((Ideal.absNorm P.asIdeal - 1) / 6) + 1) :=
        congrArg (fun n : ℕ => (Ideal.Quotient.mk Q.val r) ^ n) hexp.symm
      _ = (Ideal.Quotient.mk Q.val r) * ((Ideal.Quotient.mk Q.val r) ^ 6) ^
          ((Ideal.absNorm P.asIdeal - 1) / 6) := by rw [pow_succ, pow_mul]; ring
      _ = _ := by rw [hp]
  have he := powerRoot_eq_of_reduction_eq (q := 6) (a := 4) (by decide) Q.val h6Q
    (by simpa only [Int.cast_ofNat] using hσr) (by simpa only [Int.cast_ofNat] using hyr) hyr0 hred
  have hval := congrArg (fun t : 𝓞 E => (t : E)) he
  have hα0 : α ≠ 0 := by intro h; norm_num [h] at hα
  change primeFrobenius F E P α = α * algebraMap F E (z₀ : F) at hval
  rw [hval, mul_div_cancel_left₀ _ hα0]

end

end ArtinMatthews

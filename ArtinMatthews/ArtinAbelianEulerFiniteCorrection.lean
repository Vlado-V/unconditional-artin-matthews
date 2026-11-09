module

public import ArtinMatthews.ArtinAbelianGlobalEuler


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite-prime corrections for imprimitive ray Euler products.
The correction is holomorphic and nonzero throughout Re(s)>0. -/
set_option maxHeartbeats 800000
noncomputable section
namespace ArtinMatthews.AbelianLocal
open OAI.PrimeDegreePackets ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField IsMulCommutative Classical BigOperators

private theorem finite_character_norm_one {G : Type*} [Group G] [Finite G]
    (χ : G →* ℂˣ) (g : G) : ‖(χ g : ℂ)‖ = 1 := by
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Nat.card_pos (α := G)).ne').mp
  have h : χ g ^ Nat.card G = 1 := by rw [← map_pow, pow_card_eq_one', map_one]
  have hn := congrArg (fun z : ℂˣ => ‖(z : ℂ)‖) h
  simpa only [Units.val_pow_eq_pow_val, norm_pow, Units.val_one, norm_one] using hn

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [IsAbelianGalois F E]

private theorem heightOne_norm_two_le (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    2 ≤ Ideal.absNorm P.asIdeal := by
  have hn : Ideal.absNorm P.asIdeal ≠ 0 := by
    rw [Ideal.absNorm_ne_zero_iff]
    exact Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
  have h1 : Ideal.absNorm P.asIdeal ≠ 1 := by
    intro h
    exact P.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  omega

private theorem twisted_normPower_lt_one (χ : Gal(E/F) →* ℂˣ)
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {s : ℂ} (hs : 0 < s.re) :
    ‖(χ (abelianPrimeFrobenius F E P) : ℂ) * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)‖ < 1 := by
  have hN : 1 < (Ideal.absNorm P.asIdeal : ℝ) := by
    exact_mod_cast (show 1 < Ideal.absNorm P.asIdeal from heightOne_norm_two_le F P)
  rw [norm_mul, finite_character_norm_one, one_mul, ← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg hN (neg_neg_of_pos hs)

theorem abelianArtinLocalFactor_denominator_ne_zero (χ : Gal(E/F) →* ℂˣ)
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {s : ℂ} (hs : 0 < s.re) :
    1 - (χ (abelianPrimeFrobenius F E P) : ℂ) * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s) ≠ 0 := by
  have hn := twisted_normPower_lt_one F E χ P hs
  intro h
  rw [← sub_eq_zero.mp h, norm_one] at hn
  exact (lt_irrefl _ hn)

theorem abelianArtinLocalFactor_ne_zero (χ : Gal(E/F) →* ℂˣ)
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {s : ℂ} (hs : 0 < s.re) :
    abelianArtinLocalFactor F E χ P s ≠ 0 := by
  unfold abelianArtinLocalFactor
  split_ifs
  · exact inv_ne_zero (abelianArtinLocalFactor_denominator_ne_zero F E χ P hs)
  · exact one_ne_zero

theorem abelianArtinLocalFactor_differentiableOn (χ : Gal(E/F) →* ℂˣ)
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    DifferentiableOn ℂ (abelianArtinLocalFactor F E χ P) {s : ℂ | 0 < s.re} := by
  unfold abelianArtinLocalFactor
  split_ifs with hI
  ·
    intro s hs
    have hN : (Ideal.absNorm P.asIdeal : ℂ) ≠ 0 := by
      exact_mod_cast (show Ideal.absNorm P.asIdeal ≠ 0 by
        have hn := heightOne_norm_two_le F P
        omega)
    have hd : Differentiable ℂ (fun z : ℂ => (Ideal.absNorm P.asIdeal : ℂ) ^ (-z)) :=
      differentiable_id.neg.const_cpow (Or.inl hN)
    exact (((differentiableAt_const (1 : ℂ)).sub
      ((hd s).const_mul _)).inv (abelianArtinLocalFactor_denominator_ne_zero F E χ P hs)).differentiableWithinAt
  · change DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) {s : ℂ | 0 < s.re}
    exact differentiableOn_const (1 : ℂ)

def abelianArtinFiniteCorrection (χ : Gal(E/F) →* ℂˣ) (S : Finset Nat.Primes) (s : ℂ) : ℂ :=
  ∏ p ∈ S, abelianArtinRationalFactor F E χ p s

def abelianArtinDeletedEulerProduct (χ : Gal(E/F) →* ℂˣ) (S : Finset Nat.Primes) (s : ℂ) : ℂ :=
  ∏' p : {p : Nat.Primes // p ∉ S}, abelianArtinRationalFactor F E χ p.val s

theorem abelianArtinFiniteCorrection_ne_zero (χ : Gal(E/F) →* ℂˣ)
    (S : Finset Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    abelianArtinFiniteCorrection F E χ S s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p _
  apply Finset.prod_ne_zero_iff.mpr
  intro P _
  exact abelianArtinLocalFactor_ne_zero F E χ _ hs

theorem abelianArtinFiniteCorrection_differentiableOn (χ : Gal(E/F) →* ℂˣ)
    (S : Finset Nat.Primes) :
    DifferentiableOn ℂ (abelianArtinFiniteCorrection F E χ S) {s : ℂ | 0 < s.re} := by
  apply DifferentiableOn.fun_finsetProd
  intro p _
  apply DifferentiableOn.fun_finsetProd
  intro P _
  exact abelianArtinLocalFactor_differentiableOn F E χ _

theorem abelianArtinDeletedEulerProduct_hasProd (χ : Gal(E/F) →* ℂˣ)
    (S : Finset Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : {p : Nat.Primes // p ∉ S} => abelianArtinRationalFactor F E χ p.val s)
      (abelianArtinDeletedEulerProduct F E χ S s) := by
  have h := ((abelianArtinRationalLog_summable F E χ hs).subtype (fun p => p ∉ S)).hasSum.cexp
  have he : HasProd
      (fun p : {p : Nat.Primes // p ∉ S} => abelianArtinRationalFactor F E χ p.val s)
      (Complex.exp (∑' p : {p : Nat.Primes // p ∉ S}, abelianArtinRationalLog F E χ p.val s)) :=
    h.congr_fun (fun p => (abelianArtinRationalLog_exp F E χ p.val hs).symm)
  exact he.multipliable.hasProd

/-- Restore exactly the finite Euler factors excluded by an imprimitive ray modulus. -/
theorem abelianArtinEulerProduct_eq_finiteCorrection_mul_deleted
    (χ : Gal(E/F) →* ℂˣ) (S : Finset Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    abelianArtinEulerProduct F E χ s =
      abelianArtinFiniteCorrection F E χ S s * abelianArtinDeletedEulerProduct F E χ S s := by
  have hS : Multipliable (fun p : (S : Set Nat.Primes) => abelianArtinRationalFactor F E χ p.val s) :=
    (hasProd_fintype (fun p : (S : Set Nat.Primes) => abelianArtinRationalFactor F E χ p.val s)).multipliable
  have hSc := (abelianArtinDeletedEulerProduct_hasProd F E χ S hs).multipliable
  have h := Multipliable.tprod_mul_tprod_compl
    (f := fun p : Nat.Primes => abelianArtinRationalFactor F E χ p s)
    (s := (S : Set Nat.Primes)) hS hSc
  have hfinite : (∏' p : (S : Set Nat.Primes), abelianArtinRationalFactor F E χ p.val s) =
      abelianArtinFiniteCorrection F E χ S s :=
    Finset.tprod_subtype' S (fun p => abelianArtinRationalFactor F E χ p s)
  change _ = abelianArtinEulerProduct F E χ s at h
  rw [hfinite] at h
  exact h.symm

end ArtinMatthews.AbelianLocal

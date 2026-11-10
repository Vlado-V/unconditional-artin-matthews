module

public import ArtinMatthews.ArtinAbelianEulerFiniteCorrection
public import ArtinMatthews.ArtinFrobeniusIdealCharacter
public import ArtinMatthews.ArtinFrobeniusConductorSupport
public import ArtinMatthews.VaryingKummerAnalyticRayEuler
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact comparison with the actual ray Dirichlet series. The hypothesis
identifies its ideal character with the genuine Frobenius ideal character;
the principal ray law is carried by the EvenRayCharacter itself. -/
set_option maxHeartbeats 800000
noncomputable section
namespace ArtinMatthews.AbelianLocal
open OAI.PrimeDegreePackets ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField IsMulCommutative Classical BigOperators

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [IsAbelianGalois F E]

def abelianArtinBadPrimes (N : ℕ) : Finset Nat.Primes := N.primeFactors.subtype Nat.Prime

theorem mem_abelianArtinBadPrimes {N : ℕ} (hN : N ≠ 0) (p : Nat.Primes) :
    p ∈ abelianArtinBadPrimes N ↔ p.val ∣ N := by
  change (⟨p.val, p.property⟩ : Subtype Nat.Prime) ∈
    N.primeFactors.subtype Nat.Prime ↔ p.val ∣ N
  rw [Finset.mem_subtype, Nat.mem_primeFactors]
  exact ⟨fun h => h.2.1, fun h => ⟨p.property, h, hN⟩⟩

private theorem inertia_le_ker_of_unramified (χ : Gal(E/F) →* ℂˣ)
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    [Algebra.IsUnramifiedAt (𝓞 F) (abelianPrimeAbove F E P).val] :
    (abelianPrimeAbove F E P).val.inertia Gal(E/F) ≤ χ.ker := by
  have hc : Nat.card ((abelianPrimeAbove F E P).val.inertia Gal(E/F)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(E/F)) P.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx P.asIdeal (abelianPrimeAbove F E P).val Gal(E/F)]
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  let : Subsingleton ((abelianPrimeAbove F E P).val.inertia Gal(E/F)) :=
    (Nat.card_eq_one_iff_unique.mp hc).1
  intro g hg
  have he : g = 1 := congrArg Subtype.val (Subsingleton.elim
    (⟨g, hg⟩ : (abelianPrimeAbove F E P).val.inertia Gal(E/F)) 1)
  exact he ▸ χ.ker.one_mem

private theorem ray_local_bad {N : ℕ} (ψ : EvenRayCharacter F N)
    (p : Nat.Primes) (hpN : p.val ∣ N) {s : ℂ} (hs : 1 < s.re) :
    (∏ P : idealsOverPrime F p.val, (1 - ψ.idealTerm hs P.val)⁻¹) = 1 := by
  apply Finset.prod_eq_one
  intro P _
  have hP := (mem_idealsOverPrime_iff F p.property.ne_zero P.val).mp P.property
  apply ψ.local_factor_eq_one_of_not_coprime hs P.val
  intro hc
  have hNm : (N : 𝓞 F) ∈ P.val := by
    obtain ⟨k, rfl⟩ := hpN
    rw [Nat.cast_mul]
    exact P.val.mul_mem_right _ hP.2
  have hle : rationalModulusIdeal (𝓞 F) N ≤ P.val :=
    (Ideal.span_singleton_le_iff_mem _).mpr hNm
  apply hP.1.ne_top'
  apply eq_top_iff.mpr
  rw [← hc.codisjoint.eq_top]
  exact sup_le le_rfl hle

private theorem ray_local_good (χ : Gal(E/F) →* ℂˣ) {N : ℕ}
    (ψ : EvenRayCharacter F N)
    (hψ : ψ.idealHom = GaloisIdealCharacter.idealHom F E χ)
    (hD : (NumberField.discr E).natAbs ∣ N)
    (p : Nat.Primes) (hpN : ¬ p.val ∣ N) {s : ℂ} (hs : 1 < s.re) :
    (∏ P : idealsOverPrime F p.val, (1 - ψ.idealTerm hs P.val)⁻¹) =
      abelianArtinRationalFactor F E χ p s := by
  have hpC : p.val.Coprime N := p.property.coprime_iff_not_dvd.mpr hpN
  have hpD : p.val.Coprime (NumberField.discr E).natAbs := hpC.of_dvd_right hD
  unfold abelianArtinRationalFactor
  apply Finset.prod_congr rfl
  intro P _
  let PP := primeOverHeightOne F p P
  have hP := (mem_idealsOverPrime_iff F p.property.ne_zero P.val).mp P.property
  have hc : IsCoprime P.val (rationalModulusIdeal (𝓞 F) N) := by
    apply Ideal.isCoprime_iff_codisjoint.mpr
    apply Codisjoint.mono ((Ideal.span_singleton_le_iff_mem _).mpr hP.2) le_rfl
    exact ((Ideal.isCoprime_span_singleton_iff _ _).mpr hpC.cast).codisjoint
  let : P.val.IsPrime := hP.1
  let : Algebra.IsUnramifiedAt (𝓞 F) (abelianPrimeAbove F E PP).val :=
    unramified_of_absDiscr_not_mem F E PP.asIdeal (abelianPrimeAbove F E PP).val
      (abelianPrimeAbove F E PP).property.2.over.symm
      (Ideal.IsPrime.notMem_of_isCoprime_of_mem hpD.cast hP.2)
  have hI := inertia_le_ker_of_unramified F E χ PP
  have hval := GaloisIdealCharacter.idealHom_prime_frobenius_of_inertia_le_ker F E χ PP
    (abelianPrimeAbove F E PP).val (abelianPrimeAbove F E PP).property.2.over.symm hI
    (abelianPrimeFrobenius F E PP) (abelianPrimeFrobenius_spec F E PP)
  have he : ψ.idealTerm hs P.val =
      (χ (abelianPrimeFrobenius F E PP) : ℂ) * (Ideal.absNorm P.val : ℂ) ^ (-s) := by
    have hP0 : P.val ≠ ⊥ := PP.ne_bot
    have hval' : GaloisIdealCharacter.idealHom F E χ
        (integralIdealFractionalUnit P.val hP0) = χ (abelianPrimeFrobenius F E PP) := hval
    rw [EvenRayCharacter.idealTerm_apply, EvenRayCharacter.allCoefficient,
      dite_eq_left hP0, ite_eq_left hc, hψ, hval']
  change (1 - ψ.idealTerm hs P.val)⁻¹ = abelianArtinLocalFactor F E χ PP s
  rw [he, abelianArtinLocalFactor, ite_eq_left hI]
  rfl

/-- Full Artin Euler product = genuine ray series times the exact omitted
finite factors, for a ray character whose ideal map is the actual Artin map. -/
theorem abelianArtinEulerProduct_eq_finiteCorrection_mul_rayDirichlet
    (χ : Gal(E/F) →* ℂˣ) {N : ℕ} (hN : N ≠ 0)
    (ψ : EvenRayCharacter F N)
    (hψ : ψ.idealHom = GaloisIdealCharacter.idealHom F E χ)
    (hD : (NumberField.discr E).natAbs ∣ N) {s : ℂ} (hs : 1 < s.re) :
    abelianArtinEulerProduct F E χ s =
      abelianArtinFiniteCorrection F E χ (abelianArtinBadPrimes N) s * ψ.dirichlet s := by
  let C (p : Nat.Primes) :=
    if p ∈ abelianArtinBadPrimes N then abelianArtinRationalFactor F E χ p s else 1
  have hC : HasProd C (abelianArtinFiniteCorrection F E χ (abelianArtinBadPrimes N) s) := by
    have h : HasProd C (∏ p ∈ abelianArtinBadPrimes N, C p) :=
      hasProd_prod_of_ne_finset_one (s := abelianArtinBadPrimes N)
        (f := C) (fun p hp => ite_eq_right hp)
    simpa only [C, abelianArtinFiniteCorrection, Finset.prod_ite_mem, Finset.inter_self] using h
  apply (abelianArtinEulerProduct_hasProd F E χ hs).unique
  apply (hC.mul (ψ.dirichlet_hasProd hs)).congr_fun
  intro p
  by_cases hp : p.val ∣ N
  · simp only [C, ite_eq_left ((mem_abelianArtinBadPrimes hN p).mpr hp),
      ray_local_bad F ψ p hp hs, mul_one]
  · simp only [C, ite_eq_right (mt (mem_abelianArtinBadPrimes hN p).mp hp),
      ray_local_good F E χ ψ hψ hD p hp hs, one_mul]

/-- The actual ray Dirichlet series equals the Artin Euler product with exactly
the rational primes dividing its modulus deleted. -/
theorem abelianArtinDeletedEulerProduct_eq_rayDirichlet
    (χ : Gal(E/F) →* ℂˣ) {N : ℕ} (hN : N ≠ 0)
    (ψ : EvenRayCharacter F N)
    (hψ : ψ.idealHom = GaloisIdealCharacter.idealHom F E χ)
    (hD : (NumberField.discr E).natAbs ∣ N) {s : ℂ} (hs : 1 < s.re) :
    abelianArtinDeletedEulerProduct F E χ (abelianArtinBadPrimes N) s = ψ.dirichlet s := by
  apply mul_left_cancel₀ (abelianArtinFiniteCorrection_ne_zero F E χ
    (abelianArtinBadPrimes N) (by linarith : 0 < s.re))
  exact (abelianArtinEulerProduct_eq_finiteCorrection_mul_deleted F E χ
    (abelianArtinBadPrimes N) hs).symm.trans
      (abelianArtinEulerProduct_eq_finiteCorrection_mul_rayDirichlet F E χ hN ψ hψ hD hs)

end ArtinMatthews.AbelianLocal

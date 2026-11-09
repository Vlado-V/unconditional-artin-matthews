module

public import ArtinMatthews.ArtinAbelianRayEulerComparison
public import ArtinMatthews.VaryingKummerAnalyticRayContinuation
public import ArtinMatthews.VaryingKummerAnalyticMixedZetaContinuation


set_option backward.privateInPublic true
@[expose] public section

/-! Analytic continuation of the nonprincipal abelian Artin factors obtained
from genuine ray characters, with every finite-prime correction retained. -/
set_option maxHeartbeats 800000
noncomputable section
namespace ArtinMatthews.AbelianLocal
open OAI.PrimeDegreePackets ArtinMatthews.VaryingKummerAnalytic
open Set Filter
open scoped NumberField IsMulCommutative Classical BigOperators Topology

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [IsAbelianGalois F E]
variable {N : ℕ} [NeZero N]

local instance continuedArtinCharactersFintype : Fintype (Gal(E/F) →* ℂˣ) := Fintype.ofFinite _

/-- The continued nonprincipal Artin factor, restoring all modulus-prime
factors of its actual ray Hecke continuation. -/
def abelianArtinContinuedFactor (χ : Gal(E/F) →* ℂˣ) (ψ : EvenRayCharacter F N) (s : ℂ) : ℂ :=
  abelianArtinFiniteCorrection F E χ (abelianArtinBadPrimes N) s * ψ.nonprincipalContinued s

theorem abelianArtinContinuedFactor_differentiableOn
    (χ : Gal(E/F) →* ℂˣ) (ψ : EvenRayCharacter F N) :
    DifferentiableOn ℂ (abelianArtinContinuedFactor F E χ ψ) {s : ℂ | 0 < s.re} :=
  (abelianArtinFiniteCorrection_differentiableOn F E χ _).mul
    ψ.nonprincipalContinued_entire.differentiableOn

theorem abelianArtinContinuedFactor_eq_eulerProduct
    (χ : Gal(E/F) →* ℂˣ) (ψ : EvenRayCharacter F N)
    (hψ : ψ.idealHom = GaloisIdealCharacter.idealHom F E χ)
    (hD : (NumberField.discr E).natAbs ∣ N) (hnp : ψ.IsNonprincipal)
    {s : ℂ} (hs : 1 < s.re) :
    abelianArtinContinuedFactor F E χ ψ s = abelianArtinEulerProduct F E χ s := by
  rw [abelianArtinContinuedFactor, ψ.nonprincipalContinued_eq_dirichlet hnp hs]
  exact (abelianArtinEulerProduct_eq_finiteCorrection_mul_rayDirichlet F E χ
    (NeZero.ne N) ψ hψ hD hs).symm

/-- Product of the continued factors indexed by the actual nontrivial global
Galois characters. The trivial character is represented separately by ζ_F. -/
def abelianArtinRelativeContinued (ψ : (Gal(E/F) →* ℂˣ) → EvenRayCharacter F N) (s : ℂ) : ℂ :=
  ∏ χ ∈ (Finset.univ : Finset (Gal(E/F) →* ℂˣ)).erase 1,
    abelianArtinContinuedFactor F E χ (ψ χ) s

theorem abelianArtinRelativeContinued_differentiableOn
    (ψ : (Gal(E/F) →* ℂˣ) → EvenRayCharacter F N) :
    DifferentiableOn ℂ (abelianArtinRelativeContinued F E ψ) {s : ℂ | 0 < s.re} := by
  exact DifferentiableOn.fun_finsetProd (fun χ _ =>
    abelianArtinContinuedFactor_differentiableOn F E χ (ψ χ))

theorem dedekindZeta_eq_mul_abelianArtinRelativeContinued
    (ψ : (Gal(E/F) →* ℂˣ) → EvenRayCharacter F N)
    (hψ : ∀ χ, (ψ χ).idealHom = GaloisIdealCharacter.idealHom F E χ)
    (hD : (NumberField.discr E).natAbs ∣ N)
    (hnp : ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal)
    {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta E s =
      NumberField.dedekindZeta F s * abelianArtinRelativeContinued F E ψ s := by
  rw [dedekindZeta_eq_prod_abelianArtinEulerProduct F E hs]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (1 : Gal(E/F) →* ℂˣ))]
  rw [abelianArtinEulerProduct_one F E hs]
  congr 1
  apply Finset.prod_congr rfl
  intro χ hχ
  exact (abelianArtinContinuedFactor_eq_eulerProduct F E χ (ψ χ)
    (hψ χ) hD (hnp χ (Finset.mem_erase.mp hχ).1) hs).symm

/-- Identity theorem applied to actual pole-removed zeta functions; in
particular, the pole at one is retained rather than absorbed into an L-factor. -/
theorem regularizedDedekindZeta_eq_mul_abelianArtinRelativeContinued
    (ψ : (Gal(E/F) →* ℂˣ) → EvenRayCharacter F N)
    (hψ : ∀ χ, (ψ χ).idealHom = GaloisIdealCharacter.idealHom F E χ)
    (hD : (NumberField.discr E).natAbs ∣ N)
    (hnp : ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal)
    {s : ℂ} (hs : 0 < s.re) :
    mixedRegularizedDedekindZeta E s =
      mixedRegularizedDedekindZeta F s * abelianArtinRelativeContinued F E ψ s := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hE : AnalyticOnNhd ℂ (mixedRegularizedDedekindZeta E) {z : ℂ | 0 < z.re} := by
    intro z hz
    exact mixedRegularizedDedekindZeta_analyticAt E (by intro he; simp [he] at hz)
  have hF : AnalyticOnNhd ℂ
      (fun z => mixedRegularizedDedekindZeta F z * abelianArtinRelativeContinued F E ψ z)
      {z : ℂ | 0 < z.re} := by
    intro z hz
    exact (mixedRegularizedDedekindZeta_analyticAt F (by intro he; simp [he] at hz)).mul
      ((abelianArtinRelativeContinued_differentiableOn F E ψ).analyticOnNhd hU z hz)
  have hconn : IsPreconnected {z : ℂ | 0 < z.re} := by
    exact ((convex_Ioi (0 : ℝ)).linear_preimage Complex.reCLM.toLinearMap).isPreconnected
  have heq : mixedRegularizedDedekindZeta E =ᶠ[𝓝 (2 : ℂ)]
      (fun z => mixedRegularizedDedekindZeta F z * abelianArtinRelativeContinued F E ψ z) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (2 : ℂ) ∈ {z : ℂ | 1 < z.re} by norm_num)] with z hz
    rw [mixedRegularizedDedekindZeta_eq E hz, mixedRegularizedDedekindZeta_eq F hz,
      dedekindZeta_eq_mul_abelianArtinRelativeContinued F E ψ hψ hD hnp hz]
    ring
  exact hE.eqOn_of_preconnected_of_eventuallyEq hF hconn (by norm_num) heq hs

theorem continuedDedekindZeta_eq_mul_abelianArtinRelativeContinued
    (ψ : (Gal(E/F) →* ℂˣ) → EvenRayCharacter F N)
    (hψ : ∀ χ, (ψ χ).idealHom = GaloisIdealCharacter.idealHom F E χ)
    (hD : (NumberField.discr E).natAbs ∣ N)
    (hnp : ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal)
    {s : ℂ} (hs : 0 < s.re) :
    mixedDedekindZetaContinuation E s =
      mixedDedekindZetaContinuation F s * abelianArtinRelativeContinued F E ψ s := by
  unfold mixedDedekindZetaContinuation
  rw [regularizedDedekindZeta_eq_mul_abelianArtinRelativeContinued F E ψ hψ hD hnp hs]
  ring

end ArtinMatthews.AbelianLocal

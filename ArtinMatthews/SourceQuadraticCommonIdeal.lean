module

public import ArtinMatthews.SourceReflectionFrozenWeights
public import ArtinMatthews.SourcePrimeIdealFactorization
public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusBound


set_option backward.privateInPublic true
@[expose] public section

/-! Common divisors of the actual exterior ideals. For squarefree columns,
stripping the common ideal removes exactly the common prime labels. -/

namespace ArtinMatthews.SourceEulerAssembly
noncomputable section
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization
open UniqueFactorizationMonoid VaryingKummerAnalytic
open scoped NumberField Classical BigOperators

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

local notation "E" => SourcePrimeExponents F S₀
local notation "Prime" => SourceExteriorPrime F S₀
local notation "I" => sourcePrimeExponentIdeal F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

theorem sourceQuadraticExteriorIdeal_dvd_iff (a b : E) : I a ∣ I b ↔ a ≤ b := by
  constructor
  · intro h
    have hfac := (dvd_iff_normalizedFactors_le_normalizedFactors
      (sourcePrimeExponentIdeal_ne_bot F S₀ a)
      (sourcePrimeExponentIdeal_ne_bot F S₀ b)).mp h
    have hle : factorization (I a) ≤ factorization (I b) := by
      intro P
      exact Multiset.le_iff_count.mp hfac P
    rw [sourcePrimeExponentIdeal_factorization, sourcePrimeExponentIdeal_factorization] at hle
    exact (Finsupp.embDomain_le_embDomain_iff_le _ _ _).mp hle
  · intro h
    exact ⟨I (b - a), by rw [← sourcePrimeExponentIdeal_add, add_tsub_cancel_of_le h]⟩

theorem sourceQuadraticExteriorIdeal_inf (a b : E) : I (a ⊓ b) = I a ⊔ I b := by
  let D := I a ⊔ I b
  have hDA : D ∣ I a := Ideal.dvd_iff_le.mpr le_sup_left
  have hDB : D ∣ I b := Ideal.dvd_iff_le.mpr le_sup_right
  have hD0 : D ≠ ⊥ := by
    intro h
    exact sourcePrimeExponentIdeal_ne_bot F S₀ a (le_bot_iff.mp (h ▸ le_sup_left))
  have ha := (exteriorIdeals_mem_iff (sourceHilbertSeed F S₀) (I a)).mp
    (sourcePrimeExponentIdeal_exterior F S₀ a)
  have hD : D ∈ exteriorIdeals (principalizingDenominator (sourceHilbertSeed F S₀)) :=
    (exteriorIdeals_mem_iff (sourceHilbertSeed F S₀) D).mpr
      ⟨hD0, fun P hP hp => ha.2 P hP (dvd_trans hp hDA)⟩
  let d := sourceExteriorIdealExponents F S₀ ⟨D, hD⟩
  have hd : I d = D := sourceExteriorIdealExponents_recover F S₀ ⟨D, hD⟩
  apply le_antisymm
  · change I (a ⊓ b) ≤ D
    rw [← hd]
    apply Ideal.dvd_iff_le.mp
    apply (sourceQuadraticExteriorIdeal_dvd_iff F S₀ d (a ⊓ b)).mpr
    exact le_inf ((sourceQuadraticExteriorIdeal_dvd_iff F S₀ d a).mp (hd.symm ▸ hDA))
      ((sourceQuadraticExteriorIdeal_dvd_iff F S₀ d b).mp (hd.symm ▸ hDB))
  · exact sup_le
      (Ideal.dvd_iff_le.mp ((sourceQuadraticExteriorIdeal_dvd_iff F S₀ (a ⊓ b) a).mpr inf_le_left))
      (Ideal.dvd_iff_le.mp ((sourceQuadraticExteriorIdeal_dvd_iff F S₀ (a ⊓ b) b).mpr inf_le_right))

theorem sourceQuadraticExteriorInf_support (a b : E) :
    (a ⊓ b).support = a.support ∩ b.support := by
  ext P
  simp only [Finset.mem_inter, Finsupp.mem_support_iff, Finsupp.inf_apply]
  change min (a P) (b P) ≠ 0 ↔ a P ≠ 0 ∧ b P ≠ 0
  omega

theorem sourceQuadraticExteriorQuotient_squarefree (a g : E)
    (ha : sourceReflectionIsSquarefree a) : sourceReflectionIsSquarefree (a - g) := by
  intro P
  exact (Nat.sub_le _ _).trans (ha P)

theorem sourceQuadraticExteriorQuotient_support (a g : E)
    (ha : sourceReflectionIsSquarefree a) : (a - g).support = a.support \ g.support := by
  ext P
  simp only [Finset.mem_sdiff, Finsupp.mem_support_iff, Finsupp.tsub_apply]
  have := ha P
  omega

theorem sourceQuadraticExteriorQuotient_norm (a g : E) (hg : g ≤ a) :
    q g * q (a - g) = q a := by
  rw [← sourcePrimeExponentNorm_add, add_tsub_cancel_of_le hg]

theorem sourceQuadraticExteriorInf_sub_disjoint (a b : E) :
    Disjoint (a - (a ⊓ b)).support (b - (a ⊓ b)).support := by
  rw [Finset.disjoint_left]
  intro P hP hQ
  simp only [Finsupp.mem_support_iff, Finsupp.tsub_apply, Finsupp.inf_apply] at hP hQ
  change a P - min (a P) (b P) ≠ 0 at hP
  change b P - min (a P) (b P) ≠ 0 at hQ
  omega

theorem sourceQuadraticSquarefree_eq_active (a : E) (ha : sourceReflectionIsSquarefree a) :
    sourceReflectionActiveExponents F S₀ a.support = a := by
  ext P
  simp only [sourceReflectionActiveExponents, Finsupp.onFinset_apply, Finsupp.mem_support_iff]
  have := ha P
  split <;> omega

def sourceQuadraticSquarefreeDivisors (a : E) : Finset E :=
  a.support.powerset.map ⟨sourceReflectionActiveExponents F S₀,
    fun _ _ h => by
      have he := congrArg (fun e : E => e.support) h
      simpa only [sourceReflectionActiveExponents_support] using he⟩

theorem sourceQuadratic_mem_squarefreeDivisors (a g : E) :
    g ∈ sourceQuadraticSquarefreeDivisors F S₀ a ↔ g ≤ a ∧ sourceReflectionIsSquarefree g := by
  rw [sourceQuadraticSquarefreeDivisors, Finset.mem_map]
  constructor
  · rintro ⟨S, hS, rfl⟩
    have hsub := Finset.mem_powerset.mp hS
    refine ⟨fun P => ?_, sourceReflectionActiveExponents_squarefree F S₀ S⟩
    change (if P ∈ S then 1 else 0) ≤ a P
    split_ifs with hp
    · exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (hsub hp))
    · exact Nat.zero_le _
  · rintro ⟨hga, hg⟩
    exact ⟨g.support, Finset.mem_powerset.mpr (Finsupp.support_mono hga),
      sourceQuadraticSquarefree_eq_active F S₀ g hg⟩

theorem sourceQuadraticSquarefreeDivisors_card (a : E) :
    (sourceQuadraticSquarefreeDivisors F S₀ a).card = 2 ^ a.support.card := by
  rw [sourceQuadraticSquarefreeDivisors, Finset.card_map, Finset.card_powerset]

theorem sourceQuadraticSquarefreeDivisors_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : E, ((sourceQuadraticSquarefreeDivisors F S₀ a).card : ℝ) ≤
      C * (q a : ℝ)^ε := by
  obtain ⟨C, hC, hbound⟩ := HeckeIdealMobius.squarefree_divisor_small_power F ε hε
  refine ⟨C, hC, fun a => ?_⟩
  let A := sourceQuadraticSquarefreeDivisors F S₀ a
  let B := (HeckeIdealMobius.divisors F (I a)).filter Squarefree
  have hA : A.image I ⊆ B := by
    intro J hJ
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hJ
    obtain ⟨hga, hsf⟩ := (sourceQuadratic_mem_squarefreeDivisors F S₀ a g).mp hg
    exact Finset.mem_filter.mpr ⟨
      (HeckeIdealMobius.mem_divisors F (sourcePrimeExponentIdeal_ne_bot F S₀ a)).mpr
        ((sourceQuadraticExteriorIdeal_dvd_iff F S₀ g a).mpr hga),
      (sourceReflectionExteriorIdeal_squarefree F S₀ g).mpr hsf⟩
  have hcard : (A.card : ℝ) ≤ B.card := by
    exact_mod_cast (Finset.card_image_of_injective A (sourcePrimeExponentIdeal_injective F S₀)).symm.trans_le
      (Finset.card_le_card hA)
  have hb := hbound (I a) (sourcePrimeExponentIdeal_ne_bot F S₀ a)
  rw [sourcePrimeExponentIdeal_norm] at hb
  exact hcard.trans hb

end
end ArtinMatthews.SourceEulerAssembly

module

public import ArtinMatthews.ProbeBadPrimeHolomorphy
public import ArtinMatthews.ProbeBadPrimeNormalConvergence


set_option backward.privateInPublic true
@[expose] public section

/-! Finite bad-prime factors and the good/bad analytic product. The
subpower constant is uniform in the local phases, cutoff superset and
ideal parameter. These are the literal local factors; the global
arithmetic identification with H_u remains a separate step. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField Set
open scoped NumberField Classical BigOperators Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def probeBadPrimeFiniteProduct (T : Finset (Ideal (𝓞 K)))
    (D : ∀ P : T, ProbeBadPrimeData K P.val) (q : ArtinMatthews.ProbeCoordinates) : ℂ :=
  ∏ P : T, (D P).correction q.1 q.2.1 q.2.2

theorem probeBadPrimeFiniteProduct_differentiableOn (T : Finset (Ideal (𝓞 K)))
    (D : ∀ P : T, ProbeBadPrimeData K P.val) :
    DifferentiableOn ℂ (probeBadPrimeFiniteProduct K T D)
      (interior ArtinMatthews.probeEulerDomain) := by
  intro q hq
  have hprod (s : Finset T) : DifferentiableWithinAt ℂ
      (fun q : ArtinMatthews.ProbeCoordinates =>
        ∏ P ∈ s, (D P).correction q.1 q.2.1 q.2.2)
      (interior ArtinMatthews.probeEulerDomain) q := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty]
      exact differentiableWithinAt_const (1 : ℂ)
    | @insert P s hP ih =>
      simp only [Finset.prod_insert hP]
      exact ((D P).correction_differentiableOn q hq).mul ih
  exact hprod Finset.univ

theorem probeBadPrimeFiniteProduct_differentiableOn_open (T : Finset (Ideal (𝓞 K)))
    (D : ∀ P : T, ProbeBadPrimeData K P.val) :
    DifferentiableOn ℂ (probeBadPrimeFiniteProduct K T D)
      ArtinMatthews.probeEulerOpenDomain :=
  (probeBadPrimeFiniteProduct_differentiableOn K T D).mono
    ArtinMatthews.probeEulerOpenDomain_subset_interior

theorem probeEulerLogMajorant_le_all (S : Finset (ArtinMatthews.ProbePrime K)) :
    ArtinMatthews.probeEulerLogMajorant K S ≤
      ∑' P : ArtinMatthews.ProbePrime K, 240 * ArtinMatthews.probePrimeWeight K P := by
  apply Summable.tsum_le_tsum_of_inj
    (fun P : ArtinMatthews.ProbeGoodPrime K S => P.val) Subtype.val_injective
  · intro P _
    exact mul_nonneg (by norm_num) (ArtinMatthews.probePrimeWeight_nonneg K P)
  · intro P
    exact le_rfl
  · exact ArtinMatthews.probeGoodPrime_majorant_summable K S
  · exact (ArtinMatthews.probePrimeWeight_summable K).mul_left 240

def probeGoodProductUniformBound : ℝ :=
  Real.exp (∑' P : ArtinMatthews.ProbePrime K, 240 * ArtinMatthews.probePrimeWeight K P)

theorem probeGoodProductUniformBound_pos : 0 < probeGoodProductUniformBound K :=
  Real.exp_pos _

theorem probeEulerProduct_norm_le_uniform (S : Finset (ArtinMatthews.ProbePrime K))
    (hS : ArtinMatthews.probePrimeCutoff K ⊆ S) (a b c : ArtinMatthews.ProbePrime K → ℂ)
    (ha : ∀ P, ‖a P‖ ≤ 1) (hb : ∀ P, ‖b P‖ ≤ 1) (hc : ∀ P, ‖c P‖ ≤ 1)
    {q : ArtinMatthews.ProbeCoordinates} (hq : q ∈ ArtinMatthews.probeEulerDomain) :
    ‖ArtinMatthews.probeEulerProduct K S a b c q‖ ≤ probeGoodProductUniformBound K := by
  rw [ArtinMatthews.probeEulerProduct_eq_exp K S hS a b c ha hb hc hq]
  exact (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr
    ((ArtinMatthews.probeEulerLog_norm_le K S hS a b c ha hb hc hq).trans
      (probeEulerLogMajorant_le_all K S)))

def probeGoodBadCorrectionProduct (S : Finset (ArtinMatthews.ProbePrime K))
    (a b c : ArtinMatthews.ProbePrime K → ℂ) (T : Finset (Ideal (𝓞 K)))
    (D : ∀ P : T, ProbeBadPrimeData K P.val) (q : ArtinMatthews.ProbeCoordinates) : ℂ :=
  ArtinMatthews.probeEulerProduct K S a b c q * probeBadPrimeFiniteProduct K T D q

theorem probeGoodBadCorrectionProduct_differentiableOn (S : Finset (ArtinMatthews.ProbePrime K))
    (hS : ArtinMatthews.probePrimeCutoff K ⊆ S) (a b c : ArtinMatthews.ProbePrime K → ℂ)
    (ha : ∀ P, ‖a P‖ ≤ 1) (hb : ∀ P, ‖b P‖ ≤ 1) (hc : ∀ P, ‖c P‖ ≤ 1)
    (T : Finset (Ideal (𝓞 K))) (D : ∀ P : T, ProbeBadPrimeData K P.val) :
    DifferentiableOn ℂ (probeGoodBadCorrectionProduct K S a b c T D)
      (interior ArtinMatthews.probeEulerDomain) :=
  (ArtinMatthews.probeEulerProduct_differentiableOn K S hS a b c ha hb hc).mul
    (probeBadPrimeFiniteProduct_differentiableOn K T D)

theorem probeGoodBadCorrectionProduct_differentiableOn_open
    (S : Finset (ArtinMatthews.ProbePrime K)) (hS : ArtinMatthews.probePrimeCutoff K ⊆ S)
    (a b c : ArtinMatthews.ProbePrime K → ℂ)
    (ha : ∀ P, ‖a P‖ ≤ 1) (hb : ∀ P, ‖b P‖ ≤ 1) (hc : ∀ P, ‖c P‖ ≤ 1)
    (T : Finset (Ideal (𝓞 K))) (D : ∀ P : T, ProbeBadPrimeData K P.val) :
    DifferentiableOn ℂ (probeGoodBadCorrectionProduct K S a b c T D)
      ArtinMatthews.probeEulerOpenDomain :=
  (probeGoodBadCorrectionProduct_differentiableOn K S hS a b c ha hb hc T D).mono
    ArtinMatthews.probeEulerOpenDomain_subset_interior

theorem exists_probeGoodBadCorrectionProduct_fixed_support_bound
    (R : Ideal (𝓞 K)) (hR : R ≠ ⊥) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (ArtinMatthews.ProbePrime K)),
      ArtinMatthews.probePrimeCutoff K ⊆ S →
      ∀ (a b c : ArtinMatthews.ProbePrime K → ℂ),
      (∀ P, ‖a P‖ ≤ 1) → (∀ P, ‖b P‖ ≤ 1) → (∀ P, ‖c P‖ ≤ 1) →
      ∀ (U : Ideal (𝓞 K)), U ≠ ⊥ →
      ∀ (T : Finset (Ideal (𝓞 K))), T ⊆ HeckeIdealMobius.primeSupport K (U * R) →
      ∀ (D : ∀ P : T, ProbeBadPrimeData K P.val) (q : ArtinMatthews.ProbeCoordinates),
      q ∈ ArtinMatthews.probeEulerDomain →
      ‖probeGoodBadCorrectionProduct K S a b c T D q‖ ≤ C * (Ideal.absNorm U : ℝ) ^ ε := by
  obtain ⟨B, hB, hbound⟩ := exists_actual_badPrime_product_fixed_support_bound K R hR ε hε
  refine ⟨probeGoodProductUniformBound K * B,
    mul_pos (probeGoodProductUniformBound_pos K) hB, ?_⟩
  intro S hS a b c ha hb hc U hU T hT D q hq
  rw [probeGoodBadCorrectionProduct, norm_mul]
  have hbad : ‖probeBadPrimeFiniteProduct K T D q‖ ≤ B * (Ideal.absNorm U : ℝ) ^ ε :=
    hbound U hU T hT D q.1 q.2.1 q.2.2 hq
  calc
    _ ≤ probeGoodProductUniformBound K * (B * (Ideal.absNorm U : ℝ) ^ ε) :=
      mul_le_mul (probeEulerProduct_norm_le_uniform K S hS a b c ha hb hc hq) hbad
        (norm_nonneg _) (probeGoodProductUniformBound_pos K).le
    _ = _ := by ring

end
end ArtinMatthews.VaryingKummerAnalytic
